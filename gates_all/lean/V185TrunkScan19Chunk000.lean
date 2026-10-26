import V185TrunkScan18Incremental

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_4 : List Nat := [2, 3, 2, 4, 2, 1, 5]
def baseStart_4 : Nat := 118140960795 + 4 * 2 ^ 59
def prefixEnd_4 : Nat := 4983230072969 + 3 ^ 40 * 4 * 2
def baseEnd_4 : Nat := 405713130512207405

theorem tailTrace_4 : CollatzResearch.WordTrace tailWord_4 prefixEnd_4 405713130512207405 := by
  unfold tailWord_4
  simp only [CollatzResearch.WordTrace]
  refine ⟨72945996491764127533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97261328655685503377 72945996491764127533)
  ·
    refine ⟨27354748684411547825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72945996491764127533 27354748684411547825)
    ·
      refine ⟨20516061513308660869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27354748684411547825 20516061513308660869)
      ·
        refine ⟨3846761533745373913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20516061513308660869 3846761533745373913)
        ·
          refine ⟨2885071150309030435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3846761533745373913 2885071150309030435)
          ·
            refine ⟨4327606725463545653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885071150309030435 4327606725463545653)
            ·
              refine ⟨405713130512207405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4327606725463545653 405713130512207405)
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
  · exact (by decide : CollatzResearch.ExactOddStep 4 1118505227216467522661 209719730103087660499)
  ·
    refine ⟨314579595154631490749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209719730103087660499 314579595154631490749)
    ·
      refine ⟨117967348182986809031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314579595154631490749 117967348182986809031)
      ·
        refine ⟨176951022274480213547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117967348182986809031 176951022274480213547)
        ·
          refine ⟨265426533411720320321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176951022274480213547 265426533411720320321)
          ·
            refine ⟨199069900058790240241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265426533411720320321 199069900058790240241)
            ·
              refine ⟨149302425044092680181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199069900058790240241 149302425044092680181)
              ·
                refine ⟨13997102347883688767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149302425044092680181 13997102347883688767)
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
  · exact (by decide : CollatzResearch.ExactOddStep 2 1167135889052695237865 875351916789521428399)
  ·
    refine ⟨1313027875184282142599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 875351916789521428399 1313027875184282142599)
    ·
      refine ⟨1969541812776423213899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1313027875184282142599 1969541812776423213899)
      ·
        refine ⟨2954312719164634820849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1969541812776423213899 2954312719164634820849)
        ·
          refine ⟨2215734539373476115637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2954312719164634820849 2215734539373476115637)
          ·
            refine ⟨207725113066263385841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2215734539373476115637 207725113066263385841)
            ·
              refine ⟨155793834799697539381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207725113066263385841 155793834799697539381)
              ·
                refine ⟨14605672012471644317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155793834799697539381 14605672012471644317)
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
  · exact (by decide : CollatzResearch.ExactOddStep 3 1993857140268566396333 747696427600712398625)
  ·
    refine ⟨560772320700534298969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 747696427600712398625 560772320700534298969)
    ·
      refine ⟨420579240525400724227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 560772320700534298969 420579240525400724227)
      ·
        refine ⟨630868860788101086341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420579240525400724227 630868860788101086341)
        ·
          refine ⟨118287911397768953689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 630868860788101086341 118287911397768953689)
          ·
            refine ⟨88715933548326715267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118287911397768953689 88715933548326715267)
            ·
              refine ⟨133073900322490072901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88715933548326715267 133073900322490072901)
              ·
                refine ⟨24951356310466888669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133073900322490072901 24951356310466888669)
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
  · exact (by decide : CollatzResearch.ExactOddStep 1 2504479089548957405975 3756718634323436108963)
  ·
    refine ⟨5635077951485154163445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3756718634323436108963 5635077951485154163445)
    ·
      refine ⟨528288557951733202823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5635077951485154163445 528288557951733202823)
      ·
        refine ⟨792432836927599804235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528288557951733202823 792432836927599804235)
        ·
          refine ⟨1188649255391399706353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792432836927599804235 1188649255391399706353)
          ·
            refine ⟨891486941543549779765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1188649255391399706353 891486941543549779765)
            ·
              refine ⟨83576900769707791853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 891486941543549779765 83576900769707791853)
              ·
                refine ⟨31341337788640421945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83576900769707791853 31341337788640421945)
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
  · exact (by decide : CollatzResearch.ExactOddStep 2 3015101038829348415617 2261325779122011311713)
  ·
    refine ⟨1695994334341508483785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2261325779122011311713 1695994334341508483785)
    ·
      refine ⟨1271995750756131362839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1695994334341508483785 1271995750756131362839)
      ·
        refine ⟨1907993626134197044259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1271995750756131362839 1907993626134197044259)
        ·
          refine ⟨2861990439201295566389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907993626134197044259 2861990439201295566389)
          ·
            refine ⟨268311603675121459349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2861990439201295566389 268311603675121459349)
            ·
              refine ⟨12577106422271318407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 268311603675121459349 12577106422271318407)
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
  · exact (by decide : CollatzResearch.ExactOddStep 5 3647299642700308713269 341934341503153941869)
  ·
    refine ⟨128225378063682728201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 341934341503153941869 128225378063682728201)
    ·
      refine ⟨96169033547762046151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128225378063682728201 96169033547762046151)
      ·
        refine ⟨144253550321643069227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96169033547762046151 144253550321643069227)
        ·
          refine ⟨216380325482464603841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144253550321643069227 216380325482464603841)
          ·
            refine ⟨162285244111848452881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216380325482464603841 162285244111848452881)
            ·
              refine ⟨121713933083886339661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162285244111848452881 121713933083886339661)
              ·
                refine ⟨45642724906457377373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121713933083886339661 45642724906457377373)
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
  · exact (by decide : CollatzResearch.ExactOddStep 4 3841822290045219574085 720341679383478670141)
  ·
    refine ⟨270128129768804501303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 720341679383478670141 270128129768804501303)
    ·
      refine ⟨405192194653206751955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270128129768804501303 405192194653206751955)
      ·
        refine ⟨607788291979810127933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405192194653206751955 607788291979810127933)
        ·
          refine ⟨227920609492428797975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 607788291979810127933 227920609492428797975)
          ·
            refine ⟨341880914238643196963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227920609492428797975 341880914238643196963)
            ·
              refine ⟨512821371357964795445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341880914238643196963 512821371357964795445)
              ·
                refine ⟨48077003564809199573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 512821371357964795445 48077003564809199573)
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
  · exact (by decide : CollatzResearch.ExactOddStep 2 3890452951881447289289 2917839713911085466967)
  ·
    refine ⟨4376759570866628200451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2917839713911085466967 4376759570866628200451)
    ·
      refine ⟨6565139356299942300677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4376759570866628200451 6565139356299942300677)
      ·
        refine ⟨1230963629306239181377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6565139356299942300677 1230963629306239181377)
        ·
          refine ⟨923222721979679386033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1230963629306239181377 923222721979679386033)
          ·
            refine ⟨692417041484759539525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 923222721979679386033 692417041484759539525)
            ·
              refine ⟨129828195278392413661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 692417041484759539525 129828195278392413661)
              ·
                refine ⟨48685573229397155123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129828195278392413661 48685573229397155123)
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
  · exact (by decide : CollatzResearch.ExactOddStep 1 4303813577489382868523 6455720366234074302785)
  ·
    refine ⟨4841790274675555727089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6455720366234074302785 4841790274675555727089)
    ·
      refine ⟨3631342706006666795317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4841790274675555727089 3631342706006666795317)
      ·
        refine ⟨340438378688125012061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3631342706006666795317 340438378688125012061)
        ·
          refine ⟨127664392008046879523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340438378688125012061 127664392008046879523)
          ·
            refine ⟨191496588012070319285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127664392008046879523 191496588012070319285)
            ·
              refine ⟨17952805126131592433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191496588012070319285 17952805126131592433)
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
  · exact (by decide : CollatzResearch.ExactOddStep 3 4717174203097318447757 1768940326161494417909)
  ·
    refine ⟨165838155577640101679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1768940326161494417909 165838155577640101679)
    ·
      refine ⟨248757233366460152519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165838155577640101679 248757233366460152519)
      ·
        refine ⟨373135850049690228779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248757233366460152519 373135850049690228779)
        ·
          refine ⟨559703775074535343169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373135850049690228779 559703775074535343169)
          ·
            refine ⟨419777831305901507377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559703775074535343169 419777831305901507377)
            ·
              refine ⟨314833373479426130533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419777831305901507377 314833373479426130533)
              ·
                refine ⟨59031257527392399475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 314833373479426130533 59031257527392399475)
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
  · exact (by decide : CollatzResearch.ExactOddStep 2 8461735164486852518465 6346301373365139388849)
  ·
    refine ⟨4759726030023854541637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6346301373365139388849 4759726030023854541637)
    ·
      refine ⟨892448630629472726557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4759726030023854541637 892448630629472726557)
      ·
        refine ⟨334668236486052272459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 892448630629472726557 334668236486052272459)
        ·
          refine ⟨502002354729078408689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334668236486052272459 502002354729078408689)
          ·
            refine ⟨376501766046808806517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 502002354729078408689 376501766046808806517)
            ·
              refine ⟨35297040566888325611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 376501766046808806517 35297040566888325611)
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
  · exact (by decide : CollatzResearch.ExactOddStep 2 10309700314263505696217 7732275235697629272163)
  ·
    refine ⟨11598412853546443908245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7732275235697629272163 11598412853546443908245)
    ·
      refine ⟨543675602509989558199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11598412853546443908245 543675602509989558199)
      ·
        refine ⟨815513403764984337299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543675602509989558199 815513403764984337299)
        ·
          refine ⟨1223270105647476505949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815513403764984337299 1223270105647476505949)
          ·
            refine ⟨458726289617803689731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1223270105647476505949 458726289617803689731)
            ·
              refine ⟨688089434426705534597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458726289617803689731 688089434426705534597)
              ·
                refine ⟨129016768955007287737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 688089434426705534597 129016768955007287737)
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
  · exact (by decide : CollatzResearch.ExactOddStep 1 10820322263543896705859 16230483395315845058789)
  ·
    refine ⟨3043215636621720948523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16230483395315845058789 3043215636621720948523)
    ·
      refine ⟨4564823454932581422785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3043215636621720948523 4564823454932581422785)
      ·
        refine ⟨3423617591199436067089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4564823454932581422785 3423617591199436067089)
        ·
          refine ⟨2567713193399577050317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3423617591199436067089 2567713193399577050317)
          ·
            refine ⟨962892447524841393869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2567713193399577050317 962892447524841393869)
            ·
              refine ⟨361084667821815522701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 962892447524841393869 361084667821815522701)
              ·
                refine ⟨135406750433180821013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361084667821815522701 135406750433180821013)
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
  · exact (by decide : CollatzResearch.ExactOddStep 3 12109034802203931158765 4540888050826474184537)
  ·
    refine ⟨3405666038119855638403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4540888050826474184537 3405666038119855638403)
    ·
      refine ⟨5108499057179783457605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3405666038119855638403 5108499057179783457605)
      ·
        refine ⟨957843573221209398301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5108499057179783457605 957843573221209398301)
        ·
          refine ⟨359191339957953524363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 957843573221209398301 359191339957953524363)
          ·
            refine ⟨538787009936930286545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359191339957953524363 538787009936930286545)
            ·
              refine ⟨404090257452697714909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538787009936930286545 404090257452697714909)
              ·
                refine ⟨151533846544761643091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404090257452697714909 151533846544761643091)
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
  · exact (by decide : CollatzResearch.ExactOddStep 1 12716918075156777598815 19075377112735166398223)
  ·
    refine ⟨28613065669102749597335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19075377112735166398223 28613065669102749597335)
    ·
      refine ⟨42919598503654124396003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28613065669102749597335 42919598503654124396003)
      ·
        refine ⟨64379397755481186594005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42919598503654124396003 64379397755481186594005)
        ·
          refine ⟨1508892134894090310797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 64379397755481186594005 1508892134894090310797)
          ·
            refine ⟨565834550585283866549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1508892134894090310797 565834550585283866549)
            ·
              refine ⟨53046989117370362489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 565834550585283866549 53046989117370362489)
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

def tailWord_563 : List Nat := [1, 1, 1, 2, 4, 2, 1, 7]
def baseStart_563 : Nat := 118140960795 + 563 * 2 ^ 59
def prefixEnd_563 : Nat := 4983230072969 + 3 ^ 40 * 563 * 2
def baseEnd_563 : Nat := 171312360643870198469

theorem tailTrace_563 : CollatzResearch.WordTrace tailWord_563 prefixEnd_563 171312360643870198469 := by
  unfold tailWord_563
  simp only [CollatzResearch.WordTrace]
  refine ⟨20534296967821997854343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13689531311881331902895 20534296967821997854343)
  ·
    refine ⟨30801445451732996781515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20534296967821997854343 30801445451732996781515)
    ·
      refine ⟨46202168177599495172273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30801445451732996781515 46202168177599495172273)
      ·
        refine ⟨34651626133199621379205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46202168177599495172273 34651626133199621379205)
        ·
          refine ⟨6497179899974929008601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34651626133199621379205 6497179899974929008601)
          ·
            refine ⟨4872884924981196756451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6497179899974929008601 4872884924981196756451)
            ·
              refine ⟨7309327387471795134677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4872884924981196756451 7309327387471795134677)
              ·
                refine ⟨171312360643870198469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7309327387471795134677 171312360643870198469)
                ·
                  rfl

theorem cell19_563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_563 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_563 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_563 prefixEnd_563 := by exact prefixLift 563
  have htrace : WordTrace (prefixWord ++ tailWord_563) baseStart_563 baseEnd_563 := by
    simpa [prefixWord, tailWord_563, baseEnd_563] using wordTrace_append hprefix tailTrace_563
  have hstable : (prefixWord ++ tailWord_563).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563).length < 2 ^ (prefixWord ++ tailWord_563).sum := by decide
  have hdescent : baseEnd_563 < baseStart_563 := by decide
  rcases family_descends (prefixWord ++ tailWord_563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620 : List Nat := [2, 2, 1, 1, 3, 1, 2, 7]
def baseStart_620 : Nat := 118140960795 + 620 * 2 ^ 59
def prefixEnd_620 : Nat := 4983230072969 + 3 ^ 40 * 620 * 2
def baseEnd_620 : Nat := 188656596084626931647

theorem tailTrace_620 : CollatzResearch.WordTrace tailWord_620 prefixEnd_620 188656596084626931647 := by
  unfold tailWord_620
  simp only [CollatzResearch.WordTrace]
  refine ⟨11306628880660366339657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15075505174213821786209 11306628880660366339657)
  ·
    refine ⟨8479971660495274754743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11306628880660366339657 8479971660495274754743)
    ·
      refine ⟨12719957490742912132115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8479971660495274754743 12719957490742912132115)
      ·
        refine ⟨19079936236114368198173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12719957490742912132115 19079936236114368198173)
        ·
          refine ⟨7154976088542888074315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19079936236114368198173 7154976088542888074315)
          ·
            refine ⟨10732464132814332111473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7154976088542888074315 10732464132814332111473)
            ·
              refine ⟨8049348099610749083605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10732464132814332111473 8049348099610749083605)
              ·
                refine ⟨188656596084626931647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8049348099610749083605 188656596084626931647)
                ·
                  rfl

theorem cell19_620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_620 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_620 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_620 prefixEnd_620 := by exact prefixLift 620
  have htrace : WordTrace (prefixWord ++ tailWord_620) baseStart_620 baseEnd_620 := by
    simpa [prefixWord, tailWord_620, baseEnd_620] using wordTrace_append hprefix tailTrace_620
  have hstable : (prefixWord ++ tailWord_620).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620).length < 2 ^ (prefixWord ++ tailWord_620).sum := by decide
  have hdescent : baseEnd_620 < baseStart_620 := by decide
  rcases family_descends (prefixWord ++ tailWord_620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637 : List Nat := [1, 4, 1, 1, 5, 1, 6]
def baseStart_637 : Nat := 118140960795 + 637 * 2 ^ 59
def prefixEnd_637 : Nat := 4983230072969 + 3 ^ 40 * 637 * 2
def baseEnd_637 : Nat := 64609812744541517941

theorem tailTrace_637 : CollatzResearch.WordTrace tailWord_637 prefixEnd_637 64609812744541517941 := by
  unfold tailWord_637
  simp only [CollatzResearch.WordTrace]
  refine ⟨23233298699732636048165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15488865799821757365443 23233298699732636048165)
  ·
    refine ⟨4356243506199869259031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23233298699732636048165 4356243506199869259031)
    ·
      refine ⟨6534365259299803888547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4356243506199869259031 6534365259299803888547)
      ·
        refine ⟨9801547888949705832821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6534365259299803888547 9801547888949705832821)
        ·
          refine ⟨918895114589034921827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9801547888949705832821 918895114589034921827)
          ·
            refine ⟨1378342671883552382741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918895114589034921827 1378342671883552382741)
            ·
              refine ⟨64609812744541517941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1378342671883552382741 64609812744541517941)
              ·
                rfl

theorem cell19_637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 6].length) (baseStart_637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_637 prefixEnd_637 := by exact prefixLift 637
  have htrace : WordTrace (prefixWord ++ tailWord_637) baseStart_637 baseEnd_637 := by
    simpa [prefixWord, tailWord_637, baseEnd_637] using wordTrace_append hprefix tailTrace_637
  have hstable : (prefixWord ++ tailWord_637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637).length < 2 ^ (prefixWord ++ tailWord_637).sum := by decide
  have hdescent : baseEnd_637 < baseStart_637 := by decide
  rcases family_descends (prefixWord ++ tailWord_637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789 : List Nat := [1, 3, 2, 1, 2, 2, 5, 3]
def baseStart_789 : Nat := 118140960795 + 789 * 2 ^ 59
def prefixEnd_789 : Nat := 4983230072969 + 3 ^ 40 * 789 * 2
def baseEnd_789 : Nat := 240080732742309175631

theorem tailTrace_789 : CollatzResearch.WordTrace tailWord_789 prefixEnd_789 240080732742309175631 := by
  unfold tailWord_789
  simp only [CollatzResearch.WordTrace]
  refine ⟨28777194149062595581421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19184796099375063720947 28777194149062595581421)
  ·
    refine ⟨10791447805898473343033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28777194149062595581421 10791447805898473343033)
    ·
      refine ⟨8093585854423855007275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10791447805898473343033 8093585854423855007275)
      ·
        refine ⟨12140378781635782510913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8093585854423855007275 12140378781635782510913)
        ·
          refine ⟨9105284086226836883185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12140378781635782510913 9105284086226836883185)
          ·
            refine ⟨6828963064670127662389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9105284086226836883185 6828963064670127662389)
            ·
              refine ⟨640215287312824468349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6828963064670127662389 640215287312824468349)
              ·
                refine ⟨240080732742309175631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 640215287312824468349 240080732742309175631)
                ·
                  rfl

theorem cell19_789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 3].length) (baseStart_789 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_789 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_789 prefixEnd_789 := by exact prefixLift 789
  have htrace : WordTrace (prefixWord ++ tailWord_789) baseStart_789 baseEnd_789 := by
    simpa [prefixWord, tailWord_789, baseEnd_789] using wordTrace_append hprefix tailTrace_789
  have hstable : (prefixWord ++ tailWord_789).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789).length < 2 ^ (prefixWord ++ tailWord_789).sum := by decide
  have hdescent : baseEnd_789 < baseStart_789 := by decide
  rcases family_descends (prefixWord ++ tailWord_789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838 : List Nat := [6, 1, 1, 2, 3, 1, 2, 3]
def baseStart_838 : Nat := 118140960795 + 838 * 2 ^ 59
def prefixEnd_838 : Nat := 4983230072969 + 3 ^ 40 * 838 * 2
def baseEnd_838 : Nat := 254990689524714086609

theorem tailTrace_838 : CollatzResearch.WordTrace tailWord_838 prefixEnd_838 254990689524714086609 := by
  unfold tailWord_838
  simp only [CollatzResearch.WordTrace]
  refine ⟨955136592860748878599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20376247314362642743445 955136592860748878599)
  ·
    refine ⟨1432704889291123317899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 955136592860748878599 1432704889291123317899)
    ·
      refine ⟨2149057333936684976849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1432704889291123317899 2149057333936684976849)
      ·
        refine ⟨1611793000452513732637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2149057333936684976849 1611793000452513732637)
        ·
          refine ⟨604422375169692649739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1611793000452513732637 604422375169692649739)
          ·
            refine ⟨906633562754538974609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604422375169692649739 906633562754538974609)
            ·
              refine ⟨679975172065904230957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906633562754538974609 679975172065904230957)
              ·
                refine ⟨254990689524714086609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 679975172065904230957 254990689524714086609)
                ·
                  rfl

theorem cell19_838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_838 prefixEnd_838 := by exact prefixLift 838
  have htrace : WordTrace (prefixWord ++ tailWord_838) baseStart_838 baseEnd_838 := by
    simpa [prefixWord, tailWord_838, baseEnd_838] using wordTrace_append hprefix tailTrace_838
  have hstable : (prefixWord ++ tailWord_838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838).length < 2 ^ (prefixWord ++ tailWord_838).sum := by decide
  have hdescent : baseEnd_838 < baseStart_838 := by decide
  rcases family_descends (prefixWord ++ tailWord_838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844 : List Nat := [2, 2, 1, 3, 3, 3, 2, 3]
def baseStart_844 : Nat := 118140960795 + 844 * 2 ^ 59
def prefixEnd_844 : Nat := 4983230072969 + 3 ^ 40 * 844 * 2
def baseEnd_844 : Nat := 256816398518477953259

theorem tailTrace_844 : CollatzResearch.WordTrace tailWord_844 prefixEnd_844 256816398518477953259 := by
  unfold tailWord_844
  simp only [CollatzResearch.WordTrace]
  refine ⟨15391604474903494416793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20522139299871325889057 15391604474903494416793)
  ·
    refine ⟨11543703356177620812595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15391604474903494416793 11543703356177620812595)
    ·
      refine ⟨17315555034266431218893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11543703356177620812595 17315555034266431218893)
      ·
        refine ⟨6493333137849911707085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17315555034266431218893 6493333137849911707085)
        ·
          refine ⟨2434999926693716890157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6493333137849911707085 2434999926693716890157)
          ·
            refine ⟨913124972510143833809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2434999926693716890157 913124972510143833809)
            ·
              refine ⟨684843729382607875357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 913124972510143833809 684843729382607875357)
              ·
                refine ⟨256816398518477953259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 684843729382607875357 256816398518477953259)
                ·
                  rfl

theorem cell19_844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_844 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_844 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_844 prefixEnd_844 := by exact prefixLift 844
  have htrace : WordTrace (prefixWord ++ tailWord_844) baseStart_844 baseEnd_844 := by
    simpa [prefixWord, tailWord_844, baseEnd_844] using wordTrace_append hprefix tailTrace_844
  have hstable : (prefixWord ++ tailWord_844).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844).length < 2 ^ (prefixWord ++ tailWord_844).sum := by decide
  have hdescent : baseEnd_844 < baseStart_844 := by decide
  rcases family_descends (prefixWord ++ tailWord_844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867 : List Nat := [1, 1, 1, 5, 3, 1, 7]
def baseStart_867 : Nat := 118140960795 + 867 * 2 ^ 59
def prefixEnd_867 : Nat := 4983230072969 + 3 ^ 40 * 867 * 2
def baseEnd_867 : Nat := 87938316553746480695

theorem tailTrace_867 : CollatzResearch.WordTrace tailWord_867 prefixEnd_867 87938316553746480695 := by
  unfold tailWord_867
  simp only [CollatzResearch.WordTrace]
  refine ⟨31622087866481916920855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21081391910987944613903 31622087866481916920855)
  ·
    refine ⟨47433131799722875381283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31622087866481916920855 47433131799722875381283)
    ·
      refine ⟨71149697699584313071925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47433131799722875381283 71149697699584313071925)
      ·
        refine ⟨6670284159336029350493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71149697699584313071925 6670284159336029350493)
        ·
          refine ⟨2501356559751011006435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6670284159336029350493 2501356559751011006435)
          ·
            refine ⟨3752034839626516509653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2501356559751011006435 3752034839626516509653)
            ·
              refine ⟨87938316553746480695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3752034839626516509653 87938316553746480695)
              ·
                rfl

theorem cell19_867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 7].length) (baseStart_867 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_867 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_867 prefixEnd_867 := by exact prefixLift 867
  have htrace : WordTrace (prefixWord ++ tailWord_867) baseStart_867 baseEnd_867 := by
    simpa [prefixWord, tailWord_867, baseEnd_867] using wordTrace_append hprefix tailTrace_867
  have hstable : (prefixWord ++ tailWord_867).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867).length < 2 ^ (prefixWord ++ tailWord_867).sum := by decide
  have hdescent : baseEnd_867 < baseStart_867 := by decide
  rcases family_descends (prefixWord ++ tailWord_867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905 : List Nat := [1, 2, 1, 1, 5, 2, 2, 5]
def baseStart_905 : Nat := 118140960795 + 905 * 2 ^ 59
def prefixEnd_905 : Nat := 4983230072969 + 3 ^ 40 * 905 * 2
def baseEnd_905 : Nat := 275377773288410597537

theorem tailTrace_905 : CollatzResearch.WordTrace tailWord_905 prefixEnd_905 275377773288410597537 := by
  unfold tailWord_905
  simp only [CollatzResearch.WordTrace]
  refine ⟨33008061728814406804169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22005374485876271202779 33008061728814406804169)
  ·
    refine ⟨24756046296610805103127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33008061728814406804169 24756046296610805103127)
    ·
      refine ⟨37134069444916207654691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24756046296610805103127 37134069444916207654691)
      ·
        refine ⟨55701104167374311482037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37134069444916207654691 55701104167374311482037)
        ·
          refine ⟨5221978515691341701441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55701104167374311482037 5221978515691341701441)
          ·
            refine ⟨3916483886768506276081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5221978515691341701441 3916483886768506276081)
            ·
              refine ⟨2937362915076379707061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3916483886768506276081 2937362915076379707061)
              ·
                refine ⟨275377773288410597537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2937362915076379707061 275377773288410597537)
                ·
                  rfl

theorem cell19_905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_905 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_905 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_905 prefixEnd_905 := by exact prefixLift 905
  have htrace : WordTrace (prefixWord ++ tailWord_905) baseStart_905 baseEnd_905 := by
    simpa [prefixWord, tailWord_905, baseEnd_905] using wordTrace_append hprefix tailTrace_905
  have hstable : (prefixWord ++ tailWord_905).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905).length < 2 ^ (prefixWord ++ tailWord_905).sum := by decide
  have hdescent : baseEnd_905 < baseStart_905 := by decide
  rcases family_descends (prefixWord ++ tailWord_905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922 : List Nat := [3, 1, 1, 4, 4, 6]
def baseStart_922 : Nat := 118140960795 + 922 * 2 ^ 59
def prefixEnd_922 : Nat := 4983230072969 + 3 ^ 40 * 922 * 2
def baseEnd_922 : Nat := 31172290604156468857

theorem tailTrace_922 : CollatzResearch.WordTrace tailWord_922 prefixEnd_922 31172290604156468857 := by
  unfold tailWord_922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8407025666806577543255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22418735111484206782013 8407025666806577543255)
  ·
    refine ⟨12610538500209866314883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8407025666806577543255 12610538500209866314883)
    ·
      refine ⟨18915807750314799472325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12610538500209866314883 18915807750314799472325)
      ·
        refine ⟨3546713953184024901061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18915807750314799472325 3546713953184024901061)
        ·
          refine ⟨665008866222004668949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3546713953184024901061 665008866222004668949)
          ·
            refine ⟨31172290604156468857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 665008866222004668949 31172290604156468857)
            ·
              rfl

theorem cell19_922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 6].length) (baseStart_922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_922 prefixEnd_922 := by exact prefixLift 922
  have htrace : WordTrace (prefixWord ++ tailWord_922) baseStart_922 baseEnd_922 := by
    simpa [prefixWord, tailWord_922, baseEnd_922] using wordTrace_append hprefix tailTrace_922
  have hstable : (prefixWord ++ tailWord_922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922).length < 2 ^ (prefixWord ++ tailWord_922).sum := by decide
  have hdescent : baseEnd_922 < baseStart_922 := by decide
  rcases family_descends (prefixWord ++ tailWord_922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924 : List Nat := [2, 2, 3, 3, 9]
def baseStart_924 : Nat := 118140960795 + 924 * 2 ^ 59
def prefixEnd_924 : Nat := 4983230072969 + 3 ^ 40 * 924 * 2
def baseEnd_924 : Nat := 10413303151925784269

theorem tailTrace_924 : CollatzResearch.WordTrace tailWord_924 prefixEnd_924 10413303151925784269 := by
  unfold tailWord_924
  simp only [CollatzResearch.WordTrace]
  refine ⟨16850524329990325872913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22467365773320434497217 16850524329990325872913)
  ·
    refine ⟨12637893247492744404685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16850524329990325872913 12637893247492744404685)
    ·
      refine ⟨4739209967809779151757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12637893247492744404685 4739209967809779151757)
      ·
        refine ⟨1777203737928667181909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4739209967809779151757 1777203737928667181909)
        ·
          refine ⟨10413303151925784269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 1777203737928667181909 10413303151925784269)
          ·
            rfl

theorem cell19_924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 9].length) (baseStart_924 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_924 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_924 prefixEnd_924 := by exact prefixLift 924
  have htrace : WordTrace (prefixWord ++ tailWord_924) baseStart_924 baseEnd_924 := by
    simpa [prefixWord, tailWord_924, baseEnd_924] using wordTrace_append hprefix tailTrace_924
  have hstable : (prefixWord ++ tailWord_924).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924).length < 2 ^ (prefixWord ++ tailWord_924).sum := by decide
  have hdescent : baseEnd_924 < baseStart_924 := by decide
  rcases family_descends (prefixWord ++ tailWord_924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960 : List Nat := [2, 1, 1, 2, 3, 4, 3, 3]
def baseStart_960 : Nat := 118140960795 + 960 * 2 ^ 59
def prefixEnd_960 : Nat := 4983230072969 + 3 ^ 40 * 960 * 2
def baseEnd_960 : Nat := 292113439064579375165

theorem tailTrace_960 : CollatzResearch.WordTrace tailWord_960 prefixEnd_960 292113439064579375165 := by
  unfold tailWord_960
  simp only [CollatzResearch.WordTrace]
  refine ⟨17507038264779400028167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23342717686372533370889 17507038264779400028167)
  ·
    refine ⟨26260557397169100042251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17507038264779400028167 26260557397169100042251)
    ·
      refine ⟨39390836095753650063377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26260557397169100042251 39390836095753650063377)
      ·
        refine ⟨29543127071815237547533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39390836095753650063377 29543127071815237547533)
        ·
          refine ⟨11078672651930714080325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29543127071815237547533 11078672651930714080325)
          ·
            refine ⟨2077251122237008890061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11078672651930714080325 2077251122237008890061)
            ·
              refine ⟨778969170838878333773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2077251122237008890061 778969170838878333773)
              ·
                refine ⟨292113439064579375165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 778969170838878333773 292113439064579375165)
                ·
                  rfl

theorem cell19_960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_960 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_960 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_960 prefixEnd_960 := by exact prefixLift 960
  have htrace : WordTrace (prefixWord ++ tailWord_960) baseStart_960 baseEnd_960 := by
    simpa [prefixWord, tailWord_960, baseEnd_960] using wordTrace_append hprefix tailTrace_960
  have hstable : (prefixWord ++ tailWord_960).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960).length < 2 ^ (prefixWord ++ tailWord_960).sum := by decide
  have hdescent : baseEnd_960 < baseStart_960 := by decide
  rcases family_descends (prefixWord ++ tailWord_960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038 : List Nat := [4, 1, 1, 2, 2, 2, 7]
def baseStart_1038 : Nat := 118140960795 + 1038 * 2 ^ 59
def prefixEnd_1038 : Nat := 4983230072969 + 3 ^ 40 * 1038 * 2
def baseEnd_1038 : Nat := 105282551994503213873

theorem tailTrace_1038 : CollatzResearch.WordTrace tailWord_1038 prefixEnd_1038 105282551994503213873 := by
  unfold tailWord_1038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732371280872265174471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25239313497985414263845 4732371280872265174471)
  ·
    refine ⟨7098556921308397761707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4732371280872265174471 7098556921308397761707)
    ·
      refine ⟨10647835381962596642561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7098556921308397761707 10647835381962596642561)
      ·
        refine ⟨7985876536471947481921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10647835381962596642561 7985876536471947481921)
        ·
          refine ⟨5989407402353960611441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7985876536471947481921 5989407402353960611441)
          ·
            refine ⟨4492055551765470458581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5989407402353960611441 4492055551765470458581)
            ·
              refine ⟨105282551994503213873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4492055551765470458581 105282551994503213873)
              ·
                rfl

theorem cell19_1038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_1038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1038 prefixEnd_1038 := by exact prefixLift 1038
  have htrace : WordTrace (prefixWord ++ tailWord_1038) baseStart_1038 baseEnd_1038 := by
    simpa [prefixWord, tailWord_1038, baseEnd_1038] using wordTrace_append hprefix tailTrace_1038
  have hstable : (prefixWord ++ tailWord_1038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038).length < 2 ^ (prefixWord ++ tailWord_1038).sum := by decide
  have hdescent : baseEnd_1038 < baseStart_1038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1057 : List Nat := [1, 2, 3, 2, 3, 1, 1, 6]
def baseStart_1057 : Nat := 118140960795 + 1057 * 2 ^ 59
def prefixEnd_1057 : Nat := 4983230072969 + 3 ^ 40 * 1057 * 2
def baseEnd_1057 : Nat := 321629067797095219345

theorem tailTrace_1057 : CollatzResearch.WordTrace tailWord_1057 prefixEnd_1057 321629067797095219345 := by
  unfold tailWord_1057
  simp only [CollatzResearch.WordTrace]
  refine ⟨38551957178144366337425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25701304785429577558283 38551957178144366337425)
  ·
    refine ⟨28913967883608274753069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38551957178144366337425 28913967883608274753069)
    ·
      refine ⟨10842737956353103032401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28913967883608274753069 10842737956353103032401)
      ·
        refine ⟨8132053467264827274301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10842737956353103032401 8132053467264827274301)
        ·
          refine ⟨3049520050224310227863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8132053467264827274301 3049520050224310227863)
          ·
            refine ⟨4574280075336465341795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3049520050224310227863 4574280075336465341795)
            ·
              refine ⟨6861420113004698012693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4574280075336465341795 6861420113004698012693)
              ·
                refine ⟨321629067797095219345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6861420113004698012693 321629067797095219345)
                ·
                  rfl

theorem cell19_1057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_1057 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1057 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1057 prefixEnd_1057 := by exact prefixLift 1057
  have htrace : WordTrace (prefixWord ++ tailWord_1057) baseStart_1057 baseEnd_1057 := by
    simpa [prefixWord, tailWord_1057, baseEnd_1057] using wordTrace_append hprefix tailTrace_1057
  have hstable : (prefixWord ++ tailWord_1057).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1057).length < 2 ^ (prefixWord ++ tailWord_1057).sum := by decide
  have hdescent : baseEnd_1057 < baseStart_1057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188 : List Nat := [2, 3, 1, 2, 3, 1, 4, 3]
def baseStart_1188 : Nat := 118140960795 + 1188 * 2 ^ 59
def prefixEnd_1188 : Nat := 4983230072969 + 3 ^ 40 * 1188 * 2
def baseEnd_1188 : Nat := 361490380827606307877

theorem tailTrace_1188 : CollatzResearch.WordTrace tailWord_1188 prefixEnd_1188 361490380827606307877 := by
  unfold tailWord_1188
  simp only [CollatzResearch.WordTrace]
  refine ⟨21664959851776869678109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28886613135702492904145 21664959851776869678109)
  ·
    refine ⟨8124359944416326129291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21664959851776869678109 8124359944416326129291)
    ·
      refine ⟨12186539916624489193937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8124359944416326129291 12186539916624489193937)
      ·
        refine ⟨9139904937468366895453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12186539916624489193937 9139904937468366895453)
        ·
          refine ⟨3427464351550637585795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9139904937468366895453 3427464351550637585795)
          ·
            refine ⟨5141196527325956378693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3427464351550637585795 5141196527325956378693)
            ·
              refine ⟨963974348873616821005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5141196527325956378693 963974348873616821005)
              ·
                refine ⟨361490380827606307877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 963974348873616821005 361490380827606307877)
                ·
                  rfl

theorem cell19_1188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_1188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1188 prefixEnd_1188 := by exact prefixLift 1188
  have htrace : WordTrace (prefixWord ++ tailWord_1188) baseStart_1188 baseEnd_1188 := by
    simpa [prefixWord, tailWord_1188, baseEnd_1188] using wordTrace_append hprefix tailTrace_1188
  have hstable : (prefixWord ++ tailWord_1188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188).length < 2 ^ (prefixWord ++ tailWord_1188).sum := by decide
  have hdescent : baseEnd_1188 < baseStart_1188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209 : List Nat := [1, 2, 1, 4, 1, 5, 5]
def baseStart_1209 : Nat := 118140960795 + 1209 * 2 ^ 59
def prefixEnd_1209 : Nat := 4983230072969 + 3 ^ 40 * 1209 * 2
def baseEnd_1209 : Nat := 122626787435259947051

theorem tailTrace_1209 : CollatzResearch.WordTrace tailWord_1209 prefixEnd_1209 122626787435259947051 := by
  unfold tailWord_1209
  simp only [CollatzResearch.WordTrace]
  refine ⟨44095852627474325870681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29397235084982883913787 44095852627474325870681)
  ·
    refine ⟨33071889470605744403011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44095852627474325870681 33071889470605744403011)
    ·
      refine ⟨49607834205908616604517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33071889470605744403011 49607834205908616604517)
      ·
        refine ⟨9301468913607865613347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49607834205908616604517 9301468913607865613347)
        ·
          refine ⟨13952203370411798420021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9301468913607865613347 13952203370411798420021)
          ·
            refine ⟨1308019065976106101877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13952203370411798420021 1308019065976106101877)
            ·
              refine ⟨122626787435259947051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1308019065976106101877 122626787435259947051)
              ·
                rfl

theorem cell19_1209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 5].length) (baseStart_1209 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1209 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1209 prefixEnd_1209 := by exact prefixLift 1209
  have htrace : WordTrace (prefixWord ++ tailWord_1209) baseStart_1209 baseEnd_1209 := by
    simpa [prefixWord, tailWord_1209, baseEnd_1209] using wordTrace_append hprefix tailTrace_1209
  have hstable : (prefixWord ++ tailWord_1209).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209).length < 2 ^ (prefixWord ++ tailWord_1209).sum := by decide
  have hdescent : baseEnd_1209 < baseStart_1209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266 : List Nat := [3, 2, 1, 3, 3, 7]
def baseStart_1266 : Nat := 118140960795 + 1266 * 2 ^ 59
def prefixEnd_1266 : Nat := 4983230072969 + 3 ^ 40 * 1266 * 2
def baseEnd_1266 : Nat := 42802733082948508259

theorem tailTrace_1266 : CollatzResearch.WordTrace tailWord_1266 prefixEnd_1266 42802733082948508259 := by
  unfold tailWord_1266
  simp only [CollatzResearch.WordTrace]
  refine ⟨11543703355243265173913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30783208947315373797101 11543703355243265173913)
  ·
    refine ⟨8657777516432448880435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11543703355243265173913 8657777516432448880435)
    ·
      refine ⟨12986666274648673320653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8657777516432448880435 12986666274648673320653)
      ·
        refine ⟨4869999852993252495245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12986666274648673320653 4869999852993252495245)
        ·
          refine ⟨1826249944872469685717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4869999852993252495245 1826249944872469685717)
          ·
            refine ⟨42802733082948508259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1826249944872469685717 42802733082948508259)
            ·
              rfl

theorem cell19_1266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 7].length) (baseStart_1266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1266 prefixEnd_1266 := by exact prefixLift 1266
  have htrace : WordTrace (prefixWord ++ tailWord_1266) baseStart_1266 baseEnd_1266 := by
    simpa [prefixWord, tailWord_1266, baseEnd_1266] using wordTrace_append hprefix tailTrace_1266
  have hstable : (prefixWord ++ tailWord_1266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266).length < 2 ^ (prefixWord ++ tailWord_1266).sum := by decide
  have hdescent : baseEnd_1266 < baseStart_1266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298 : List Nat := [3, 2, 4, 2, 1, 1, 3, 3]
def baseStart_1298 : Nat := 118140960795 + 1298 * 2 ^ 59
def prefixEnd_1298 : Nat := 4983230072969 + 3 ^ 40 * 1298 * 2
def baseEnd_1298 : Nat := 394961712379943863133

theorem tailTrace_1298 : CollatzResearch.WordTrace tailWord_1298 prefixEnd_1298 394961712379943863133 := by
  unfold tailWord_1298
  simp only [CollatzResearch.WordTrace]
  refine ⟨11835487326260631465137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31561299536695017240365 11835487326260631465137)
  ·
    refine ⟨8876615494695473598853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11835487326260631465137 8876615494695473598853)
    ·
      refine ⟨1664365405255401299785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8876615494695473598853 1664365405255401299785)
      ·
        refine ⟨1248274053941550974839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1664365405255401299785 1248274053941550974839)
        ·
          refine ⟨1872411080912326462259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248274053941550974839 1872411080912326462259)
          ·
            refine ⟨2808616621368489693389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1872411080912326462259 2808616621368489693389)
            ·
              refine ⟨1053231233013183635021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2808616621368489693389 1053231233013183635021)
              ·
                refine ⟨394961712379943863133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1053231233013183635021 394961712379943863133)
                ·
                  rfl

theorem cell19_1298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_1298 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1298 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1298 prefixEnd_1298 := by exact prefixLift 1298
  have htrace : WordTrace (prefixWord ++ tailWord_1298) baseStart_1298 baseEnd_1298 := by
    simpa [prefixWord, tailWord_1298, baseEnd_1298] using wordTrace_append hprefix tailTrace_1298
  have hstable : (prefixWord ++ tailWord_1298).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298).length < 2 ^ (prefixWord ++ tailWord_1298).sum := by decide
  have hdescent : baseEnd_1298 < baseStart_1298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342 : List Nat := [4, 2, 1, 2, 1, 1, 2, 6]
def baseStart_1342 : Nat := 118140960795 + 1342 * 2 ^ 59
def prefixEnd_1342 : Nat := 4983230072969 + 3 ^ 40 * 1342 * 2
def baseEnd_1342 : Nat := 408350245000878885235

theorem tailTrace_1342 : CollatzResearch.WordTrace tailWord_1342 prefixEnd_1342 408350245000878885235 := by
  unfold tailWord_1342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6118345143204755057785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32631174097092026974853 6118345143204755057785)
  ·
    refine ⟨4588758857403566293339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6118345143204755057785 4588758857403566293339)
    ·
      refine ⟨6883138286105349440009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4588758857403566293339 6883138286105349440009)
      ·
        refine ⟨5162353714579012080007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6883138286105349440009 5162353714579012080007)
        ·
          refine ⟨7743530571868518120011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5162353714579012080007 7743530571868518120011)
          ·
            refine ⟨11615295857802777180017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7743530571868518120011 11615295857802777180017)
            ·
              refine ⟨8711471893352082885013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11615295857802777180017 8711471893352082885013)
              ·
                refine ⟨408350245000878885235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8711471893352082885013 408350245000878885235)
                ·
                  rfl

theorem cell19_1342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_1342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1342 prefixEnd_1342 := by exact prefixLift 1342
  have htrace : WordTrace (prefixWord ++ tailWord_1342) baseStart_1342 baseEnd_1342 := by
    simpa [prefixWord, tailWord_1342, baseEnd_1342] using wordTrace_append hprefix tailTrace_1342
  have hstable : (prefixWord ++ tailWord_1342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342).length < 2 ^ (prefixWord ++ tailWord_1342).sum := by decide
  have hdescent : baseEnd_1342 < baseStart_1342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344 : List Nat := [2, 1, 1, 2, 2, 1, 4, 6]
def baseStart_1344 : Nat := 118140960795 + 1344 * 2 ^ 59
def prefixEnd_1344 : Nat := 4983230072969 + 3 ^ 40 * 1344 * 2
def baseEnd_1344 : Nat := 408958814665466840785

theorem tailTrace_1344 : CollatzResearch.WordTrace tailWord_1344 prefixEnd_1344 408958814665466840785 := by
  unfold tailWord_1344
  simp only [CollatzResearch.WordTrace]
  refine ⟨24509853569196191017543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32679804758928254690057 24509853569196191017543)
  ·
    refine ⟨36764780353794286526315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24509853569196191017543 36764780353794286526315)
    ·
      refine ⟨55147170530691429789473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36764780353794286526315 55147170530691429789473)
      ·
        refine ⟨41360377898018572342105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55147170530691429789473 41360377898018572342105)
        ·
          refine ⟨31020283423513929256579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41360377898018572342105 31020283423513929256579)
          ·
            refine ⟨46530425135270893884869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31020283423513929256579 46530425135270893884869)
            ·
              refine ⟨8724454712863292603413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46530425135270893884869 8724454712863292603413)
              ·
                refine ⟨408958814665466840785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8724454712863292603413 408958814665466840785)
                ·
                  rfl

theorem cell19_1344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_1344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1344 prefixEnd_1344 := by exact prefixLift 1344
  have htrace : WordTrace (prefixWord ++ tailWord_1344) baseStart_1344 baseEnd_1344 := by
    simpa [prefixWord, tailWord_1344, baseEnd_1344] using wordTrace_append hprefix tailTrace_1344
  have hstable : (prefixWord ++ tailWord_1344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344).length < 2 ^ (prefixWord ++ tailWord_1344).sum := by decide
  have hdescent : baseEnd_1344 < baseStart_1344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357 : List Nat := [1, 6, 1, 3, 1, 1, 1, 5]
def baseStart_1357 : Nat := 118140960795 + 1357 * 2 ^ 59
def prefixEnd_1357 : Nat := 4983230072969 + 3 ^ 40 * 1357 * 2
def baseEnd_1357 : Nat := 412914517485288551861

theorem tailTrace_1357 : CollatzResearch.WordTrace tailWord_1357 prefixEnd_1357 412914517485288551861 := by
  unfold tailWord_1357
  simp only [CollatzResearch.WordTrace]
  refine ⟨49493856091295602258325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32995904060863734838883 49493856091295602258325)
  ·
    refine ⟨2320024504279481355859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49493856091295602258325 2320024504279481355859)
    ·
      refine ⟨3480036756419222033789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2320024504279481355859 3480036756419222033789)
      ·
        refine ⟨1305013783657208262671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3480036756419222033789 1305013783657208262671)
        ·
          refine ⟨1957520675485812394007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1305013783657208262671 1957520675485812394007)
          ·
            refine ⟨2936281013228718591011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957520675485812394007 2936281013228718591011)
            ·
              refine ⟨4404421519843077886517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936281013228718591011 4404421519843077886517)
              ·
                refine ⟨412914517485288551861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4404421519843077886517 412914517485288551861)
                ·
                  rfl

theorem cell19_1357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 5].length) (baseStart_1357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1357 prefixEnd_1357 := by exact prefixLift 1357
  have htrace : WordTrace (prefixWord ++ tailWord_1357) baseStart_1357 baseEnd_1357 := by
    simpa [prefixWord, tailWord_1357, baseEnd_1357] using wordTrace_append hprefix tailTrace_1357
  have hstable : (prefixWord ++ tailWord_1357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357).length < 2 ^ (prefixWord ++ tailWord_1357).sum := by decide
  have hdescent : baseEnd_1357 < baseStart_1357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363 : List Nat := [1, 1, 1, 2, 1, 1, 7, 5]
def baseStart_1363 : Nat := 118140960795 + 1363 * 2 ^ 59
def prefixEnd_1363 : Nat := 4983230072969 + 3 ^ 40 * 1363 * 2
def baseEnd_1363 : Nat := 414740226479052418511

theorem tailTrace_1363 : CollatzResearch.WordTrace tailWord_1363 prefixEnd_1363 414740226479052418511 := by
  unfold tailWord_1363
  simp only [CollatzResearch.WordTrace]
  refine ⟨49712694069558626976743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33141796046372417984495 49712694069558626976743)
  ·
    refine ⟨74569041104337940465115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49712694069558626976743 74569041104337940465115)
    ·
      refine ⟨111853561656506910697673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74569041104337940465115 111853561656506910697673)
      ·
        refine ⟨83890171242380183023255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111853561656506910697673 83890171242380183023255)
        ·
          refine ⟨125835256863570274534883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83890171242380183023255 125835256863570274534883)
          ·
            refine ⟨188752885295355411802325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125835256863570274534883 188752885295355411802325)
            ·
              refine ⟨4423895749109892464117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 188752885295355411802325 4423895749109892464117)
              ·
                refine ⟨414740226479052418511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4423895749109892464117 414740226479052418511)
                ·
                  rfl

theorem cell19_1363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_1363 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1363 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1363 prefixEnd_1363 := by exact prefixLift 1363
  have htrace : WordTrace (prefixWord ++ tailWord_1363) baseStart_1363 baseEnd_1363 := by
    simpa [prefixWord, tailWord_1363, baseEnd_1363] using wordTrace_append hprefix tailTrace_1363
  have hstable : (prefixWord ++ tailWord_1363).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363).length < 2 ^ (prefixWord ++ tailWord_1363).sum := by decide
  have hdescent : baseEnd_1363 < baseStart_1363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1380 : List Nat := [2, 3, 1, 1, 3, 4, 5]
def baseStart_1380 : Nat := 118140960795 + 1380 * 2 ^ 59
def prefixEnd_1380 : Nat := 4983230072969 + 3 ^ 40 * 1380 * 2
def baseEnd_1380 : Nat := 139971022876016680229

theorem tailTrace_1380 : CollatzResearch.WordTrace tailWord_1380 prefixEnd_1380 139971022876016680229 := by
  unfold tailWord_1380
  simp only [CollatzResearch.WordTrace]
  refine ⟨25166367503985265172797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33555156671980353563729 25166367503985265172797)
  ·
    refine ⟨9437387813994474439799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25166367503985265172797 9437387813994474439799)
    ·
      refine ⟨14156081720991711659699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9437387813994474439799 14156081720991711659699)
      ·
        refine ⟨21234122581487567489549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14156081720991711659699 21234122581487567489549)
        ·
          refine ⟨7962795968057837808581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21234122581487567489549 7962795968057837808581)
          ·
            refine ⟨1493024244010844589109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7962795968057837808581 1493024244010844589109)
            ·
              refine ⟨139971022876016680229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1493024244010844589109 139971022876016680229)
              ·
                rfl

theorem cell19_1380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 5].length) (baseStart_1380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1380 prefixEnd_1380 := by exact prefixLift 1380
  have htrace : WordTrace (prefixWord ++ tailWord_1380) baseStart_1380 baseEnd_1380 := by
    simpa [prefixWord, tailWord_1380, baseEnd_1380] using wordTrace_append hprefix tailTrace_1380
  have hstable : (prefixWord ++ tailWord_1380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1380).length < 2 ^ (prefixWord ++ tailWord_1380).sum := by decide
  have hdescent : baseEnd_1380 < baseStart_1380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397 : List Nat := [1, 3, 4, 1, 3, 1, 2, 4]
def baseStart_1397 : Nat := 118140960795 + 1397 * 2 ^ 59
def prefixEnd_1397 : Nat := 4983230072969 + 3 ^ 40 * 1397 * 2
def baseEnd_1397 : Nat := 425085910777047662863

theorem tailTrace_1397 : CollatzResearch.WordTrace tailWord_1397 prefixEnd_1397 425085910777047662863 := by
  unfold tailWord_1397
  simp only [CollatzResearch.WordTrace]
  refine ⟨50952775946382433714445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33968517297588289142963 50952775946382433714445)
  ·
    refine ⟨19107290979893412642917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50952775946382433714445 19107290979893412642917)
    ·
      refine ⟨3582617058730014870547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19107290979893412642917 3582617058730014870547)
      ·
        refine ⟨5373925588095022305821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3582617058730014870547 5373925588095022305821)
        ·
          refine ⟨2015222095535633364683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5373925588095022305821 2015222095535633364683)
          ·
            refine ⟨3022833143303450047025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015222095535633364683 3022833143303450047025)
            ·
              refine ⟨2267124857477587535269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3022833143303450047025 2267124857477587535269)
              ·
                refine ⟨425085910777047662863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2267124857477587535269 425085910777047662863)
                ·
                  rfl

theorem cell19_1397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_1397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1397 prefixEnd_1397 := by exact prefixLift 1397
  have htrace : WordTrace (prefixWord ++ tailWord_1397) baseStart_1397 baseEnd_1397 := by
    simpa [prefixWord, tailWord_1397, baseEnd_1397] using wordTrace_append hprefix tailTrace_1397
  have hstable : (prefixWord ++ tailWord_1397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397).length < 2 ^ (prefixWord ++ tailWord_1397).sum := by decide
  have hdescent : baseEnd_1397 < baseStart_1397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401 : List Nat := [1, 2, 1, 3, 2, 1, 3, 6]
def baseStart_1401 : Nat := 118140960795 + 1401 * 2 ^ 59
def prefixEnd_1401 : Nat := 4983230072969 + 3 ^ 40 * 1401 * 2
def baseEnd_1401 : Nat := 426303050106223573963

theorem tailTrace_1401 : CollatzResearch.WordTrace tailWord_1401 prefixEnd_1401 426303050106223573963 := by
  unfold tailWord_1401
  simp only [CollatzResearch.WordTrace]
  refine ⟨51098667931891116860057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34065778621260744573371 51098667931891116860057)
  ·
    refine ⟨38324000948918337645043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51098667931891116860057 38324000948918337645043)
    ·
      refine ⟨57486001423377506467565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38324000948918337645043 57486001423377506467565)
      ·
        refine ⟨21557250533766564925337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57486001423377506467565 21557250533766564925337)
        ·
          refine ⟨16167937900324923694003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21557250533766564925337 16167937900324923694003)
          ·
            refine ⟨24251906850487385541005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16167937900324923694003 24251906850487385541005)
            ·
              refine ⟨9094465068932769577877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24251906850487385541005 9094465068932769577877)
              ·
                refine ⟨426303050106223573963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9094465068932769577877 426303050106223573963)
                ·
                  rfl

theorem cell19_1401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_1401 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1401 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1401 prefixEnd_1401 := by exact prefixLift 1401
  have htrace : WordTrace (prefixWord ++ tailWord_1401) baseStart_1401 baseEnd_1401 := by
    simpa [prefixWord, tailWord_1401, baseEnd_1401] using wordTrace_append hprefix tailTrace_1401
  have hstable : (prefixWord ++ tailWord_1401).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401).length < 2 ^ (prefixWord ++ tailWord_1401).sum := by decide
  have hdescent : baseEnd_1401 < baseStart_1401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1420 : List Nat := [2, 2, 1, 2, 1, 3, 1, 7]
def baseStart_1420 : Nat := 118140960795 + 1420 * 2 ^ 59
def prefixEnd_1420 : Nat := 4983230072969 + 3 ^ 40 * 1420 * 2
def baseEnd_1420 : Nat := 432084461919809151689

theorem tailTrace_1420 : CollatzResearch.WordTrace tailWord_1420 prefixEnd_1420 432084461919809151689 := by
  unfold tailWord_1420
  simp only [CollatzResearch.WordTrace]
  refine ⟨25895827431528680900857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34527769908704907867809 25895827431528680900857)
  ·
    refine ⟨19421870573646510675643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25895827431528680900857 19421870573646510675643)
    ·
      refine ⟨29132805860469766013465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19421870573646510675643 29132805860469766013465)
      ·
        refine ⟨21849604395352324510099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29132805860469766013465 21849604395352324510099)
        ·
          refine ⟨32774406593028486765149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21849604395352324510099 32774406593028486765149)
          ·
            refine ⟨12290402472385682536931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32774406593028486765149 12290402472385682536931)
            ·
              refine ⟨18435603708578523805397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12290402472385682536931 18435603708578523805397)
              ·
                refine ⟨432084461919809151689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18435603708578523805397 432084461919809151689)
                ·
                  rfl

theorem cell19_1420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_1420 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1420 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1420 prefixEnd_1420 := by exact prefixLift 1420
  have htrace : WordTrace (prefixWord ++ tailWord_1420) baseStart_1420 baseEnd_1420 := by
    simpa [prefixWord, tailWord_1420, baseEnd_1420] using wordTrace_append hprefix tailTrace_1420
  have hstable : (prefixWord ++ tailWord_1420).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1420).length < 2 ^ (prefixWord ++ tailWord_1420).sum := by decide
  have hdescent : baseEnd_1420 < baseStart_1420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439 : List Nat := [1, 1, 2, 5, 1, 9]
def baseStart_1439 : Nat := 118140960795 + 1439 * 2 ^ 59
def prefixEnd_1439 : Nat := 4983230072969 + 3 ^ 40 * 1439 * 2
def baseEnd_1439 : Nat := 48651763748154969935

theorem tailTrace_1439 : CollatzResearch.WordTrace tailWord_1439 prefixEnd_1439 48651763748154969935 := by
  unfold tailWord_1439
  simp only [CollatzResearch.WordTrace]
  refine ⟨52484641794223606743371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34989761196149071162247 52484641794223606743371)
  ·
    refine ⟨78726962691335410115057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52484641794223606743371 78726962691335410115057)
    ·
      refine ⟨59045222018501557586293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78726962691335410115057 59045222018501557586293)
      ·
        refine ⟨5535489564234521023715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59045222018501557586293 5535489564234521023715)
        ·
          refine ⟨8303234346351781535573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5535489564234521023715 8303234346351781535573)
          ·
            refine ⟨48651763748154969935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 8303234346351781535573 48651763748154969935)
            ·
              rfl

theorem cell19_1439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 9].length) (baseStart_1439 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1439 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1439 prefixEnd_1439 := by exact prefixLift 1439
  have htrace : WordTrace (prefixWord ++ tailWord_1439) baseStart_1439 baseEnd_1439 := by
    simpa [prefixWord, tailWord_1439, baseEnd_1439] using wordTrace_append hprefix tailTrace_1439
  have hstable : (prefixWord ++ tailWord_1439).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439).length < 2 ^ (prefixWord ++ tailWord_1439).sum := by decide
  have hdescent : baseEnd_1439 < baseStart_1439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458 : List Nat := [3, 2, 1, 1, 1, 1, 2, 8]
def baseStart_1458 : Nat := 118140960795 + 1458 * 2 ^ 59
def prefixEnd_1458 : Nat := 4983230072969 + 3 ^ 40 * 1458 * 2
def baseEnd_1458 : Nat := 443647285546980307141

theorem tailTrace_1458 : CollatzResearch.WordTrace tailWord_1458 prefixEnd_1458 443647285546980307141 := by
  unfold tailWord_1458
  simp only [CollatzResearch.WordTrace]
  refine ⟨13294407181347462921257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35451752483593234456685 13294407181347462921257)
  ·
    refine ⟨9970805386010597190943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13294407181347462921257 9970805386010597190943)
    ·
      refine ⟨14956208079015895786415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9970805386010597190943 14956208079015895786415)
      ·
        refine ⟨22434312118523843679623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14956208079015895786415 22434312118523843679623)
        ·
          refine ⟨33651468177785765519435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22434312118523843679623 33651468177785765519435)
          ·
            refine ⟨50477202266678648279153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33651468177785765519435 50477202266678648279153)
            ·
              refine ⟨37857901700008986209365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50477202266678648279153 37857901700008986209365)
              ·
                refine ⟨443647285546980307141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 37857901700008986209365 443647285546980307141)
                ·
                  rfl

theorem cell19_1458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_1458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1458 prefixEnd_1458 := by exact prefixLift 1458
  have htrace : WordTrace (prefixWord ++ tailWord_1458) baseStart_1458 baseEnd_1458 := by
    simpa [prefixWord, tailWord_1458, baseEnd_1458] using wordTrace_append hprefix tailTrace_1458
  have hstable : (prefixWord ++ tailWord_1458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458).length < 2 ^ (prefixWord ++ tailWord_1458).sum := by decide
  have hdescent : baseEnd_1458 < baseStart_1458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532 : List Nat := [2, 2, 2, 1, 2, 1, 6, 3]
def baseStart_1532 : Nat := 118140960795 + 1532 * 2 ^ 59
def prefixEnd_1532 : Nat := 4983230072969 + 3 ^ 40 * 1532 * 2
def baseEnd_1532 : Nat := 466164363136734662495

theorem tailTrace_1532 : CollatzResearch.WordTrace tailWord_1532 prefixEnd_1532 466164363136734662495 := by
  unfold tailWord_1532
  simp only [CollatzResearch.WordTrace]
  refine ⟨27938315228650244939425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37251086971533659919233 27938315228650244939425)
  ·
    refine ⟨20953736421487683704569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27938315228650244939425 20953736421487683704569)
    ·
      refine ⟨15715302316115762778427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20953736421487683704569 15715302316115762778427)
      ·
        refine ⟨23572953474173644167641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15715302316115762778427 23572953474173644167641)
        ·
          refine ⟨17679715105630233125731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23572953474173644167641 17679715105630233125731)
          ·
            refine ⟨26519572658445349688597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17679715105630233125731 26519572658445349688597)
            ·
              refine ⟨1243104968364625766653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26519572658445349688597 1243104968364625766653)
              ·
                refine ⟨466164363136734662495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1243104968364625766653 466164363136734662495)
                ·
                  rfl

theorem cell19_1532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_1532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1532 prefixEnd_1532 := by exact prefixLift 1532
  have htrace : WordTrace (prefixWord ++ tailWord_1532) baseStart_1532 baseEnd_1532 := by
    simpa [prefixWord, tailWord_1532, baseEnd_1532] using wordTrace_append hprefix tailTrace_1532
  have hstable : (prefixWord ++ tailWord_1532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532).length < 2 ^ (prefixWord ++ tailWord_1532).sum := by decide
  have hdescent : baseEnd_1532 < baseStart_1532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591 : List Nat := [1, 1, 3, 1, 2, 4, 2, 5]
def baseStart_1591 : Nat := 118140960795 + 1591 * 2 ^ 59
def prefixEnd_1591 : Nat := 4983230072969 + 3 ^ 40 * 1591 * 2
def baseEnd_1591 : Nat := 484117168242079351223

theorem tailTrace_1591 : CollatzResearch.WordTrace tailWord_1591 prefixEnd_1591 484117168242079351223 := by
  unfold tailWord_1591
  simp only [CollatzResearch.WordTrace]
  refine ⟨58028537243553566276627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38685691495702377517751 58028537243553566276627)
  ·
    refine ⟨87042805865330349414941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58028537243553566276627 87042805865330349414941)
    ·
      refine ⟨32641052199498881030603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87042805865330349414941 32641052199498881030603)
      ·
        refine ⟨48961578299248321545905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32641052199498881030603 48961578299248321545905)
        ·
          refine ⟨36721183724436241159429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48961578299248321545905 36721183724436241159429)
          ·
            refine ⟨6885221948331795217393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36721183724436241159429 6885221948331795217393)
            ·
              refine ⟨5163916461248846413045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6885221948331795217393 5163916461248846413045)
              ·
                refine ⟨484117168242079351223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5163916461248846413045 484117168242079351223)
                ·
                  rfl

theorem cell19_1591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_1591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1591 prefixEnd_1591 := by exact prefixLift 1591
  have htrace : WordTrace (prefixWord ++ tailWord_1591) baseStart_1591 baseEnd_1591 := by
    simpa [prefixWord, tailWord_1591, baseEnd_1591] using wordTrace_append hprefix tailTrace_1591
  have hstable : (prefixWord ++ tailWord_1591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591).length < 2 ^ (prefixWord ++ tailWord_1591).sum := by decide
  have hdescent : baseEnd_1591 < baseStart_1591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606 : List Nat := [6, 1, 1, 1, 3, 7]
def baseStart_1606 : Nat := 118140960795 + 1606 * 2 ^ 59
def prefixEnd_1606 : Nat := 4983230072969 + 3 ^ 40 * 1606 * 2
def baseEnd_1606 : Nat := 54297937858498779761

theorem tailTrace_1606 : CollatzResearch.WordTrace tailWord_1606 prefixEnd_1606 54297937858498779761 := by
  unfold tailWord_1606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1830488505912847752271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39050421459474085381781 1830488505912847752271)
  ·
    refine ⟨2745732758869271628407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1830488505912847752271 2745732758869271628407)
    ·
      refine ⟨4118599138303907442611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2745732758869271628407 4118599138303907442611)
      ·
        refine ⟨6177898707455861163917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4118599138303907442611 6177898707455861163917)
        ·
          refine ⟨2316712015295947936469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6177898707455861163917 2316712015295947936469)
          ·
            refine ⟨54297937858498779761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 2316712015295947936469 54297937858498779761)
            ·
              rfl

theorem cell19_1606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 7].length) (baseStart_1606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1606 prefixEnd_1606 := by exact prefixLift 1606
  have htrace : WordTrace (prefixWord ++ tailWord_1606) baseStart_1606 baseEnd_1606 := by
    simpa [prefixWord, tailWord_1606, baseEnd_1606] using wordTrace_append hprefix tailTrace_1606
  have hstable : (prefixWord ++ tailWord_1606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606).length < 2 ^ (prefixWord ++ tailWord_1606).sum := by decide
  have hdescent : baseEnd_1606 < baseStart_1606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724 : List Nat := [2, 2, 2, 3, 1, 2, 7]
def baseStart_1724 : Nat := 118140960795 + 1724 * 2 ^ 59
def prefixEnd_1724 : Nat := 4983230072969 + 3 ^ 40 * 1724 * 2
def baseEnd_1724 : Nat := 174862350312392798435

theorem tailTrace_1724 : CollatzResearch.WordTrace tailWord_1724 prefixEnd_1724 174862350312392798435 := by
  unfold tailWord_1724
  simp only [CollatzResearch.WordTrace]
  refine ⟨31439722880858640434113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41919630507811520578817 31439722880858640434113)
  ·
    refine ⟨23579792160643980325585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31439722880858640434113 23579792160643980325585)
    ·
      refine ⟨17684844120482985244189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23579792160643980325585 17684844120482985244189)
      ·
        refine ⟨6631816545181119466571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17684844120482985244189 6631816545181119466571)
        ·
          refine ⟨9947724817771679199857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6631816545181119466571 9947724817771679199857)
          ·
            refine ⟨7460793613328759399893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9947724817771679199857 7460793613328759399893)
            ·
              refine ⟨174862350312392798435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7460793613328759399893 174862350312392798435)
              ·
                rfl

theorem cell19_1724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_1724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1724 prefixEnd_1724 := by exact prefixLift 1724
  have htrace : WordTrace (prefixWord ++ tailWord_1724) baseStart_1724 baseEnd_1724 := by
    simpa [prefixWord, tailWord_1724, baseEnd_1724] using wordTrace_append hprefix tailTrace_1724
  have hstable : (prefixWord ++ tailWord_1724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724).length < 2 ^ (prefixWord ++ tailWord_1724).sum := by decide
  have hdescent : baseEnd_1724 < baseStart_1724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874 : List Nat := [3, 2, 2, 1, 1, 3, 4, 3]
def baseStart_1874 : Nat := 118140960795 + 1874 * 2 ^ 59
def prefixEnd_1874 : Nat := 4983230072969 + 3 ^ 40 * 1874 * 2
def baseEnd_1874 : Nat := 570229775781275061563

theorem tailTrace_1874 : CollatzResearch.WordTrace tailWord_1874 prefixEnd_1874 570229775781275061563 := by
  unfold tailWord_1874
  simp only [CollatzResearch.WordTrace]
  refine ⟨17087598804573224707169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45566930145528599219117 17087598804573224707169)
  ·
    refine ⟨12815699103429918530377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17087598804573224707169 12815699103429918530377)
    ·
      refine ⟨9611774327572438897783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12815699103429918530377 9611774327572438897783)
      ·
        refine ⟨14417661491358658346675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9611774327572438897783 14417661491358658346675)
        ·
          refine ⟨21626492237037987520013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14417661491358658346675 21626492237037987520013)
          ·
            refine ⟨8109934588889245320005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21626492237037987520013 8109934588889245320005)
            ·
              refine ⟨1520612735416733497501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8109934588889245320005 1520612735416733497501)
              ·
                refine ⟨570229775781275061563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1520612735416733497501 570229775781275061563)
                ·
                  rfl

theorem cell19_1874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_1874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1874 prefixEnd_1874 := by exact prefixLift 1874
  have htrace : WordTrace (prefixWord ++ tailWord_1874) baseStart_1874 baseEnd_1874 := by
    simpa [prefixWord, tailWord_1874, baseEnd_1874] using wordTrace_append hprefix tailTrace_1874
  have hstable : (prefixWord ++ tailWord_1874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874).length < 2 ^ (prefixWord ++ tailWord_1874).sum := by decide
  have hdescent : baseEnd_1874 < baseStart_1874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910 : List Nat := [5, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1910 : Nat := 118140960795 + 1910 * 2 ^ 59
def prefixEnd_1910 : Nat := 4983230072969 + 3 ^ 40 * 1910 * 2
def baseEnd_1910 : Nat := 581184029743858261465

theorem tailTrace_1910 : CollatzResearch.WordTrace tailWord_1910 prefixEnd_1910 581184029743858261465 := by
  unfold tailWord_1910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4353963942991940446199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46442282058580698092789 4353963942991940446199)
  ·
    refine ⟨6530945914487910669299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4353963942991940446199 6530945914487910669299)
    ·
      refine ⟨9796418871731866003949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6530945914487910669299 9796418871731866003949)
      ·
        refine ⟨3673657076899449751481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9796418871731866003949 3673657076899449751481)
        ·
          refine ⟨2755242807674587313611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3673657076899449751481 2755242807674587313611)
          ·
            refine ⟨4132864211511880970417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2755242807674587313611 4132864211511880970417)
            ·
              refine ⟨3099648158633910727813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4132864211511880970417 3099648158633910727813)
              ·
                refine ⟨581184029743858261465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3099648158633910727813 581184029743858261465)
                ·
                  rfl

theorem cell19_1910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1910 prefixEnd_1910 := by exact prefixLift 1910
  have htrace : WordTrace (prefixWord ++ tailWord_1910) baseStart_1910 baseEnd_1910 := by
    simpa [prefixWord, tailWord_1910, baseEnd_1910] using wordTrace_append hprefix tailTrace_1910
  have hstable : (prefixWord ++ tailWord_1910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910).length < 2 ^ (prefixWord ++ tailWord_1910).sum := by decide
  have hdescent : baseEnd_1910 < baseStart_1910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950 : List Nat := [4, 3, 1, 3, 8]
def baseStart_1950 : Nat := 118140960795 + 1950 * 2 ^ 59
def prefixEnd_1950 : Nat := 4983230072969 + 3 ^ 40 * 1950 * 2
def baseEnd_1950 : Nat := 21976126779096939721

theorem tailTrace_1950 : CollatzResearch.WordTrace tailWord_1950 prefixEnd_1950 21976126779096939721 := by
  unfold tailWord_1950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8890292867869734824413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47414895295305252396869 8890292867869734824413)
  ·
    refine ⟨3333859825451150559155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8890292867869734824413 3333859825451150559155)
    ·
      refine ⟨5000789738176725838733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3333859825451150559155 5000789738176725838733)
      ·
        refine ⟨1875296151816272189525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5000789738176725838733 1875296151816272189525)
        ·
          refine ⟨21976126779096939721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 1875296151816272189525 21976126779096939721)
          ·
            rfl

theorem cell19_1950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 8].length) (baseStart_1950 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1950 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1950 prefixEnd_1950 := by exact prefixLift 1950
  have htrace : WordTrace (prefixWord ++ tailWord_1950) baseStart_1950 baseEnd_1950 := by
    simpa [prefixWord, tailWord_1950, baseEnd_1950] using wordTrace_append hprefix tailTrace_1950
  have hstable : (prefixWord ++ tailWord_1950).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950).length < 2 ^ (prefixWord ++ tailWord_1950).sum := by decide
  have hdescent : baseEnd_1950 < baseStart_1950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969 : List Nat := [1, 2, 2, 4, 2, 3, 1, 4]
def baseStart_1969 : Nat := 118140960795 + 1969 * 2 ^ 59
def prefixEnd_1969 : Nat := 4983230072969 + 3 ^ 40 * 1969 * 2
def baseEnd_1969 : Nat := 599136834849202950193

theorem tailTrace_1969 : CollatzResearch.WordTrace tailWord_1969 prefixEnd_1969 599136834849202950193 := by
  unfold tailWord_1969
  simp only [CollatzResearch.WordTrace]
  refine ⟨71815329874124123536961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47876886582749415691307 71815329874124123536961)
  ·
    refine ⟨53861497405593092652721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71815329874124123536961 53861497405593092652721)
    ·
      refine ⟨40396123054194819489541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53861497405593092652721 40396123054194819489541)
      ·
        refine ⟨7574273072661528654289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40396123054194819489541 7574273072661528654289)
        ·
          refine ⟨5680704804496146490717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7574273072661528654289 5680704804496146490717)
          ·
            refine ⟨2130264301686054934019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5680704804496146490717 2130264301686054934019)
            ·
              refine ⟨3195396452529082401029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130264301686054934019 3195396452529082401029)
              ·
                refine ⟨599136834849202950193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3195396452529082401029 599136834849202950193)
                ·
                  rfl

theorem cell19_1969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_1969 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_1969 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_1969 prefixEnd_1969 := by exact prefixLift 1969
  have htrace : WordTrace (prefixWord ++ tailWord_1969) baseStart_1969 baseEnd_1969 := by
    simpa [prefixWord, tailWord_1969, baseEnd_1969] using wordTrace_append hprefix tailTrace_1969
  have hstable : (prefixWord ++ tailWord_1969).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969).length < 2 ^ (prefixWord ++ tailWord_1969).sum := by decide
  have hdescent : baseEnd_1969 < baseStart_1969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009 : List Nat := [1, 2, 1, 2, 6, 1, 6]
def baseStart_2009 : Nat := 118140960795 + 2009 * 2 ^ 59
def prefixEnd_2009 : Nat := 4983230072969 + 3 ^ 40 * 2009 * 2
def baseEnd_2009 : Nat := 203769409380320687065

theorem tailTrace_2009 : CollatzResearch.WordTrace tailWord_2009 prefixEnd_2009 203769409380320687065 := by
  unfold tailWord_2009
  simp only [CollatzResearch.WordTrace]
  refine ⟨73274249729210954993081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48849499819473969995387 73274249729210954993081)
  ·
    refine ⟨54955687296908216244811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73274249729210954993081 54955687296908216244811)
    ·
      refine ⟨82433530945362324367217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54955687296908216244811 82433530945362324367217)
      ·
        refine ⟨61825148209021743275413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82433530945362324367217 61825148209021743275413)
        ·
          refine ⟨2898053822297894216035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61825148209021743275413 2898053822297894216035)
          ·
            refine ⟨4347080733446841324053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898053822297894216035 4347080733446841324053)
            ·
              refine ⟨203769409380320687065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4347080733446841324053 203769409380320687065)
              ·
                rfl

theorem cell19_2009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 6].length) (baseStart_2009 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2009 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2009 prefixEnd_2009 := by exact prefixLift 2009
  have htrace : WordTrace (prefixWord ++ tailWord_2009) baseStart_2009 baseEnd_2009 := by
    simpa [prefixWord, tailWord_2009, baseEnd_2009] using wordTrace_append hprefix tailTrace_2009
  have hstable : (prefixWord ++ tailWord_2009).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009).length < 2 ^ (prefixWord ++ tailWord_2009).sum := by decide
  have hdescent : baseEnd_2009 < baseStart_2009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085 : List Nat := [1, 3, 1, 2, 2, 4, 2, 4]
def baseStart_2085 : Nat := 118140960795 + 2085 * 2 ^ 59
def prefixEnd_2085 : Nat := 4983230072969 + 3 ^ 40 * 2085 * 2
def baseEnd_2085 : Nat := 634433875395304372099

theorem tailTrace_2085 : CollatzResearch.WordTrace tailWord_2085 prefixEnd_2085 634433875395304372099 := by
  unfold tailWord_2085
  simp only [CollatzResearch.WordTrace]
  refine ⟨76046197453875934759709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50697464969250623173139 76046197453875934759709)
  ·
    refine ⟨28517324045203475534891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76046197453875934759709 28517324045203475534891)
    ·
      refine ⟨42775986067805213302337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28517324045203475534891 42775986067805213302337)
      ·
        refine ⟨32081989550853909976753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42775986067805213302337 32081989550853909976753)
        ·
          refine ⟨24061492163140432482565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32081989550853909976753 24061492163140432482565)
          ·
            refine ⟨4511529780588831090481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24061492163140432482565 4511529780588831090481)
            ·
              refine ⟨3383647335441623317861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4511529780588831090481 3383647335441623317861)
              ·
                refine ⟨634433875395304372099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3383647335441623317861 634433875395304372099)
                ·
                  rfl

theorem cell19_2085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_2085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2085 prefixEnd_2085 := by exact prefixLift 2085
  have htrace : WordTrace (prefixWord ++ tailWord_2085) baseStart_2085 baseEnd_2085 := by
    simpa [prefixWord, tailWord_2085, baseEnd_2085] using wordTrace_append hprefix tailTrace_2085
  have hstable : (prefixWord ++ tailWord_2085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085).length < 2 ^ (prefixWord ++ tailWord_2085).sum := by decide
  have hdescent : baseEnd_2085 < baseStart_2085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140 : List Nat := [2, 2, 4, 1, 1, 4, 1, 4]
def baseStart_2140 : Nat := 118140960795 + 2140 * 2 ^ 59
def prefixEnd_2140 : Nat := 4983230072969 + 3 ^ 40 * 2140 * 2
def baseEnd_2140 : Nat := 651169541171473149727

theorem tailTrace_2140 : CollatzResearch.WordTrace tailWord_2140 prefixEnd_2140 651169541171473149727 := by
  unfold tailWord_2140
  simp only [CollatzResearch.WordTrace]
  refine ⟨39026106127310164005937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52034808169746885341249 39026106127310164005937)
  ·
    refine ⟨29269579595482623004453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39026106127310164005937 29269579595482623004453)
    ·
      refine ⟨5488046174152991813335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29269579595482623004453 5488046174152991813335)
      ·
        refine ⟨8232069261229487720003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5488046174152991813335 8232069261229487720003)
        ·
          refine ⟨12348103891844231580005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8232069261229487720003 12348103891844231580005)
          ·
            refine ⟨2315269479720793421251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12348103891844231580005 2315269479720793421251)
            ·
              refine ⟨3472904219581190131877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2315269479720793421251 3472904219581190131877)
              ·
                refine ⟨651169541171473149727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3472904219581190131877 651169541171473149727)
                ·
                  rfl

theorem cell19_2140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_2140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2140 prefixEnd_2140 := by exact prefixLift 2140
  have htrace : WordTrace (prefixWord ++ tailWord_2140) baseStart_2140 baseEnd_2140 := by
    simpa [prefixWord, tailWord_2140, baseEnd_2140] using wordTrace_append hprefix tailTrace_2140
  have hstable : (prefixWord ++ tailWord_2140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140).length < 2 ^ (prefixWord ++ tailWord_2140).sum := by decide
  have hdescent : baseEnd_2140 < baseStart_2140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161 : List Nat := [1, 2, 2, 2, 1, 1, 7, 3]
def baseStart_2161 : Nat := 118140960795 + 2161 * 2 ^ 59
def prefixEnd_2161 : Nat := 4983230072969 + 3 ^ 40 * 2161 * 2
def baseEnd_2161 : Nat := 657559522649646683003

theorem tailTrace_2161 : CollatzResearch.WordTrace tailWord_2161 prefixEnd_2161 657559522649646683003 := by
  unfold tailWord_2161
  simp only [CollatzResearch.WordTrace]
  refine ⟨78818145178540914526337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52545430119027276350891 78818145178540914526337)
  ·
    refine ⟨59113608883905685894753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78818145178540914526337 59113608883905685894753)
    ·
      refine ⟨44335206662929264421065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59113608883905685894753 44335206662929264421065)
      ·
        refine ⟨33251404997196948315799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44335206662929264421065 33251404997196948315799)
        ·
          refine ⟨49877107495795422473699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33251404997196948315799 49877107495795422473699)
          ·
            refine ⟨74815661243693133710549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49877107495795422473699 74815661243693133710549)
            ·
              refine ⟨1753492060399057821341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 74815661243693133710549 1753492060399057821341)
              ·
                refine ⟨657559522649646683003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1753492060399057821341 657559522649646683003)
                ·
                  rfl

theorem cell19_2161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 3].length) (baseStart_2161 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2161 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2161 prefixEnd_2161 := by exact prefixLift 2161
  have htrace : WordTrace (prefixWord ++ tailWord_2161) baseStart_2161 baseEnd_2161 := by
    simpa [prefixWord, tailWord_2161, baseEnd_2161] using wordTrace_append hprefix tailTrace_2161
  have hstable : (prefixWord ++ tailWord_2161).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161).length < 2 ^ (prefixWord ++ tailWord_2161).sum := by decide
  have hdescent : baseEnd_2161 < baseStart_2161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313 : List Nat := [1, 2, 1, 1, 3, 6, 1, 4]
def baseStart_2313 : Nat := 118140960795 + 2313 * 2 ^ 59
def prefixEnd_2313 : Nat := 4983230072969 + 3 ^ 40 * 2313 * 2
def baseEnd_2313 : Nat := 703810817158331304811

theorem tailTrace_2313 : CollatzResearch.WordTrace tailWord_2313 prefixEnd_2313 703810817158331304811 := by
  unfold tailWord_2313
  simp only [CollatzResearch.WordTrace]
  refine ⟨84362040627870874059593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56241360418580582706395 84362040627870874059593)
  ·
    refine ⟨63271530470903155544695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84362040627870874059593 63271530470903155544695)
    ·
      refine ⟨94907295706354733317043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63271530470903155544695 94907295706354733317043)
      ·
        refine ⟨142360943559532099975565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94907295706354733317043 142360943559532099975565)
        ·
          refine ⟨53385353834824537490837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142360943559532099975565 53385353834824537490837)
          ·
            refine ⟨2502438461007400194883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53385353834824537490837 2502438461007400194883)
            ·
              refine ⟨3753657691511100292325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2502438461007400194883 3753657691511100292325)
              ·
                refine ⟨703810817158331304811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3753657691511100292325 703810817158331304811)
                ·
                  rfl

theorem cell19_2313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_2313 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2313 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2313 prefixEnd_2313 := by exact prefixLift 2313
  have htrace : WordTrace (prefixWord ++ tailWord_2313) baseStart_2313 baseEnd_2313 := by
    simpa [prefixWord, tailWord_2313, baseEnd_2313] using wordTrace_append hprefix tailTrace_2313
  have hstable : (prefixWord ++ tailWord_2313).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313).length < 2 ^ (prefixWord ++ tailWord_2313).sum := by decide
  have hdescent : baseEnd_2313 < baseStart_2313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330 : List Nat := [3, 1, 1, 3, 4, 1, 3, 3]
def baseStart_2330 : Nat := 118140960795 + 2330 * 2 ^ 59
def prefixEnd_2330 : Nat := 4983230072969 + 3 ^ 40 * 2330 * 2
def baseEnd_2330 : Nat := 708983659307328926987

theorem tailTrace_2330 : CollatzResearch.WordTrace tailWord_2330 prefixEnd_2330 708983659307328926987 := by
  unfold tailWord_2330
  simp only [CollatzResearch.WordTrace]
  refine ⟨21245520391570694357111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56654721044188518285629 21245520391570694357111)
  ·
    refine ⟨31868280587356041535667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21245520391570694357111 31868280587356041535667)
    ·
      refine ⟨47802420881034062303501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31868280587356041535667 47802420881034062303501)
      ·
        refine ⟨17925907830387773363813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47802420881034062303501 17925907830387773363813)
        ·
          refine ⟨3361107718197707505715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17925907830387773363813 3361107718197707505715)
          ·
            refine ⟨5041661577296561258573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3361107718197707505715 5041661577296561258573)
            ·
              refine ⟨1890623091486210471965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5041661577296561258573 1890623091486210471965)
              ·
                refine ⟨708983659307328926987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1890623091486210471965 708983659307328926987)
                ·
                  rfl

theorem cell19_2330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_2330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2330 prefixEnd_2330 := by exact prefixLift 2330
  have htrace : WordTrace (prefixWord ++ tailWord_2330) baseStart_2330 baseEnd_2330 := by
    simpa [prefixWord, tailWord_2330, baseEnd_2330] using wordTrace_append hprefix tailTrace_2330
  have hstable : (prefixWord ++ tailWord_2330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330).length < 2 ^ (prefixWord ++ tailWord_2330).sum := by decide
  have hdescent : baseEnd_2330 < baseStart_2330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349 : List Nat := [1, 5, 3, 1, 2, 1, 6]
def baseStart_2349 : Nat := 118140960795 + 2349 * 2 ^ 59
def prefixEnd_2349 : Nat := 4983230072969 + 3 ^ 40 * 2349 * 2
def baseEnd_2349 : Nat := 238255023706971501571

theorem tailTrace_2349 : CollatzResearch.WordTrace tailWord_2349 prefixEnd_2349 238255023706971501571 := by
  unfold tailWord_2349
  simp only [CollatzResearch.WordTrace]
  refine ⟨85675068497449022370101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57116712331632681580067 85675068497449022370101)
  ·
    refine ⟨8032037671635845847197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85675068497449022370101 8032037671635845847197)
    ·
      refine ⟨3012014126863442192699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8032037671635845847197 3012014126863442192699)
      ·
        refine ⟨4518021190295163289049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3012014126863442192699 4518021190295163289049)
        ·
          refine ⟨3388515892721372466787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4518021190295163289049 3388515892721372466787)
          ·
            refine ⟨5082773839082058700181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3388515892721372466787 5082773839082058700181)
            ·
              refine ⟨238255023706971501571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5082773839082058700181 238255023706971501571)
              ·
                rfl

theorem cell19_2349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 6].length) (baseStart_2349 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2349 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2349 prefixEnd_2349 := by exact prefixLift 2349
  have htrace : WordTrace (prefixWord ++ tailWord_2349) baseStart_2349 baseEnd_2349 := by
    simpa [prefixWord, tailWord_2349, baseEnd_2349] using wordTrace_append hprefix tailTrace_2349
  have hstable : (prefixWord ++ tailWord_2349).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349).length < 2 ^ (prefixWord ++ tailWord_2349).sum := by decide
  have hdescent : baseEnd_2349 < baseStart_2349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389 : List Nat := [1, 3, 2, 2, 4, 1, 1, 5]
def baseStart_2389 : Nat := 118140960795 + 2389 * 2 ^ 59
def prefixEnd_2389 : Nat := 4983230072969 + 3 ^ 40 * 2389 * 2
def baseEnd_2389 : Nat := 726936464412673615715

theorem tailTrace_2389 : CollatzResearch.WordTrace tailWord_2389 prefixEnd_2389 726936464412673615715 := by
  unfold tailWord_2389
  simp only [CollatzResearch.WordTrace]
  refine ⟨87133988352535853826221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58089325568357235884147 87133988352535853826221)
  ·
    refine ⟨32675245632200945184833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87133988352535853826221 32675245632200945184833)
    ·
      refine ⟨24506434224150708888625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32675245632200945184833 24506434224150708888625)
      ·
        refine ⟨18379825668113031666469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24506434224150708888625 18379825668113031666469)
        ·
          refine ⟨3446217312771193437463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18379825668113031666469 3446217312771193437463)
          ·
            refine ⟨5169325969156790156195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3446217312771193437463 5169325969156790156195)
            ·
              refine ⟨7753988953735185234293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5169325969156790156195 7753988953735185234293)
              ·
                refine ⟨726936464412673615715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7753988953735185234293 726936464412673615715)
                ·
                  rfl

theorem cell19_2389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_2389 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2389 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2389 prefixEnd_2389 := by exact prefixLift 2389
  have htrace : WordTrace (prefixWord ++ tailWord_2389) baseStart_2389 baseEnd_2389 := by
    simpa [prefixWord, tailWord_2389, baseEnd_2389] using wordTrace_append hprefix tailTrace_2389
  have hstable : (prefixWord ++ tailWord_2389).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389).length < 2 ^ (prefixWord ++ tailWord_2389).sum := by decide
  have hdescent : baseEnd_2389 < baseStart_2389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2391 : List Nat := [1, 1, 3, 2, 3, 1, 3, 5]
def baseStart_2391 : Nat := 118140960795 + 2391 * 2 ^ 59
def prefixEnd_2391 : Nat := 4983230072969 + 3 ^ 40 * 2391 * 2
def baseEnd_2391 : Nat := 727545034077261571265

theorem tailTrace_2391 : CollatzResearch.WordTrace tailWord_2391 prefixEnd_2391 727545034077261571265 := by
  unfold tailWord_2391
  simp only [CollatzResearch.WordTrace]
  refine ⟨87206934345290195399027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58137956230193463599351 87206934345290195399027)
  ·
    refine ⟨130810401517935293098541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87206934345290195399027 130810401517935293098541)
    ·
      refine ⟨49053900569225734911953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130810401517935293098541 49053900569225734911953)
      ·
        refine ⟨36790425426919301183965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49053900569225734911953 36790425426919301183965)
        ·
          refine ⟨13796409535094737943987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36790425426919301183965 13796409535094737943987)
          ·
            refine ⟨20694614302642106915981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13796409535094737943987 20694614302642106915981)
            ·
              refine ⟨7760480363490790093493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20694614302642106915981 7760480363490790093493)
              ·
                refine ⟨727545034077261571265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7760480363490790093493 727545034077261571265)
                ·
                  rfl

theorem cell19_2391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_2391 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2391 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2391 prefixEnd_2391 := by exact prefixLift 2391
  have htrace : WordTrace (prefixWord ++ tailWord_2391) baseStart_2391 baseEnd_2391 := by
    simpa [prefixWord, tailWord_2391, baseEnd_2391] using wordTrace_append hprefix tailTrace_2391
  have hstable : (prefixWord ++ tailWord_2391).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2391).length < 2 ^ (prefixWord ++ tailWord_2391).sum := by decide
  have hdescent : baseEnd_2391 < baseStart_2391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408 : List Nat := [2, 1, 4, 2, 2, 3, 5]
def baseStart_2408 : Nat := 118140960795 + 2408 * 2 ^ 59
def prefixEnd_2408 : Nat := 4983230072969 + 3 ^ 40 * 2408 * 2
def baseEnd_2408 : Nat := 244239292075419731147

theorem tailTrace_2408 : CollatzResearch.WordTrace tailWord_2408 prefixEnd_2408 244239292075419731147 := by
  unfold tailWord_2408
  simp only [CollatzResearch.WordTrace]
  refine ⟨43913487641851049383939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58551316855801399178585 43913487641851049383939)
  ·
    refine ⟨65870231462776574075909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43913487641851049383939 65870231462776574075909)
    ·
      refine ⟨12350668399270607639233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65870231462776574075909 12350668399270607639233)
      ·
        refine ⟨9263001299452955729425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12350668399270607639233 9263001299452955729425)
        ·
          refine ⟨6947250974589716797069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9263001299452955729425 6947250974589716797069)
          ·
            refine ⟨2605219115471143798901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6947250974589716797069 2605219115471143798901)
            ·
              refine ⟨244239292075419731147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2605219115471143798901 244239292075419731147)
              ·
                rfl

theorem cell19_2408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 5].length) (baseStart_2408 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2408 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2408 prefixEnd_2408 := by exact prefixLift 2408
  have htrace : WordTrace (prefixWord ++ tailWord_2408) baseStart_2408 baseEnd_2408 := by
    simpa [prefixWord, tailWord_2408, baseEnd_2408] using wordTrace_append hprefix tailTrace_2408
  have hstable : (prefixWord ++ tailWord_2408).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408).length < 2 ^ (prefixWord ++ tailWord_2408).sum := by decide
  have hdescent : baseEnd_2408 < baseStart_2408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429 : List Nat := [1, 4, 1, 1, 2, 3, 1, 6]
def baseStart_2429 : Nat := 118140960795 + 2429 * 2 ^ 59
def prefixEnd_2429 : Nat := 4983230072969 + 3 ^ 40 * 2429 * 2
def baseEnd_2429 : Nat := 739107857704432726717

theorem tailTrace_2429 : CollatzResearch.WordTrace tailWord_2429 prefixEnd_2429 739107857704432726717 := by
  unfold tailWord_2429
  simp only [CollatzResearch.WordTrace]
  refine ⟨88592908207622685282341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59061938805081790188227 88592908207622685282341)
  ·
    refine ⟨16611170288929253490439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88592908207622685282341 16611170288929253490439)
    ·
      refine ⟨24916755433393880235659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16611170288929253490439 24916755433393880235659)
      ·
        refine ⟨37375133150090820353489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24916755433393880235659 37375133150090820353489)
        ·
          refine ⟨28031349862568115265117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37375133150090820353489 28031349862568115265117)
          ·
            refine ⟨10511756198463043224419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28031349862568115265117 10511756198463043224419)
            ·
              refine ⟨15767634297694564836629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10511756198463043224419 15767634297694564836629)
              ·
                refine ⟨739107857704432726717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15767634297694564836629 739107857704432726717)
                ·
                  rfl

theorem cell19_2429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_2429 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2429 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2429 prefixEnd_2429 := by exact prefixLift 2429
  have htrace : WordTrace (prefixWord ++ tailWord_2429) baseStart_2429 baseEnd_2429 := by
    simpa [prefixWord, tailWord_2429, baseEnd_2429] using wordTrace_append hprefix tailTrace_2429
  have hstable : (prefixWord ++ tailWord_2429).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429).length < 2 ^ (prefixWord ++ tailWord_2429).sum := by decide
  have hdescent : baseEnd_2429 < baseStart_2429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446 : List Nat := [4, 1, 1, 4, 1, 1, 2, 5]
def baseStart_2446 : Nat := 118140960795 + 2446 * 2 ^ 59
def prefixEnd_2446 : Nat := 4983230072969 + 3 ^ 40 * 2446 * 2
def baseEnd_2446 : Nat := 744280699853430348893

theorem tailTrace_2446 : CollatzResearch.WordTrace tailWord_2446 prefixEnd_2446 744280699853430348893 := by
  unfold tailWord_2446
  simp only [CollatzResearch.WordTrace]
  refine ⟨11151618643254323581399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59475299430689725767461 11151618643254323581399)
  ·
    refine ⟨16727427964881485372099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11151618643254323581399 16727427964881485372099)
    ·
      refine ⟨25091141947322228058149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16727427964881485372099 25091141947322228058149)
      ·
        refine ⟨4704589115122917760903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25091141947322228058149 4704589115122917760903)
        ·
          refine ⟨7056883672684376641355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4704589115122917760903 7056883672684376641355)
          ·
            refine ⟨10585325509026564962033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7056883672684376641355 10585325509026564962033)
            ·
              refine ⟨7938994131769923721525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10585325509026564962033 7938994131769923721525)
              ·
                refine ⟨744280699853430348893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7938994131769923721525 744280699853430348893)
                ·
                  rfl

theorem cell19_2446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_2446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2446 prefixEnd_2446 := by exact prefixLift 2446
  have htrace : WordTrace (prefixWord ++ tailWord_2446) baseStart_2446 baseEnd_2446 := by
    simpa [prefixWord, tailWord_2446, baseEnd_2446] using wordTrace_append hprefix tailTrace_2446
  have hstable : (prefixWord ++ tailWord_2446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446).length < 2 ^ (prefixWord ++ tailWord_2446).sum := by decide
  have hdescent : baseEnd_2446 < baseStart_2446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2465 : List Nat := [1, 2, 3, 5, 1, 7]
def baseStart_2465 : Nat := 118140960795 + 2465 * 2 ^ 59
def prefixEnd_2465 : Nat := 4983230072969 + 3 ^ 40 * 2465 * 2
def baseEnd_2465 : Nat := 83340234629668436291

theorem tailTrace_2465 : CollatzResearch.WordTrace tailWord_2465 prefixEnd_2465 83340234629668436291 := by
  unfold tailWord_2465
  simp only [CollatzResearch.WordTrace]
  refine ⟨89905936077200833592849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59937290718133889061899 89905936077200833592849)
  ·
    refine ⟨67429452057900625194637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89905936077200833592849 67429452057900625194637)
    ·
      refine ⟨25286044521712734447989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67429452057900625194637 25286044521712734447989)
      ·
        refine ⟨2370566673910568854499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25286044521712734447989 2370566673910568854499)
        ·
          refine ⟨3555850010865853281749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2370566673910568854499 3555850010865853281749)
          ·
            refine ⟨83340234629668436291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 3555850010865853281749 83340234629668436291)
            ·
              rfl

theorem cell19_2465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 7].length) (baseStart_2465 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2465 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2465 prefixEnd_2465 := by exact prefixLift 2465
  have htrace : WordTrace (prefixWord ++ tailWord_2465) baseStart_2465 baseEnd_2465 := by
    simpa [prefixWord, tailWord_2465, baseEnd_2465] using wordTrace_append hprefix tailTrace_2465
  have hstable : (prefixWord ++ tailWord_2465).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2465).length < 2 ^ (prefixWord ++ tailWord_2465).sum := by decide
  have hdescent : baseEnd_2465 < baseStart_2465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497 : List Nat := [1, 2, 7, 1, 1, 1, 3, 3]
def baseStart_2497 : Nat := 118140960795 + 2497 * 2 ^ 59
def prefixEnd_2497 : Nat := 4983230072969 + 3 ^ 40 * 2497 * 2
def baseEnd_2497 : Nat := 759799226300423215421

theorem tailTrace_2497 : CollatzResearch.WordTrace tailWord_2497 prefixEnd_2497 759799226300423215421 := by
  unfold tailWord_2497
  simp only [CollatzResearch.WordTrace]
  refine ⟨91073071961270298757745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60715381307513532505163 91073071961270298757745)
  ·
    refine ⟨68304803970952724068309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91073071961270298757745 68304803970952724068309)
    ·
      refine ⟨1600893843069204470351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 68304803970952724068309 1600893843069204470351)
      ·
        refine ⟨2401340764603806705527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1600893843069204470351 2401340764603806705527)
        ·
          refine ⟨3602011146905710058291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2401340764603806705527 3602011146905710058291)
          ·
            refine ⟨5403016720358565087437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3602011146905710058291 5403016720358565087437)
            ·
              refine ⟨2026131270134461907789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5403016720358565087437 2026131270134461907789)
              ·
                refine ⟨759799226300423215421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2026131270134461907789 759799226300423215421)
                ·
                  rfl

theorem cell19_2497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 3].length) (baseStart_2497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2497 prefixEnd_2497 := by exact prefixLift 2497
  have htrace : WordTrace (prefixWord ++ tailWord_2497) baseStart_2497 baseEnd_2497 := by
    simpa [prefixWord, tailWord_2497, baseEnd_2497] using wordTrace_append hprefix tailTrace_2497
  have hstable : (prefixWord ++ tailWord_2497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497).length < 2 ^ (prefixWord ++ tailWord_2497).sum := by decide
  have hdescent : baseEnd_2497 < baseStart_2497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503 : List Nat := [1, 1, 4, 1, 1, 5, 3, 3]
def baseStart_2503 : Nat := 118140960795 + 2503 * 2 ^ 59
def prefixEnd_2503 : Nat := 4983230072969 + 3 ^ 40 * 2503 * 2
def baseEnd_2503 : Nat := 761624935294187082071

theorem tailTrace_2503 : CollatzResearch.WordTrace tailWord_2503 prefixEnd_2503 761624935294187082071 := by
  unfold tailWord_2503
  simp only [CollatzResearch.WordTrace]
  refine ⟨91291909939533323476163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60861273293022215650775 91291909939533323476163)
  ·
    refine ⟨136937864909299985214245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91291909939533323476163 136937864909299985214245)
    ·
      refine ⟨25675849670493747227671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136937864909299985214245 25675849670493747227671)
      ·
        refine ⟨38513774505740620841507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25675849670493747227671 38513774505740620841507)
        ·
          refine ⟨57770661758610931262261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38513774505740620841507 57770661758610931262261)
          ·
            refine ⟨5415999539869774805837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57770661758610931262261 5415999539869774805837)
            ·
              refine ⟨2030999827451165552189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5415999539869774805837 2030999827451165552189)
              ·
                refine ⟨761624935294187082071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2030999827451165552189 761624935294187082071)
                ·
                  rfl

theorem cell19_2503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 3].length) (baseStart_2503 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2503 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2503 prefixEnd_2503 := by exact prefixLift 2503
  have htrace : WordTrace (prefixWord ++ tailWord_2503) baseStart_2503 baseEnd_2503 := by
    simpa [prefixWord, tailWord_2503, baseEnd_2503] using wordTrace_append hprefix tailTrace_2503
  have hstable : (prefixWord ++ tailWord_2503).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503).length < 2 ^ (prefixWord ++ tailWord_2503).sum := by decide
  have hdescent : baseEnd_2503 < baseStart_2503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2596 : List Nat := [2, 3, 1, 5, 1, 1, 2, 4]
def baseStart_2596 : Nat := 118140960795 + 2596 * 2 ^ 59
def prefixEnd_2596 : Nat := 4983230072969 + 3 ^ 40 * 2596 * 2
def baseEnd_2596 : Nat := 789923424697527015151

theorem tailTrace_2596 : CollatzResearch.WordTrace tailWord_2596 prefixEnd_2596 789923424697527015151 := by
  unfold tailWord_2596
  simp only [CollatzResearch.WordTrace]
  refine ⟨47341949301305103305821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63122599068406804407761 47341949301305103305821)
  ·
    refine ⟨17753230987989413739683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47341949301305103305821 17753230987989413739683)
    ·
      refine ⟨26629846481984120609525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17753230987989413739683 26629846481984120609525)
      ·
        refine ⟨2496548107686011307143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26629846481984120609525 2496548107686011307143)
        ·
          refine ⟨3744822161529016960715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2496548107686011307143 3744822161529016960715)
          ·
            refine ⟨5617233242293525441073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3744822161529016960715 5617233242293525441073)
            ·
              refine ⟨4212924931720144080805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5617233242293525441073 4212924931720144080805)
              ·
                refine ⟨789923424697527015151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4212924931720144080805 789923424697527015151)
                ·
                  rfl

theorem cell19_2596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_2596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2596 prefixEnd_2596 := by exact prefixLift 2596
  have htrace : WordTrace (prefixWord ++ tailWord_2596) baseStart_2596 baseEnd_2596 := by
    simpa [prefixWord, tailWord_2596, baseEnd_2596] using wordTrace_append hprefix tailTrace_2596
  have hstable : (prefixWord ++ tailWord_2596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2596).length < 2 ^ (prefixWord ++ tailWord_2596).sum := by decide
  have hdescent : baseEnd_2596 < baseStart_2596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657 : List Nat := [1, 2, 3, 1, 1, 4, 3, 4]
def baseStart_2657 : Nat := 118140960795 + 2657 * 2 ^ 59
def prefixEnd_2657 : Nat := 4983230072969 + 3 ^ 40 * 2657 * 2
def baseEnd_2657 : Nat := 808484799467459659429

theorem tailTrace_2657 : CollatzResearch.WordTrace tailWord_2657 prefixEnd_2657 808484799467459659429 := by
  unfold tailWord_2657
  simp only [CollatzResearch.WordTrace]
  refine ⟨96908751381617624582225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64605834254411749721483 96908751381617624582225)
  ·
    refine ⟨72681563536213218436669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96908751381617624582225 72681563536213218436669)
    ·
      refine ⟨27255586326079956913751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72681563536213218436669 27255586326079956913751)
      ·
        refine ⟨40883379489119935370627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27255586326079956913751 40883379489119935370627)
        ·
          refine ⟨61325069233679903055941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40883379489119935370627 61325069233679903055941)
          ·
            refine ⟨11498450481314981822989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61325069233679903055941 11498450481314981822989)
            ·
              refine ⟨4311918930493118183621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11498450481314981822989 4311918930493118183621)
              ·
                refine ⟨808484799467459659429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4311918930493118183621 808484799467459659429)
                ·
                  rfl

theorem cell19_2657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_2657 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2657 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2657 prefixEnd_2657 := by exact prefixLift 2657
  have htrace : WordTrace (prefixWord ++ tailWord_2657) baseStart_2657 baseEnd_2657 := by
    simpa [prefixWord, tailWord_2657, baseEnd_2657] using wordTrace_append hprefix tailTrace_2657
  have hstable : (prefixWord ++ tailWord_2657).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657).length < 2 ^ (prefixWord ++ tailWord_2657).sum := by decide
  have hdescent : baseEnd_2657 < baseStart_2657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727 : List Nat := [1, 1, 6, 3, 1, 2, 2, 3]
def baseStart_2727 : Nat := 118140960795 + 2727 * 2 ^ 59
def prefixEnd_2727 : Nat := 4983230072969 + 3 ^ 40 * 2727 * 2
def baseEnd_2727 : Nat := 829784737728038103683

theorem tailTrace_2727 : CollatzResearch.WordTrace tailWord_2727 prefixEnd_2727 829784737728038103683 := by
  unfold tailWord_2727
  simp only [CollatzResearch.WordTrace]
  refine ⟨99461861128019579630435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66307907418679719753623 99461861128019579630435)
  ·
    refine ⟨149192791692029369445653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99461861128019579630435 149192791692029369445653)
    ·
      refine ⟨6993412110563876692765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 149192791692029369445653 6993412110563876692765)
      ·
        refine ⟨2622529541461453759787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6993412110563876692765 2622529541461453759787)
        ·
          refine ⟨3933794312192180639681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2622529541461453759787 3933794312192180639681)
          ·
            refine ⟨2950345734144135479761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3933794312192180639681 2950345734144135479761)
            ·
              refine ⟨2212759300608101609821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2950345734144135479761 2212759300608101609821)
              ·
                refine ⟨829784737728038103683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2212759300608101609821 829784737728038103683)
                ·
                  rfl

theorem cell19_2727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 3].length) (baseStart_2727 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2727 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2727 prefixEnd_2727 := by exact prefixLift 2727
  have htrace : WordTrace (prefixWord ++ tailWord_2727) baseStart_2727 baseEnd_2727 := by
    simpa [prefixWord, tailWord_2727, baseEnd_2727] using wordTrace_append hprefix tailTrace_2727
  have hstable : (prefixWord ++ tailWord_2727).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727).length < 2 ^ (prefixWord ++ tailWord_2727).sum := by decide
  have hdescent : baseEnd_2727 < baseStart_2727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2752 : List Nat := [2, 1, 1, 2, 4, 4, 5]
def baseStart_2752 : Nat := 118140960795 + 2752 * 2 ^ 59
def prefixEnd_2752 : Nat := 4983230072969 + 3 ^ 40 * 2752 * 2
def baseEnd_2752 : Nat := 279130619511795849353

theorem tailTrace_2752 : CollatzResearch.WordTrace tailWord_2752 prefixEnd_2752 279130619511795849353 := by
  unfold tailWord_2752
  simp only [CollatzResearch.WordTrace]
  refine ⟨50186843018724424645255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66915790691632566193673 50186843018724424645255)
  ·
    refine ⟨75280264528086636967883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50186843018724424645255 75280264528086636967883)
    ·
      refine ⟨112920396792129955451825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75280264528086636967883 112920396792129955451825)
      ·
        refine ⟨84690297594097466588869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112920396792129955451825 84690297594097466588869)
        ·
          refine ⟨15879430798893274985413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84690297594097466588869 15879430798893274985413)
          ·
            refine ⟨2977393274792489059765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15879430798893274985413 2977393274792489059765)
            ·
              refine ⟨279130619511795849353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2977393274792489059765 279130619511795849353)
              ·
                rfl

theorem cell19_2752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 5].length) (baseStart_2752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2752 prefixEnd_2752 := by exact prefixLift 2752
  have htrace : WordTrace (prefixWord ++ tailWord_2752) baseStart_2752 baseEnd_2752 := by
    simpa [prefixWord, tailWord_2752, baseEnd_2752] using wordTrace_append hprefix tailTrace_2752
  have hstable : (prefixWord ++ tailWord_2752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2752).length < 2 ^ (prefixWord ++ tailWord_2752).sum := by decide
  have hdescent : baseEnd_2752 < baseStart_2752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805 : List Nat := [1, 3, 6, 1, 1, 7]
def baseStart_2805 : Nat := 118140960795 + 2805 * 2 ^ 59
def prefixEnd_2805 : Nat := 4983230072969 + 3 ^ 40 * 2805 * 2
def baseEnd_2805 : Nat := 94835439405218707793

theorem tailTrace_2805 : CollatzResearch.WordTrace tailWord_2805 prefixEnd_2805 94835439405218707793 := by
  unfold tailWord_2805
  simp only [CollatzResearch.WordTrace]
  refine ⟨102306754845438900969869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68204503230292600646579 102306754845438900969869)
  ·
    refine ⟨38365033067039587863701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102306754845438900969869 38365033067039587863701)
    ·
      refine ⟨1798360925017480681111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38365033067039587863701 1798360925017480681111)
      ·
        refine ⟨2697541387526221021667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1798360925017480681111 2697541387526221021667)
        ·
          refine ⟨4046312081289331532501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2697541387526221021667 4046312081289331532501)
          ·
            refine ⟨94835439405218707793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4046312081289331532501 94835439405218707793)
            ·
              rfl

theorem cell19_2805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 7].length) (baseStart_2805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2805 prefixEnd_2805 := by exact prefixLift 2805
  have htrace : WordTrace (prefixWord ++ tailWord_2805) baseStart_2805 baseEnd_2805 := by
    simpa [prefixWord, tailWord_2805, baseEnd_2805] using wordTrace_append hprefix tailTrace_2805
  have hstable : (prefixWord ++ tailWord_2805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805).length < 2 ^ (prefixWord ++ tailWord_2805).sum := by decide
  have hdescent : baseEnd_2805 < baseStart_2805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887 : List Nat := [1, 1, 4, 1, 2, 1, 1, 8]
def baseStart_2887 : Nat := 118140960795 + 2887 * 2 ^ 59
def prefixEnd_2887 : Nat := 4983230072969 + 3 ^ 40 * 2887 * 2
def baseEnd_2887 : Nat := 878470310895074547691

theorem tailTrace_2887 : CollatzResearch.WordTrace tailWord_2887 prefixEnd_2887 878470310895074547691 := by
  unfold tailWord_2887
  simp only [CollatzResearch.WordTrace]
  refine ⟨105297540548366905454915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70198360365577936969943 105297540548366905454915)
  ·
    refine ⟨157946310822550358182373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105297540548366905454915 157946310822550358182373)
    ·
      refine ⟨29614933279228192159195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157946310822550358182373 29614933279228192159195)
      ·
        refine ⟨44422399918842288238793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29614933279228192159195 44422399918842288238793)
        ·
          refine ⟨33316799939131716179095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44422399918842288238793 33316799939131716179095)
          ·
            refine ⟨49975199908697574268643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33316799939131716179095 49975199908697574268643)
            ·
              refine ⟨74962799863046361402965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49975199908697574268643 74962799863046361402965)
              ·
                refine ⟨878470310895074547691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 74962799863046361402965 878470310895074547691)
                ·
                  rfl

theorem cell19_2887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_2887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2887 prefixEnd_2887 := by exact prefixLift 2887
  have htrace : WordTrace (prefixWord ++ tailWord_2887) baseStart_2887 baseEnd_2887 := by
    simpa [prefixWord, tailWord_2887, baseEnd_2887] using wordTrace_append hprefix tailTrace_2887
  have hstable : (prefixWord ++ tailWord_2887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887).length < 2 ^ (prefixWord ++ tailWord_2887).sum := by decide
  have hdescent : baseEnd_2887 < baseStart_2887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900 : List Nat := [2, 4, 1, 1, 4, 2, 2, 3]
def baseStart_2900 : Nat := 118140960795 + 2900 * 2 ^ 59
def prefixEnd_2900 : Nat := 4983230072969 + 3 ^ 40 * 2900 * 2
def baseEnd_2900 : Nat := 882426013714896258767

theorem tailTrace_2900 : CollatzResearch.WordTrace tailWord_2900 prefixEnd_2900 882426013714896258767 := by
  unfold tailWord_2900
  simp only [CollatzResearch.WordTrace]
  refine ⟨52885844750635062839077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70514459667513417118769 52885844750635062839077)
  ·
    refine ⟨9916095890744074282327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52885844750635062839077 9916095890744074282327)
    ·
      refine ⟨14874143836116111423491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9916095890744074282327 14874143836116111423491)
      ·
        refine ⟨22311215754174167135237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14874143836116111423491 22311215754174167135237)
        ·
          refine ⟨4183352953907656337857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22311215754174167135237 4183352953907656337857)
          ·
            refine ⟨3137514715430742253393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4183352953907656337857 3137514715430742253393)
            ·
              refine ⟨2353136036573056690045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3137514715430742253393 2353136036573056690045)
              ·
                refine ⟨882426013714896258767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2353136036573056690045 882426013714896258767)
                ·
                  rfl

theorem cell19_2900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_2900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_2900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_2900 prefixEnd_2900 := by exact prefixLift 2900
  have htrace : WordTrace (prefixWord ++ tailWord_2900) baseStart_2900 baseEnd_2900 := by
    simpa [prefixWord, tailWord_2900, baseEnd_2900] using wordTrace_append hprefix tailTrace_2900
  have hstable : (prefixWord ++ tailWord_2900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900).length < 2 ^ (prefixWord ++ tailWord_2900).sum := by decide
  have hdescent : baseEnd_2900 < baseStart_2900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016 : List Nat := [2, 1, 3, 1, 5, 1, 3, 3]
def baseStart_3016 : Nat := 118140960795 + 3016 * 2 ^ 59
def prefixEnd_3016 : Nat := 4983230072969 + 3 ^ 40 * 3016 * 2
def baseEnd_3016 : Nat := 917723054260997680673

theorem tailTrace_3016 : CollatzResearch.WordTrace tailWord_3016 prefixEnd_3016 917723054260997680673 := by
  unfold tailWord_3016
  simp only [CollatzResearch.WordTrace]
  refine ⟨55001278540510968450451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73335038054014624600601 55001278540510968450451)
  ·
    refine ⟨82501917810766452675677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55001278540510968450451 82501917810766452675677)
    ·
      refine ⟨30938219179037419753379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82501917810766452675677 30938219179037419753379)
      ·
        refine ⟨46407328768556129630069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30938219179037419753379 46407328768556129630069)
        ·
          refine ⟨4350687072052137152819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46407328768556129630069 4350687072052137152819)
          ·
            refine ⟨6526030608078205729229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4350687072052137152819 6526030608078205729229)
            ·
              refine ⟨2447261478029327148461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6526030608078205729229 2447261478029327148461)
              ·
                refine ⟨917723054260997680673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2447261478029327148461 917723054260997680673)
                ·
                  rfl

theorem cell19_3016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_3016 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3016 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3016 prefixEnd_3016 := by exact prefixLift 3016
  have htrace : WordTrace (prefixWord ++ tailWord_3016) baseStart_3016 baseEnd_3016 := by
    simpa [prefixWord, tailWord_3016, baseEnd_3016] using wordTrace_append hprefix tailTrace_3016
  have hstable : (prefixWord ++ tailWord_3016).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016).length < 2 ^ (prefixWord ++ tailWord_3016).sum := by decide
  have hdescent : baseEnd_3016 < baseStart_3016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3037 : List Nat := [1, 4, 3, 1, 2, 2, 6]
def baseStart_3037 : Nat := 118140960795 + 3037 * 2 ^ 59
def prefixEnd_3037 : Nat := 4983230072969 + 3 ^ 40 * 3037 * 2
def baseEnd_3037 : Nat := 308037678579723737983

theorem tailTrace_3037 : CollatzResearch.WordTrace tailWord_3037 prefixEnd_3037 308037678579723737983 := by
  unfold tailWord_3037
  simp only [CollatzResearch.WordTrace]
  refine ⟨110768490004942523415365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73845660003295015610243 110768490004942523415365)
  ·
    refine ⟨20769091875926723140381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110768490004942523415365 20769091875926723140381)
    ·
      refine ⟨7788409453472521177643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20769091875926723140381 7788409453472521177643)
      ·
        refine ⟨11682614180208781766465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7788409453472521177643 11682614180208781766465)
        ·
          refine ⟨8761960635156586324849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11682614180208781766465 8761960635156586324849)
          ·
            refine ⟨6571470476367439743637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8761960635156586324849 6571470476367439743637)
            ·
              refine ⟨308037678579723737983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6571470476367439743637 308037678579723737983)
              ·
                rfl

theorem cell19_3037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 6].length) (baseStart_3037 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3037 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3037 prefixEnd_3037 := by exact prefixLift 3037
  have htrace : WordTrace (prefixWord ++ tailWord_3037) baseStart_3037 baseEnd_3037 := by
    simpa [prefixWord, tailWord_3037, baseEnd_3037] using wordTrace_append hprefix tailTrace_3037
  have hstable : (prefixWord ++ tailWord_3037).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3037).length < 2 ^ (prefixWord ++ tailWord_3037).sum := by decide
  have hdescent : baseEnd_3037 < baseStart_3037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073 : List Nat := [1, 2, 4, 1, 2, 4, 2, 3]
def baseStart_3073 : Nat := 118140960795 + 3073 * 2 ^ 59
def prefixEnd_3073 : Nat := 4983230072969 + 3 ^ 40 * 3073 * 2
def baseEnd_3073 : Nat := 935067289701754413851

theorem tailTrace_3073 : CollatzResearch.WordTrace tailWord_3073 prefixEnd_3073 935067289701754413851 := by
  unfold tailWord_3073
  simp only [CollatzResearch.WordTrace]
  refine ⟨112081517874520671725873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74721011916347114483915 112081517874520671725873)
  ·
    refine ⟨84061138405890503794405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112081517874520671725873 84061138405890503794405)
    ·
      refine ⟨15761463451104469461451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84061138405890503794405 15761463451104469461451)
      ·
        refine ⟨23642195176656704192177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15761463451104469461451 23642195176656704192177)
        ·
          refine ⟨17731646382492528144133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23642195176656704192177 17731646382492528144133)
          ·
            refine ⟨3324683696717349027025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17731646382492528144133 3324683696717349027025)
            ·
              refine ⟨2493512772538011770269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3324683696717349027025 2493512772538011770269)
              ·
                refine ⟨935067289701754413851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2493512772538011770269 935067289701754413851)
                ·
                  rfl

theorem cell19_3073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 3].length) (baseStart_3073 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3073 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3073 prefixEnd_3073 := by exact prefixLift 3073
  have htrace : WordTrace (prefixWord ++ tailWord_3073) baseStart_3073 baseEnd_3073 := by
    simpa [prefixWord, tailWord_3073, baseEnd_3073] using wordTrace_append hprefix tailTrace_3073
  have hstable : (prefixWord ++ tailWord_3073).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073).length < 2 ^ (prefixWord ++ tailWord_3073).sum := by decide
  have hdescent : baseEnd_3073 < baseStart_3073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077 : List Nat := [1, 3, 1, 1, 2, 3, 3, 5]
def baseStart_3077 : Nat := 118140960795 + 3077 * 2 ^ 59
def prefixEnd_3077 : Nat := 4983230072969 + 3 ^ 40 * 3077 * 2
def baseEnd_3077 : Nat := 936284429030930324951

theorem tailTrace_3077 : CollatzResearch.WordTrace tailWord_3077 prefixEnd_3077 936284429030930324951 := by
  unfold tailWord_3077
  simp only [CollatzResearch.WordTrace]
  refine ⟨112227409860029354871485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74818273240019569914323 112227409860029354871485)
  ·
    refine ⟨42085278697511008076807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112227409860029354871485 42085278697511008076807)
    ·
      refine ⟨63127918046266512115211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42085278697511008076807 63127918046266512115211)
      ·
        refine ⟨94691877069399768172817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63127918046266512115211 94691877069399768172817)
        ·
          refine ⟨71018907802049826129613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94691877069399768172817 71018907802049826129613)
          ·
            refine ⟨26632090425768684798605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71018907802049826129613 26632090425768684798605)
            ·
              refine ⟨9987033909663256799477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26632090425768684798605 9987033909663256799477)
              ·
                refine ⟨936284429030930324951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9987033909663256799477 936284429030930324951)
                ·
                  rfl

theorem cell19_3077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_3077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3077 prefixEnd_3077 := by exact prefixLift 3077
  have htrace : WordTrace (prefixWord ++ tailWord_3077) baseStart_3077 baseEnd_3077 := by
    simpa [prefixWord, tailWord_3077, baseEnd_3077] using wordTrace_append hprefix tailTrace_3077
  have hstable : (prefixWord ++ tailWord_3077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077).length < 2 ^ (prefixWord ++ tailWord_3077).sum := by decide
  have hdescent : baseEnd_3077 < baseStart_3077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096 : List Nat := [2, 1, 2, 3, 2, 2, 7]
def baseStart_3096 : Nat := 118140960795 + 3096 * 2 ^ 59
def prefixEnd_3096 : Nat := 4983230072969 + 3 ^ 40 * 3096 * 2
def baseEnd_3096 : Nat := 314021946948171967559

theorem tailTrace_3096 : CollatzResearch.WordTrace tailWord_3096 prefixEnd_3096 314021946948171967559 := by
  unfold tailWord_3096
  simp only [CollatzResearch.WordTrace]
  refine ⟨56460198395597799906571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75280264527463733208761 56460198395597799906571)
  ·
    refine ⟨84690297593396699859857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56460198395597799906571 84690297593396699859857)
    ·
      refine ⟨63517723195047524894893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84690297593396699859857 63517723195047524894893)
      ·
        refine ⟨23819146198142821835585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63517723195047524894893 23819146198142821835585)
        ·
          refine ⟨17864359648607116376689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23819146198142821835585 17864359648607116376689)
          ·
            refine ⟨13398269736455337282517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17864359648607116376689 13398269736455337282517)
            ·
              refine ⟨314021946948171967559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 13398269736455337282517 314021946948171967559)
              ·
                rfl

theorem cell19_3096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_3096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3096 prefixEnd_3096 := by exact prefixLift 3096
  have htrace : WordTrace (prefixWord ++ tailWord_3096) baseStart_3096 baseEnd_3096 := by
    simpa [prefixWord, tailWord_3096, baseEnd_3096] using wordTrace_append hprefix tailTrace_3096
  have hstable : (prefixWord ++ tailWord_3096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096).length < 2 ^ (prefixWord ++ tailWord_3096).sum := by decide
  have hdescent : baseEnd_3096 < baseStart_3096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3111 : List Nat := [1, 1, 7, 1, 1, 2, 2, 4]
def baseStart_3111 : Nat := 118140960795 + 3111 * 2 ^ 59
def prefixEnd_3111 : Nat := 4983230072969 + 3 ^ 40 * 3111 * 2
def baseEnd_3111 : Nat := 946630113328925569303

theorem tailTrace_3111 : CollatzResearch.WordTrace tailWord_3111 prefixEnd_3111 946630113328925569303 := by
  unfold tailWord_3111
  simp only [CollatzResearch.WordTrace]
  refine ⟨113467491736853161609187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75644994491235441072791 113467491736853161609187)
  ·
    refine ⟨170201237605279742413781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113467491736853161609187 170201237605279742413781)
    ·
      refine ⟨3989091506373743962823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 170201237605279742413781 3989091506373743962823)
      ·
        refine ⟨5983637259560615944235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3989091506373743962823 5983637259560615944235)
        ·
          refine ⟨8975455889340923916353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5983637259560615944235 8975455889340923916353)
          ·
            refine ⟨6731591917005692937265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8975455889340923916353 6731591917005692937265)
            ·
              refine ⟨5048693937754269702949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6731591917005692937265 5048693937754269702949)
              ·
                refine ⟨946630113328925569303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5048693937754269702949 946630113328925569303)
                ·
                  rfl

theorem cell19_3111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_3111 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3111 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3111 prefixEnd_3111 := by exact prefixLift 3111
  have htrace : WordTrace (prefixWord ++ tailWord_3111) baseStart_3111 baseEnd_3111 := by
    simpa [prefixWord, tailWord_3111, baseEnd_3111] using wordTrace_append hprefix tailTrace_3111
  have hstable : (prefixWord ++ tailWord_3111).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3111).length < 2 ^ (prefixWord ++ tailWord_3111).sum := by decide
  have hdescent : baseEnd_3111 < baseStart_3111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115 : List Nat := [1, 1, 1, 1, 2, 1, 8, 4]
def baseStart_3115 : Nat := 118140960795 + 3115 * 2 ^ 59
def prefixEnd_3115 : Nat := 4983230072969 + 3 ^ 40 * 3115 * 2
def baseEnd_3115 : Nat := 947847252658101480403

theorem tailTrace_3115 : CollatzResearch.WordTrace tailWord_3115 prefixEnd_3115 947847252658101480403 := by
  unfold tailWord_3115
  simp only [CollatzResearch.WordTrace]
  refine ⟨113613383722361844754799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75742255814907896503199 113613383722361844754799)
  ·
    refine ⟨170420075583542767132199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113613383722361844754799 170420075583542767132199)
    ·
      refine ⟨255630113375314150698299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170420075583542767132199 255630113375314150698299)
      ·
        refine ⟨383445170062971226047449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255630113375314150698299 383445170062971226047449)
        ·
          refine ⟨287583877547228419535587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383445170062971226047449 287583877547228419535587)
          ·
            refine ⟨431375816320842629303381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287583877547228419535587 431375816320842629303381)
            ·
              refine ⟨5055185347509874562149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 431375816320842629303381 5055185347509874562149)
              ·
                refine ⟨947847252658101480403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5055185347509874562149 947847252658101480403)
                ·
                  rfl

theorem cell19_3115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_3115 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3115 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3115 prefixEnd_3115 := by exact prefixLift 3115
  have htrace : WordTrace (prefixWord ++ tailWord_3115) baseStart_3115 baseEnd_3115 := by
    simpa [prefixWord, tailWord_3115, baseEnd_3115] using wordTrace_append hprefix tailTrace_3115
  have hstable : (prefixWord ++ tailWord_3115).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115).length < 2 ^ (prefixWord ++ tailWord_3115).sum := by decide
  have hdescent : baseEnd_3115 < baseStart_3115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3166 : List Nat := [4, 4, 1, 1, 1, 1, 3, 4]
def baseStart_3166 : Nat := 118140960795 + 3166 * 2 ^ 59
def prefixEnd_3166 : Nat := 4983230072969 + 3 ^ 40 * 3166 * 2
def baseEnd_3166 : Nat := 963365779105094346931

theorem tailTrace_3166 : CollatzResearch.WordTrace tailWord_3166 prefixEnd_3166 963365779105094346931 := by
  unfold tailWord_3166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14434188317199694357669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76982337691731703240901 14434188317199694357669)
  ·
    refine ⟨2706410309474942692063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14434188317199694357669 2706410309474942692063)
    ·
      refine ⟨4059615464212414038095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2706410309474942692063 4059615464212414038095)
      ·
        refine ⟨6089423196318621057143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4059615464212414038095 6089423196318621057143)
        ·
          refine ⟨9134134794477931585715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6089423196318621057143 9134134794477931585715)
          ·
            refine ⟨13701202191716897378573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9134134794477931585715 13701202191716897378573)
            ·
              refine ⟨5137950821893836516965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13701202191716897378573 5137950821893836516965)
              ·
                refine ⟨963365779105094346931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5137950821893836516965 963365779105094346931)
                ·
                  rfl

theorem cell19_3166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_3166 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3166 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3166 prefixEnd_3166 := by exact prefixLift 3166
  have htrace : WordTrace (prefixWord ++ tailWord_3166) baseStart_3166 baseEnd_3166 := by
    simpa [prefixWord, tailWord_3166, baseEnd_3166] using wordTrace_append hprefix tailTrace_3166
  have hstable : (prefixWord ++ tailWord_3166).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3166).length < 2 ^ (prefixWord ++ tailWord_3166).sum := by decide
  have hdescent : baseEnd_3166 < baseStart_3166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208 : List Nat := [2, 1, 3, 4, 2, 1, 6]
def baseStart_3208 : Nat := 118140960795 + 3208 * 2 ^ 59
def prefixEnd_3208 : Nat := 4983230072969 + 3 ^ 40 * 3208 * 2
def baseEnd_3208 : Nat := 325381914020480471161

theorem tailTrace_3208 : CollatzResearch.WordTrace tailWord_3208 prefixEnd_3208 325381914020480471161 := by
  unfold tailWord_3208
  simp only [CollatzResearch.WordTrace]
  refine ⟨58502686192719363945139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78003581590292485260185 58502686192719363945139)
  ·
    refine ⟨87754029289079045917709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58502686192719363945139 87754029289079045917709)
    ·
      refine ⟨32907760983404642219141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87754029289079045917709 32907760983404642219141)
      ·
        refine ⟨6170205184388370416089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32907760983404642219141 6170205184388370416089)
        ·
          refine ⟨4627653888291277812067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6170205184388370416089 4627653888291277812067)
          ·
            refine ⟨6941480832436916718101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4627653888291277812067 6941480832436916718101)
            ·
              refine ⟨325381914020480471161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6941480832436916718101 325381914020480471161)
              ·
                rfl

theorem cell19_3208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 6].length) (baseStart_3208 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3208 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3208 prefixEnd_3208 := by exact prefixLift 3208
  have htrace : WordTrace (prefixWord ++ tailWord_3208) baseStart_3208 baseEnd_3208 := by
    simpa [prefixWord, tailWord_3208, baseEnd_3208] using wordTrace_append hprefix tailTrace_3208
  have hstable : (prefixWord ++ tailWord_3208).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208).length < 2 ^ (prefixWord ++ tailWord_3208).sum := by decide
  have hdescent : baseEnd_3208 < baseStart_3208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210 : List Nat := [3, 1, 2, 3, 1, 1, 8]
def baseStart_3210 : Nat := 118140960795 + 3210 * 2 ^ 59
def prefixEnd_3210 : Nat := 4983230072969 + 3 ^ 40 * 3210 * 2
def baseEnd_3210 : Nat := 325584770575343123011

theorem tailTrace_3210 : CollatzResearch.WordTrace tailWord_3210 prefixEnd_3210 325584770575343123011 := by
  unfold tailWord_3210
  simp only [CollatzResearch.WordTrace]
  refine ⟨29269579594548267365771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78052212252128712975389 29269579594548267365771)
  ·
    refine ⟨43904369391822401048657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29269579594548267365771 43904369391822401048657)
    ·
      refine ⟨32928277043866800786493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43904369391822401048657 32928277043866800786493)
      ·
        refine ⟨12348103891450050294935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32928277043866800786493 12348103891450050294935)
        ·
          refine ⟨18522155837175075442403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12348103891450050294935 18522155837175075442403)
          ·
            refine ⟨27783233755762613163605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18522155837175075442403 27783233755762613163605)
            ·
              refine ⟨325584770575343123011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 27783233755762613163605 325584770575343123011)
              ·
                rfl

theorem cell19_3210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_3210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3210 prefixEnd_3210 := by exact prefixLift 3210
  have htrace : WordTrace (prefixWord ++ tailWord_3210) baseStart_3210 baseEnd_3210 := by
    simpa [prefixWord, tailWord_3210, baseEnd_3210] using wordTrace_append hprefix tailTrace_3210
  have hstable : (prefixWord ++ tailWord_3210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210).length < 2 ^ (prefixWord ++ tailWord_3210).sum := by decide
  have hdescent : baseEnd_3210 < baseStart_3210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229 : List Nat := [1, 4, 2, 1, 1, 2, 2, 6]
def baseStart_3229 : Nat := 118140960795 + 3229 * 2 ^ 59
def prefixEnd_3229 : Nat := 4983230072969 + 3 ^ 40 * 3229 * 2
def baseEnd_3229 : Nat := 982535723539614946759

theorem tailTrace_3229 : CollatzResearch.WordTrace tailWord_3229 prefixEnd_3229 982535723539614946759 := by
  unfold tailWord_3229
  simp only [CollatzResearch.WordTrace]
  refine ⟨117771305309359314404741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78514203539572876269827 117771305309359314404741)
  ·
    refine ⟨22082119745504871450889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117771305309359314404741 22082119745504871450889)
    ·
      refine ⟨16561589809128653588167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22082119745504871450889 16561589809128653588167)
      ·
        refine ⟨24842384713692980382251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16561589809128653588167 24842384713692980382251)
        ·
          refine ⟨37263577070539470573377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24842384713692980382251 37263577070539470573377)
          ·
            refine ⟨27947682802904602930033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37263577070539470573377 27947682802904602930033)
            ·
              refine ⟨20960762102178452197525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27947682802904602930033 20960762102178452197525)
              ·
                refine ⟨982535723539614946759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20960762102178452197525 982535723539614946759)
                ·
                  rfl

theorem cell19_3229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_3229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3229 prefixEnd_3229 := by exact prefixLift 3229
  have htrace : WordTrace (prefixWord ++ tailWord_3229) baseStart_3229 baseEnd_3229 := by
    simpa [prefixWord, tailWord_3229, baseEnd_3229] using wordTrace_append hprefix tailTrace_3229
  have hstable : (prefixWord ++ tailWord_3229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229).length < 2 ^ (prefixWord ++ tailWord_3229).sum := by decide
  have hdescent : baseEnd_3229 < baseStart_3229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242 : List Nat := [3, 1, 5, 1, 1, 3, 2, 3]
def baseStart_3242 : Nat := 118140960795 + 3242 * 2 ^ 59
def prefixEnd_3242 : Nat := 4983230072969 + 3 ^ 40 * 3242 * 2
def baseEnd_3242 : Nat := 986491426359436657835

theorem tailTrace_3242 : CollatzResearch.WordTrace tailWord_3242 prefixEnd_3242 986491426359436657835 := by
  unfold tailWord_3242
  simp only [CollatzResearch.WordTrace]
  refine ⟨29561363565565633656995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78830302841508356418653 29561363565565633656995)
  ·
    refine ⟨44342045348348450485493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29561363565565633656995 44342045348348450485493)
    ·
      refine ⟨4157066751407667233015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44342045348348450485493 4157066751407667233015)
      ·
        refine ⟨6235600127111500849523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4157066751407667233015 6235600127111500849523)
        ·
          refine ⟨9353400190667251274285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6235600127111500849523 9353400190667251274285)
          ·
            refine ⟨3507525071500219227857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9353400190667251274285 3507525071500219227857)
            ·
              refine ⟨2630643803625164420893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3507525071500219227857 2630643803625164420893)
              ·
                refine ⟨986491426359436657835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2630643803625164420893 986491426359436657835)
                ·
                  rfl

theorem cell19_3242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_3242 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3242 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3242 prefixEnd_3242 := by exact prefixLift 3242
  have htrace : WordTrace (prefixWord ++ tailWord_3242) baseStart_3242 baseEnd_3242 := by
    simpa [prefixWord, tailWord_3242, baseEnd_3242] using wordTrace_append hprefix tailTrace_3242
  have hstable : (prefixWord ++ tailWord_3242).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242).length < 2 ^ (prefixWord ++ tailWord_3242).sum := by decide
  have hdescent : baseEnd_3242 < baseStart_3242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265 : List Nat := [1, 2, 6, 1, 1, 1, 7]
def baseStart_3265 : Nat := 118140960795 + 3265 * 2 ^ 59
def prefixEnd_3265 : Nat := 4983230072969 + 3 ^ 40 * 3265 * 2
def baseEnd_3265 : Nat := 331163325834066048887

theorem tailTrace_3265 : CollatzResearch.WordTrace tailWord_3265 prefixEnd_3265 331163325834066048887 := by
  unfold tailWord_3265
  simp only [CollatzResearch.WordTrace]
  refine ⟨119084333178937462715249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79389555452624975143499 119084333178937462715249)
  ·
    refine ⟨89313249884203097036437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119084333178937462715249 89313249884203097036437)
    ·
      refine ⟨4186558588322020173583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89313249884203097036437 4186558588322020173583)
      ·
        refine ⟨6279837882483030260375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4186558588322020173583 6279837882483030260375)
        ·
          refine ⟨9419756823724545390563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6279837882483030260375 9419756823724545390563)
          ·
            refine ⟨14129635235586818085845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9419756823724545390563 14129635235586818085845)
            ·
              refine ⟨331163325834066048887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14129635235586818085845 331163325834066048887)
              ·
                rfl

theorem cell19_3265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 7].length) (baseStart_3265 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3265 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3265 prefixEnd_3265 := by exact prefixLift 3265
  have htrace : WordTrace (prefixWord ++ tailWord_3265) baseStart_3265 baseEnd_3265 := by
    simpa [prefixWord, tailWord_3265, baseEnd_3265] using wordTrace_append hprefix tailTrace_3265
  have hstable : (prefixWord ++ tailWord_3265).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265).length < 2 ^ (prefixWord ++ tailWord_3265).sum := by decide
  have hdescent : baseEnd_3265 < baseStart_3265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324 : List Nat := [2, 2, 2, 1, 5, 7]
def baseStart_3324 : Nat := 118140960795 + 3324 * 2 ^ 59
def prefixEnd_3324 : Nat := 4983230072969 + 3 ^ 40 * 3324 * 2
def baseEnd_3324 : Nat := 112382531400838092821

theorem tailTrace_3324 : CollatzResearch.WordTrace tailWord_3324 prefixEnd_3324 112382531400838092821 := by
  unfold tailWord_3324
  simp only [CollatzResearch.WordTrace]
  refine ⟨60618119982595269556513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80824159976793692742017 60618119982595269556513)
  ·
    refine ⟨45463589986946452167385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60618119982595269556513 45463589986946452167385)
    ·
      refine ⟨34097692490209839125539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45463589986946452167385 34097692490209839125539)
      ·
        refine ⟨51146538735314758688309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34097692490209839125539 51146538735314758688309)
        ·
          refine ⟨4794988006435758627029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51146538735314758688309 4794988006435758627029)
          ·
            refine ⟨112382531400838092821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4794988006435758627029 112382531400838092821)
            ·
              rfl

theorem cell19_3324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 7].length) (baseStart_3324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3324 prefixEnd_3324 := by exact prefixLift 3324
  have htrace : WordTrace (prefixWord ++ tailWord_3324) baseStart_3324 baseEnd_3324 := by
    simpa [prefixWord, tailWord_3324, baseEnd_3324] using wordTrace_append hprefix tailTrace_3324
  have hstable : (prefixWord ++ tailWord_3324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324).length < 2 ^ (prefixWord ++ tailWord_3324).sum := by decide
  have hdescent : baseEnd_3324 < baseStart_3324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381 : List Nat := [1, 3, 3, 1, 2, 3, 6]
def baseStart_3381 : Nat := 118140960795 + 3381 * 2 ^ 59
def prefixEnd_3381 : Nat := 4983230072969 + 3 ^ 40 * 3381 * 2
def baseEnd_3381 : Nat := 342929006016099856189

theorem tailTrace_3381 : CollatzResearch.WordTrace tailWord_3381 prefixEnd_3381 342929006016099856189 := by
  unfold tailWord_3381
  simp only [CollatzResearch.WordTrace]
  refine ⟨123315200758689273937997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82210133839126182625331 123315200758689273937997)
  ·
    refine ⟨46243200284508477726749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123315200758689273937997 46243200284508477726749)
    ·
      refine ⟨17341200106690679147531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46243200284508477726749 17341200106690679147531)
      ·
        refine ⟨26011800160036018721297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17341200106690679147531 26011800160036018721297)
        ·
          refine ⟨19508850120027014040973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26011800160036018721297 19508850120027014040973)
          ·
            refine ⟨7315818795010130265365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19508850120027014040973 7315818795010130265365)
            ·
              refine ⟨342929006016099856189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7315818795010130265365 342929006016099856189)
              ·
                rfl

theorem cell19_3381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 6].length) (baseStart_3381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3381 prefixEnd_3381 := by exact prefixLift 3381
  have htrace : WordTrace (prefixWord ++ tailWord_3381) baseStart_3381 baseEnd_3381 := by
    simpa [prefixWord, tailWord_3381, baseEnd_3381] using wordTrace_append hprefix tailTrace_3381
  have hstable : (prefixWord ++ tailWord_3381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381).length < 2 ^ (prefixWord ++ tailWord_3381).sum := by decide
  have hdescent : baseEnd_3381 < baseStart_3381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434 : List Nat := [3, 1, 3, 3, 3, 1, 5]
def baseStart_3434 : Nat := 118140960795 + 3434 * 2 ^ 59
def prefixEnd_3434 : Nat := 4983230072969 + 3 ^ 40 * 3434 * 2
def baseEnd_3434 : Nat := 348304704719960130215

theorem tailTrace_3434 : CollatzResearch.WordTrace tailWord_3434 prefixEnd_3434 348304704719960130215 := by
  unfold tailWord_3434
  simp only [CollatzResearch.WordTrace]
  refine ⟨31312067391669831404339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83498846377786217078237 31312067391669831404339)
  ·
    refine ⟨46968101087504747106509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31312067391669831404339 46968101087504747106509)
    ·
      refine ⟨17613037907814280164941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46968101087504747106509 17613037907814280164941)
      ·
        refine ⟨6604889215430355061853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17613037907814280164941 6604889215430355061853)
        ·
          refine ⟨2476833455786383148195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6604889215430355061853 2476833455786383148195)
          ·
            refine ⟨3715250183679574722293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476833455786383148195 3715250183679574722293)
            ·
              refine ⟨348304704719960130215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3715250183679574722293 348304704719960130215)
              ·
                rfl

theorem cell19_3434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 5].length) (baseStart_3434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3434 prefixEnd_3434 := by exact prefixLift 3434
  have htrace : WordTrace (prefixWord ++ tailWord_3434) baseStart_3434 baseEnd_3434 := by
    simpa [prefixWord, tailWord_3434, baseEnd_3434] using wordTrace_append hprefix tailTrace_3434
  have hstable : (prefixWord ++ tailWord_3434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434).length < 2 ^ (prefixWord ++ tailWord_3434).sum := by decide
  have hdescent : baseEnd_3434 < baseStart_3434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535 : List Nat := [1, 1, 2, 1, 1, 4, 2, 7]
def baseStart_3535 : Nat := 118140960795 + 3535 * 2 ^ 59
def prefixEnd_3535 : Nat := 4983230072969 + 3 ^ 40 * 3535 * 2
def baseEnd_3535 : Nat := 1075646882221572145925

theorem tailTrace_3535 : CollatzResearch.WordTrace tailWord_3535 prefixEnd_3535 1075646882221572145925 := by
  unfold tailWord_3535
  simp only [CollatzResearch.WordTrace]
  refine ⟨128932042200773575044059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85954694800515716696039 128932042200773575044059)
  ·
    refine ⟨193398063301160362566089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128932042200773575044059 193398063301160362566089)
    ·
      refine ⟨145048547475870271924567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193398063301160362566089 145048547475870271924567)
      ·
        refine ⟨217572821213805407886851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145048547475870271924567 217572821213805407886851)
        ·
          refine ⟨326359231820708111830277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217572821213805407886851 326359231820708111830277)
          ·
            refine ⟨61192355966382770968177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326359231820708111830277 61192355966382770968177)
            ·
              refine ⟨45894266974787078226133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61192355966382770968177 45894266974787078226133)
              ·
                refine ⟨1075646882221572145925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45894266974787078226133 1075646882221572145925)
                ·
                  rfl

theorem cell19_3535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_3535 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3535 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3535 prefixEnd_3535 := by exact prefixLift 3535
  have htrace : WordTrace (prefixWord ++ tailWord_3535) baseStart_3535 baseEnd_3535 := by
    simpa [prefixWord, tailWord_3535, baseEnd_3535] using wordTrace_append hprefix tailTrace_3535
  have hstable : (prefixWord ++ tailWord_3535).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535).length < 2 ^ (prefixWord ++ tailWord_3535).sum := by decide
  have hdescent : baseEnd_3535 < baseStart_3535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582 : List Nat := [4, 2, 2, 3, 2, 1, 2, 3]
def baseStart_3582 : Nat := 118140960795 + 3582 * 2 ^ 59
def prefixEnd_3582 : Nat := 4983230072969 + 3 ^ 40 * 3582 * 2
def baseEnd_3582 : Nat := 1089948269339389101353

theorem tailTrace_3582 : CollatzResearch.WordTrace tailWord_3582 prefixEnd_3582 1089948269339389101353 := by
  unfold tailWord_3582
  simp only [CollatzResearch.WordTrace]
  refine ⟨16330784128812575250625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87097515353667068003333 16330784128812575250625)
  ·
    refine ⟨12248088096609431437969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16330784128812575250625 12248088096609431437969)
    ·
      refine ⟨9186066072457073578477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12248088096609431437969 9186066072457073578477)
      ·
        refine ⟨3444774777171402591929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9186066072457073578477 3444774777171402591929)
        ·
          refine ⟨2583581082878551943947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3444774777171402591929 2583581082878551943947)
          ·
            refine ⟨3875371624317827915921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583581082878551943947 3875371624317827915921)
            ·
              refine ⟨2906528718238370936941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3875371624317827915921 2906528718238370936941)
              ·
                refine ⟨1089948269339389101353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2906528718238370936941 1089948269339389101353)
                ·
                  rfl

theorem cell19_3582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_3582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3582 prefixEnd_3582 := by exact prefixLift 3582
  have htrace : WordTrace (prefixWord ++ tailWord_3582) baseStart_3582 baseEnd_3582 := by
    simpa [prefixWord, tailWord_3582, baseEnd_3582] using wordTrace_append hprefix tailTrace_3582
  have hstable : (prefixWord ++ tailWord_3582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582).length < 2 ^ (prefixWord ++ tailWord_3582).sum := by decide
  have hdescent : baseEnd_3582 < baseStart_3582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586 : List Nat := [3, 4, 1, 2, 1, 1, 4, 3]
def baseStart_3586 : Nat := 118140960795 + 3586 * 2 ^ 59
def prefixEnd_3586 : Nat := 4983230072969 + 3 ^ 40 * 3586 * 2
def baseEnd_3586 : Nat := 1091165408668565012453

theorem tailTrace_3586 : CollatzResearch.WordTrace tailWord_3586 prefixEnd_3586 1091165408668565012453 := by
  unfold tailWord_3586
  simp only [CollatzResearch.WordTrace]
  refine ⟨32698041254002321287653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87194776677339523433741 32698041254002321287653)
  ·
    refine ⟨6130882735125435241435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32698041254002321287653 6130882735125435241435)
    ·
      refine ⟨9196324102688152862153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6130882735125435241435 9196324102688152862153)
      ·
        refine ⟨6897243077016114646615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9196324102688152862153 6897243077016114646615)
        ·
          refine ⟨10345864615524171969923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6897243077016114646615 10345864615524171969923)
          ·
            refine ⟨15518796923286257954885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10345864615524171969923 15518796923286257954885)
            ·
              refine ⟨2909774423116173366541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15518796923286257954885 2909774423116173366541)
              ·
                refine ⟨1091165408668565012453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2909774423116173366541 1091165408668565012453)
                ·
                  rfl

theorem cell19_3586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_3586 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3586 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3586 prefixEnd_3586 := by exact prefixLift 3586
  have htrace : WordTrace (prefixWord ++ tailWord_3586) baseStart_3586 baseEnd_3586 := by
    simpa [prefixWord, tailWord_3586, baseEnd_3586] using wordTrace_append hprefix tailTrace_3586
  have hstable : (prefixWord ++ tailWord_3586).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586).length < 2 ^ (prefixWord ++ tailWord_3586).sum := by decide
  have hdescent : baseEnd_3586 < baseStart_3586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588 : List Nat := [2, 3, 2, 3, 2, 1, 1, 5]
def baseStart_3588 : Nat := 118140960795 + 3588 * 2 ^ 59
def prefixEnd_3588 : Nat := 4983230072969 + 3 ^ 40 * 3588 * 2
def baseEnd_3588 : Nat := 1091773978333152968003

theorem tailTrace_3588 : CollatzResearch.WordTrace tailWord_3588 prefixEnd_3588 1091773978333152968003 := by
  unfold tailWord_3588
  simp only [CollatzResearch.WordTrace]
  refine ⟨65432555504381813361709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87243407339175751148945 65432555504381813361709)
  ·
    refine ⟨24537208314143180010641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65432555504381813361709 24537208314143180010641)
    ·
      refine ⟨18402906235607385007981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24537208314143180010641 18402906235607385007981)
      ·
        refine ⟨6901089838352769377993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18402906235607385007981 6901089838352769377993)
        ·
          refine ⟨5175817378764577033495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6901089838352769377993 5175817378764577033495)
          ·
            refine ⟨7763726068146865550243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5175817378764577033495 7763726068146865550243)
            ·
              refine ⟨11645589102220298325365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7763726068146865550243 11645589102220298325365)
              ·
                refine ⟨1091773978333152968003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11645589102220298325365 1091773978333152968003)
                ·
                  rfl

theorem cell19_3588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_3588 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3588 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3588 prefixEnd_3588 := by exact prefixLift 3588
  have htrace : WordTrace (prefixWord ++ tailWord_3588) baseStart_3588 baseEnd_3588 := by
    simpa [prefixWord, tailWord_3588, baseEnd_3588] using wordTrace_append hprefix tailTrace_3588
  have hstable : (prefixWord ++ tailWord_3588).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588).length < 2 ^ (prefixWord ++ tailWord_3588).sum := by decide
  have hdescent : baseEnd_3588 < baseStart_3588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685 : List Nat := [1, 3, 1, 3, 3, 1, 3, 4]
def baseStart_3685 : Nat := 118140960795 + 3685 * 2 ^ 59
def prefixEnd_3685 : Nat := 4983230072969 + 3 ^ 40 * 3685 * 2
def baseEnd_3685 : Nat := 1121289607065668812183

theorem tailTrace_3685 : CollatzResearch.WordTrace tailWord_3685 prefixEnd_3685 1121289607065668812183 := by
  unfold tailWord_3685
  simp only [CollatzResearch.WordTrace]
  refine ⟨134402991657349193004509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89601994438232795336339 134402991657349193004509)
  ·
    refine ⟨50401121871505947376691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134402991657349193004509 50401121871505947376691)
    ·
      refine ⟨75601682807258921065037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50401121871505947376691 75601682807258921065037)
      ·
        refine ⟨28350631052722095399389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75601682807258921065037 28350631052722095399389)
        ·
          refine ⟨10631486644770785774771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28350631052722095399389 10631486644770785774771)
          ·
            refine ⟨15947229967156178662157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10631486644770785774771 15947229967156178662157)
            ·
              refine ⟨5980211237683566998309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15947229967156178662157 5980211237683566998309)
              ·
                refine ⟨1121289607065668812183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5980211237683566998309 1121289607065668812183)
                ·
                  rfl

theorem cell19_3685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_3685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3685 prefixEnd_3685 := by exact prefixLift 3685
  have htrace : WordTrace (prefixWord ++ tailWord_3685) baseStart_3685 baseEnd_3685 := by
    simpa [prefixWord, tailWord_3685, baseEnd_3685] using wordTrace_append hprefix tailTrace_3685
  have hstable : (prefixWord ++ tailWord_3685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685).length < 2 ^ (prefixWord ++ tailWord_3685).sum := by decide
  have hdescent : baseEnd_3685 < baseStart_3685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763 : List Nat := [1, 1, 1, 2, 3, 3, 3, 5]
def baseStart_3763 : Nat := 118140960795 + 3763 * 2 ^ 59
def prefixEnd_3763 : Nat := 4983230072969 + 3 ^ 40 * 3763 * 2
def baseEnd_3763 : Nat := 1145023823984599078637

theorem tailTrace_3763 : CollatzResearch.WordTrace tailWord_3763 prefixEnd_3763 1145023823984599078637 := by
  unfold tailWord_3763
  simp only [CollatzResearch.WordTrace]
  refine ⟨137247885374768514343943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91498590249845676229295 137247885374768514343943)
  ·
    refine ⟨205871828062152771515915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137247885374768514343943 205871828062152771515915)
    ·
      refine ⟨308807742093229157273873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205871828062152771515915 308807742093229157273873)
      ·
        refine ⟨231605806569921867955405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308807742093229157273873 231605806569921867955405)
        ·
          refine ⟨86852177463720700483277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231605806569921867955405 86852177463720700483277)
          ·
            refine ⟨32569566548895262681229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86852177463720700483277 32569566548895262681229)
            ·
              refine ⟨12213587455835723505461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32569566548895262681229 12213587455835723505461)
              ·
                refine ⟨1145023823984599078637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12213587455835723505461 1145023823984599078637)
                ·
                  rfl

theorem cell19_3763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_3763 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3763 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3763 prefixEnd_3763 := by exact prefixLift 3763
  have htrace : WordTrace (prefixWord ++ tailWord_3763) baseStart_3763 baseEnd_3763 := by
    simpa [prefixWord, tailWord_3763, baseEnd_3763] using wordTrace_append hprefix tailTrace_3763
  have hstable : (prefixWord ++ tailWord_3763).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763).length < 2 ^ (prefixWord ++ tailWord_3763).sum := by decide
  have hdescent : baseEnd_3763 < baseStart_3763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801 : List Nat := [1, 2, 1, 2, 3, 3, 1, 6]
def baseStart_3801 : Nat := 118140960795 + 3801 * 2 ^ 59
def prefixEnd_3801 : Nat := 4983230072969 + 3 ^ 40 * 3801 * 2
def baseEnd_3801 : Nat := 1156586647611770234089

theorem tailTrace_3801 : CollatzResearch.WordTrace tailWord_3801 prefixEnd_3801 1156586647611770234089 := by
  unfold tailWord_3801
  simp only [CollatzResearch.WordTrace]
  refine ⟨138633859237101004227257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92422572824734002818171 138633859237101004227257)
  ·
    refine ⟨103975394427825753170443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138633859237101004227257 103975394427825753170443)
    ·
      refine ⟨155963091641738629755665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103975394427825753170443 155963091641738629755665)
      ·
        refine ⟨116972318731303972316749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155963091641738629755665 116972318731303972316749)
        ·
          refine ⟨43864619524238989618781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116972318731303972316749 43864619524238989618781)
          ·
            refine ⟨16449232321589621107043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43864619524238989618781 16449232321589621107043)
            ·
              refine ⟨24673848482384431660565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16449232321589621107043 24673848482384431660565)
              ·
                refine ⟨1156586647611770234089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24673848482384431660565 1156586647611770234089)
                ·
                  rfl

theorem cell19_3801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_3801 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3801 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3801 prefixEnd_3801 := by exact prefixLift 3801
  have htrace : WordTrace (prefixWord ++ tailWord_3801) baseStart_3801 baseEnd_3801 := by
    simpa [prefixWord, tailWord_3801, baseEnd_3801] using wordTrace_append hprefix tailTrace_3801
  have hstable : (prefixWord ++ tailWord_3801).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801).length < 2 ^ (prefixWord ++ tailWord_3801).sum := by decide
  have hdescent : baseEnd_3801 < baseStart_3801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820 : List Nat := [2, 2, 1, 1, 2, 2, 4, 5]
def baseStart_3820 : Nat := 118140960795 + 3820 * 2 ^ 59
def prefixEnd_3820 : Nat := 4983230072969 + 3 ^ 40 * 3820 * 2
def baseEnd_3820 : Nat := 1162368059425355811815

theorem tailTrace_3820 : CollatzResearch.WordTrace tailWord_3820 prefixEnd_3820 1162368059425355811815 := by
  unfold tailWord_3820
  simp only [CollatzResearch.WordTrace]
  refine ⟨69663423084133624584457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92884564112178166112609 69663423084133624584457)
  ·
    refine ⟨52247567313100218438343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69663423084133624584457 52247567313100218438343)
    ·
      refine ⟨78371350969650327657515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52247567313100218438343 78371350969650327657515)
      ·
        refine ⟨117557026454475491486273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78371350969650327657515 117557026454475491486273)
        ·
          refine ⟨88167769840856618614705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117557026454475491486273 88167769840856618614705)
          ·
            refine ⟨66125827380642463961029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88167769840856618614705 66125827380642463961029)
            ·
              refine ⟨12398592633870461992693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66125827380642463961029 12398592633870461992693)
              ·
                refine ⟨1162368059425355811815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12398592633870461992693 1162368059425355811815)
                ·
                  rfl

theorem cell19_3820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_3820 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3820 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3820 prefixEnd_3820 := by exact prefixLift 3820
  have htrace : WordTrace (prefixWord ++ tailWord_3820) baseStart_3820 baseEnd_3820 := by
    simpa [prefixWord, tailWord_3820, baseEnd_3820] using wordTrace_append hprefix tailTrace_3820
  have hstable : (prefixWord ++ tailWord_3820).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820).length < 2 ^ (prefixWord ++ tailWord_3820).sum := by decide
  have hdescent : baseEnd_3820 < baseStart_3820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846 : List Nat := [6, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3846 : Nat := 118140960795 + 3846 * 2 ^ 59
def prefixEnd_3846 : Nat := 4983230072969 + 3 ^ 40 * 3846 * 2
def baseEnd_3846 : Nat := 1170279465064999233967

theorem tailTrace_3846 : CollatzResearch.WordTrace tailWord_3846 prefixEnd_3846 1170279465064999233967 := by
  unfold tailWord_3846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383598252314802800481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93516762716049126410261 4383598252314802800481)
  ·
    refine ⟨3287698689236102100361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4383598252314802800481 3287698689236102100361)
    ·
      refine ⟨2465774016927076575271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3287698689236102100361 2465774016927076575271)
      ·
        refine ⟨3698661025390614862907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465774016927076575271 3698661025390614862907)
        ·
          refine ⟨5547991538085922294361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3698661025390614862907 5547991538085922294361)
          ·
            refine ⟨4160993653564441720771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5547991538085922294361 4160993653564441720771)
            ·
              refine ⟨6241490480346662581157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4160993653564441720771 6241490480346662581157)
              ·
                refine ⟨1170279465064999233967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6241490480346662581157 1170279465064999233967)
                ·
                  rfl

theorem cell19_3846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3846 prefixEnd_3846 := by exact prefixLift 3846
  have htrace : WordTrace (prefixWord ++ tailWord_3846) baseStart_3846 baseEnd_3846 := by
    simpa [prefixWord, tailWord_3846, baseEnd_3846] using wordTrace_append hprefix tailTrace_3846
  have hstable : (prefixWord ++ tailWord_3846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846).length < 2 ^ (prefixWord ++ tailWord_3846).sum := by decide
  have hdescent : baseEnd_3846 < baseStart_3846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896 : List Nat := [2, 1, 2, 1, 3, 4, 6]
def baseStart_3896 : Nat := 118140960795 + 3896 * 2 ^ 59
def prefixEnd_3896 : Nat := 4983230072969 + 3 ^ 40 * 3896 * 2
def baseEnd_3896 : Nat := 395164568893232707573

theorem tailTrace_3896 : CollatzResearch.WordTrace tailWord_3896 prefixEnd_3896 395164568893232707573 := by
  unfold tailWord_3896
  simp only [CollatzResearch.WordTrace]
  refine ⟨71049396946466114467771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94732529261954819290361 71049396946466114467771)
  ·
    refine ⟨106574095419699171701657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71049396946466114467771 106574095419699171701657)
    ·
      refine ⟨79930571564774378776243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106574095419699171701657 79930571564774378776243)
      ·
        refine ⟨119895857347161568164365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79930571564774378776243 119895857347161568164365)
        ·
          refine ⟨44960946505185588061637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119895857347161568164365 44960946505185588061637)
          ·
            refine ⟨8430177469722297761557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44960946505185588061637 8430177469722297761557)
            ·
              refine ⟨395164568893232707573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8430177469722297761557 395164568893232707573)
              ·
                rfl

theorem cell19_3896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 6].length) (baseStart_3896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3896 prefixEnd_3896 := by exact prefixLift 3896
  have htrace : WordTrace (prefixWord ++ tailWord_3896) baseStart_3896 baseEnd_3896 := by
    simpa [prefixWord, tailWord_3896, baseEnd_3896] using wordTrace_append hprefix tailTrace_3896
  have hstable : (prefixWord ++ tailWord_3896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896).length < 2 ^ (prefixWord ++ tailWord_3896).sum := by decide
  have hdescent : baseEnd_3896 < baseStart_3896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972 : List Nat := [2, 3, 2, 1, 1, 1, 3, 6]
def baseStart_3972 : Nat := 118140960795 + 3972 * 2 ^ 59
def prefixEnd_3972 : Nat := 4983230072969 + 3 ^ 40 * 3972 * 2
def baseEnd_3972 : Nat := 1208619353934040433623

theorem tailTrace_3972 : CollatzResearch.WordTrace tailWord_3972 prefixEnd_3972 1208619353934040433623 := by
  unfold tailWord_3972
  simp only [CollatzResearch.WordTrace]
  refine ⟨72435370808798604351085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96580494411731472468113 72435370808798604351085)
  ·
    refine ⟨27163264053299476631657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72435370808798604351085 27163264053299476631657)
    ·
      refine ⟨20372448039974607473743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27163264053299476631657 20372448039974607473743)
      ·
        refine ⟨30558672059961911210615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20372448039974607473743 30558672059961911210615)
        ·
          refine ⟨45838008089942866815923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30558672059961911210615 45838008089942866815923)
          ·
            refine ⟨68757012134914300223885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45838008089942866815923 68757012134914300223885)
            ·
              refine ⟨25783879550592862583957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68757012134914300223885 25783879550592862583957)
              ·
                refine ⟨1208619353934040433623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25783879550592862583957 1208619353934040433623)
                ·
                  rfl

theorem cell19_3972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_3972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3972 prefixEnd_3972 := by exact prefixLift 3972
  have htrace : WordTrace (prefixWord ++ tailWord_3972) baseStart_3972 baseEnd_3972 := by
    simpa [prefixWord, tailWord_3972, baseEnd_3972] using wordTrace_append hprefix tailTrace_3972
  have hstable : (prefixWord ++ tailWord_3972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972).length < 2 ^ (prefixWord ++ tailWord_3972).sum := by decide
  have hdescent : baseEnd_3972 < baseStart_3972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991 : List Nat := [1, 1, 3, 3, 1, 3, 2, 5]
def baseStart_3991 : Nat := 118140960795 + 3991 * 2 ^ 59
def prefixEnd_3991 : Nat := 4983230072969 + 3 ^ 40 * 3991 * 2
def baseEnd_3991 : Nat := 1214400765747626011349

theorem tailTrace_3991 : CollatzResearch.WordTrace tailWord_3991 prefixEnd_3991 1214400765747626011349 := by
  unfold tailWord_3991
  simp only [CollatzResearch.WordTrace]
  refine ⟨145563728548763453643827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97042485699175635762551 145563728548763453643827)
  ·
    refine ⟨218345592823145180465741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145563728548763453643827 218345592823145180465741)
    ·
      refine ⟨81879597308679442674653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218345592823145180465741 81879597308679442674653)
      ·
        refine ⟨30704848990754791002995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81879597308679442674653 30704848990754791002995)
        ·
          refine ⟨46057273486132186504493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30704848990754791002995 46057273486132186504493)
          ·
            refine ⟨17271477557299569939185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46057273486132186504493 17271477557299569939185)
            ·
              refine ⟨12953608167974677454389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17271477557299569939185 12953608167974677454389)
              ·
                refine ⟨1214400765747626011349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12953608167974677454389 1214400765747626011349)
                ·
                  rfl

theorem cell19_3991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_3991 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_3991 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_3991 prefixEnd_3991 := by exact prefixLift 3991
  have htrace : WordTrace (prefixWord ++ tailWord_3991) baseStart_3991 baseEnd_3991 := by
    simpa [prefixWord, tailWord_3991, baseEnd_3991] using wordTrace_append hprefix tailTrace_3991
  have hstable : (prefixWord ++ tailWord_3991).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991).length < 2 ^ (prefixWord ++ tailWord_3991).sum := by decide
  have hdescent : baseEnd_3991 < baseStart_3991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4008 : List Nat := [2, 1, 6, 2, 8]
def baseStart_4008 : Nat := 118140960795 + 4008 * 2 ^ 59
def prefixEnd_4008 : Nat := 4983230072969 + 3 ^ 40 * 4008 * 2
def baseEnd_4008 : Nat := 45169392885060134575

theorem tailTrace_4008 : CollatzResearch.WordTrace tailWord_4008 prefixEnd_4008 45169392885060134575 := by
  unfold tailWord_4008
  simp only [CollatzResearch.WordTrace]
  refine ⟨73091884743587678506339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97455846324783571341785 73091884743587678506339)
  ·
    refine ⟨109637827115381517759509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73091884743587678506339 109637827115381517759509)
    ·
      refine ⟨5139273146033508644977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109637827115381517759509 5139273146033508644977)
      ·
        refine ⟨3854454859525131483733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5139273146033508644977 3854454859525131483733)
        ·
          refine ⟨45169392885060134575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 3854454859525131483733 45169392885060134575)
          ·
            rfl

theorem cell19_4008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 8].length) (baseStart_4008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4008 prefixEnd_4008 := by exact prefixLift 4008
  have htrace : WordTrace (prefixWord ++ tailWord_4008) baseStart_4008 baseEnd_4008 := by
    simpa [prefixWord, tailWord_4008, baseEnd_4008] using wordTrace_append hprefix tailTrace_4008
  have hstable : (prefixWord ++ tailWord_4008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4008).length < 2 ^ (prefixWord ++ tailWord_4008).sum := by decide
  have hdescent : baseEnd_4008 < baseStart_4008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046 : List Nat := [4, 1, 1, 1, 2, 2, 5, 3]
def baseStart_4046 : Nat := 118140960795 + 4046 * 2 ^ 59
def prefixEnd_4046 : Nat := 4983230072969 + 3 ^ 40 * 4046 * 2
def baseEnd_4046 : Nat := 1231136431523794788977

theorem tailTrace_4046 : CollatzResearch.WordTrace tailWord_4046 prefixEnd_4046 1231136431523794788977 := by
  unfold tailWord_4046
  simp only [CollatzResearch.WordTrace]
  refine ⟨18446217918688480861999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98379828899671897930661 18446217918688480861999)
  ·
    refine ⟨27669326878032721292999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18446217918688480861999 27669326878032721292999)
    ·
      refine ⟨41503990317049081939499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27669326878032721292999 41503990317049081939499)
      ·
        refine ⟨62255985475573622909249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41503990317049081939499 62255985475573622909249)
        ·
          refine ⟨46691989106680217181937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62255985475573622909249 46691989106680217181937)
          ·
            refine ⟨35018991830010162886453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46691989106680217181937 35018991830010162886453)
            ·
              refine ⟨3283030484063452770605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35018991830010162886453 3283030484063452770605)
              ·
                refine ⟨1231136431523794788977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3283030484063452770605 1231136431523794788977)
                ·
                  rfl

theorem cell19_4046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_4046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4046 prefixEnd_4046 := by exact prefixLift 4046
  have htrace : WordTrace (prefixWord ++ tailWord_4046) baseStart_4046 baseEnd_4046 := by
    simpa [prefixWord, tailWord_4046, baseEnd_4046] using wordTrace_append hprefix tailTrace_4046
  have hstable : (prefixWord ++ tailWord_4046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046).length < 2 ^ (prefixWord ++ tailWord_4046).sum := by decide
  have hdescent : baseEnd_4046 < baseStart_4046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067 : List Nat := [1, 1, 1, 6, 1, 3, 6]
def baseStart_4067 : Nat := 118140960795 + 4067 * 2 ^ 59
def prefixEnd_4067 : Nat := 4983230072969 + 3 ^ 40 * 4067 * 2
def baseEnd_4067 : Nat := 412508804333989440751

theorem tailTrace_4067 : CollatzResearch.WordTrace tailWord_4067 prefixEnd_4067 412508804333989440751 := by
  unfold tailWord_4067
  simp only [CollatzResearch.WordTrace]
  refine ⟨148335676273428433410455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98890450848952288940303 148335676273428433410455)
  ·
    refine ⟨222503514410142650115683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148335676273428433410455 222503514410142650115683)
    ·
      refine ⟨333755271615213975173525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222503514410142650115683 333755271615213975173525)
      ·
        refine ⟨15644778356963155086259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 333755271615213975173525 15644778356963155086259)
        ·
          refine ⟨23467167535444732629389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15644778356963155086259 23467167535444732629389)
          ·
            refine ⟨8800187825791774736021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23467167535444732629389 8800187825791774736021)
            ·
              refine ⟨412508804333989440751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8800187825791774736021 412508804333989440751)
              ·
                rfl

theorem cell19_4067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 6].length) (baseStart_4067 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4067 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4067 prefixEnd_4067 := by exact prefixLift 4067
  have htrace : WordTrace (prefixWord ++ tailWord_4067) baseStart_4067 baseEnd_4067 := by
    simpa [prefixWord, tailWord_4067, baseEnd_4067] using wordTrace_append hprefix tailTrace_4067
  have hstable : (prefixWord ++ tailWord_4067).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067).length < 2 ^ (prefixWord ++ tailWord_4067).sum := by decide
  have hdescent : baseEnd_4067 < baseStart_4067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103 : List Nat := [1, 1, 4, 3, 1, 2, 4, 3]
def baseStart_4103 : Nat := 118140960795 + 4103 * 2 ^ 59
def prefixEnd_4103 : Nat := 4983230072969 + 3 ^ 40 * 4103 * 2
def baseEnd_4103 : Nat := 1248480666964551522155

theorem tailTrace_4103 : CollatzResearch.WordTrace tailWord_4103 prefixEnd_4103 1248480666964551522155 := by
  unfold tailWord_4103
  simp only [CollatzResearch.WordTrace]
  refine ⟨149648704143006581720963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99765802762004387813975 149648704143006581720963)
  ·
    refine ⟨224473056214509872581445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149648704143006581720963 224473056214509872581445)
    ·
      refine ⟨42088698040220601109021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224473056214509872581445 42088698040220601109021)
      ·
        refine ⟨15783261765082725415883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42088698040220601109021 15783261765082725415883)
        ·
          refine ⟨23674892647624088123825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15783261765082725415883 23674892647624088123825)
          ·
            refine ⟨17756169485718066092869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23674892647624088123825 17756169485718066092869)
            ·
              refine ⟨3329281778572137392413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17756169485718066092869 3329281778572137392413)
              ·
                refine ⟨1248480666964551522155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3329281778572137392413 1248480666964551522155)
                ·
                  rfl

theorem cell19_4103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 3].length) (baseStart_4103 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4103 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4103 prefixEnd_4103 := by exact prefixLift 4103
  have htrace : WordTrace (prefixWord ++ tailWord_4103) baseStart_4103 baseEnd_4103 := by
    simpa [prefixWord, tailWord_4103, baseEnd_4103] using wordTrace_append hprefix tailTrace_4103
  have hstable : (prefixWord ++ tailWord_4103).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103).length < 2 ^ (prefixWord ++ tailWord_4103).sum := by decide
  have hdescent : baseEnd_4103 < baseStart_4103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4124 : List Nat := [2, 2, 3, 1, 3, 1, 7]
def baseStart_4124 : Nat := 118140960795 + 4124 * 2 ^ 59
def prefixEnd_4124 : Nat := 4983230072969 + 3 ^ 40 * 4124 * 2
def baseEnd_4124 : Nat := 418290216147575018477

theorem tailTrace_4124 : CollatzResearch.WordTrace tailWord_4124 prefixEnd_4124 418290216147575018477 := by
  unfold tailWord_4124
  simp only [CollatzResearch.WordTrace]
  refine ⟨75207318533463584117713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100276424711284778823617 75207318533463584117713)
  ·
    refine ⟨56405488900097688088285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75207318533463584117713 56405488900097688088285)
    ·
      refine ⟨21152058337536633033107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56405488900097688088285 21152058337536633033107)
      ·
        refine ⟨31728087506304949549661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21152058337536633033107 31728087506304949549661)
        ·
          refine ⟨11898032814864356081123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31728087506304949549661 11898032814864356081123)
          ·
            refine ⟨17847049222296534121685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11898032814864356081123 17847049222296534121685)
            ·
              refine ⟨418290216147575018477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17847049222296534121685 418290216147575018477)
              ·
                rfl

theorem cell19_4124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 7].length) (baseStart_4124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4124 prefixEnd_4124 := by exact prefixLift 4124
  have htrace : WordTrace (prefixWord ++ tailWord_4124) baseStart_4124 baseEnd_4124 := by
    simpa [prefixWord, tailWord_4124, baseEnd_4124] using wordTrace_append hprefix tailTrace_4124
  have hstable : (prefixWord ++ tailWord_4124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4124).length < 2 ^ (prefixWord ++ tailWord_4124).sum := by decide
  have hdescent : baseEnd_4124 < baseStart_4124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194 : List Nat := [3, 3, 2, 2, 3, 1, 1, 4]
def baseStart_4194 : Nat := 118140960795 + 4194 * 2 ^ 59
def prefixEnd_4194 : Nat := 4983230072969 + 3 ^ 40 * 4194 * 2
def baseEnd_4194 : Nat := 1276170586703303499685

theorem tailTrace_4194 : CollatzResearch.WordTrace tailWord_4194 prefixEnd_4194 1276170586703303499685 := by
  unfold tailWord_4194
  simp only [CollatzResearch.WordTrace]
  refine ⟨38241936703332280820909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101978497875552748855757 38241936703332280820909)
  ·
    refine ⟨14340726263749605307841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38241936703332280820909 14340726263749605307841)
    ·
      refine ⟨10755544697812203980881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14340726263749605307841 10755544697812203980881)
      ·
        refine ⟨8066658523359152985661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10755544697812203980881 8066658523359152985661)
        ·
          refine ⟨3024996946259682369623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8066658523359152985661 3024996946259682369623)
          ·
            refine ⟨4537495419389523554435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024996946259682369623 4537495419389523554435)
            ·
              refine ⟨6806243129084285331653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4537495419389523554435 6806243129084285331653)
              ·
                refine ⟨1276170586703303499685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6806243129084285331653 1276170586703303499685)
                ·
                  rfl

theorem cell19_4194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_4194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4194 prefixEnd_4194 := by exact prefixLift 4194
  have htrace : WordTrace (prefixWord ++ tailWord_4194) baseStart_4194 baseEnd_4194 := by
    simpa [prefixWord, tailWord_4194, baseEnd_4194] using wordTrace_append hprefix tailTrace_4194
  have hstable : (prefixWord ++ tailWord_4194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194).length < 2 ^ (prefixWord ++ tailWord_4194).sum := by decide
  have hdescent : baseEnd_4194 < baseStart_4194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4217 : List Nat := [1, 2, 1, 3, 4, 2, 3, 3]
def baseStart_4217 : Nat := 118140960795 + 4217 * 2 ^ 59
def prefixEnd_4217 : Nat := 4983230072969 + 3 ^ 40 * 4217 * 2
def baseEnd_4217 : Nat := 1283169137846064988511

theorem tailTrace_4217 : CollatzResearch.WordTrace tailWord_4217 prefixEnd_4217 1283169137846064988511 := by
  unfold tailWord_4217
  simp only [CollatzResearch.WordTrace]
  refine ⟨153806625730004051370905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102537750486669367580603 153806625730004051370905)
  ·
    refine ⟨115354969297503038528179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153806625730004051370905 115354969297503038528179)
    ·
      refine ⟨173032453946254557792269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115354969297503038528179 173032453946254557792269)
      ·
        refine ⟨64887170229845459172101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173032453946254557792269 64887170229845459172101)
        ·
          refine ⟨12166344418096023594769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64887170229845459172101 12166344418096023594769)
          ·
            refine ⟨9124758313572017696077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12166344418096023594769 9124758313572017696077)
            ·
              refine ⟨3421784367589506636029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9124758313572017696077 3421784367589506636029)
              ·
                refine ⟨1283169137846064988511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3421784367589506636029 1283169137846064988511)
                ·
                  rfl

theorem cell19_4217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 3].length) (baseStart_4217 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4217 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4217 prefixEnd_4217 := by exact prefixLift 4217
  have htrace : WordTrace (prefixWord ++ tailWord_4217) baseStart_4217 baseEnd_4217 := by
    simpa [prefixWord, tailWord_4217, baseEnd_4217] using wordTrace_append hprefix tailTrace_4217
  have hstable : (prefixWord ++ tailWord_4217).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4217).length < 2 ^ (prefixWord ++ tailWord_4217).sum := by decide
  have hdescent : baseEnd_4217 < baseStart_4217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240 : List Nat := [2, 1, 1, 1, 1, 1, 12]
def baseStart_4240 : Nat := 118140960795 + 4240 * 2 ^ 59
def prefixEnd_4240 : Nat := 4983230072969 + 3 ^ 40 * 4240 * 2
def baseEnd_4240 : Nat := 430055896329608825779

theorem tailTrace_4240 : CollatzResearch.WordTrace tailWord_4240 prefixEnd_4240 430055896329608825779 := by
  unfold tailWord_4240
  simp only [CollatzResearch.WordTrace]
  refine ⟨77322752323339489729087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103097003097785986305449 77322752323339489729087)
  ·
    refine ⟨115984128485009234593631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77322752323339489729087 115984128485009234593631)
    ·
      refine ⟨173976192727513851890447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115984128485009234593631 173976192727513851890447)
      ·
        refine ⟨260964289091270777835671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173976192727513851890447 260964289091270777835671)
        ·
          refine ⟨391446433636906166753507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260964289091270777835671 391446433636906166753507)
          ·
            refine ⟨587169650455359250130261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391446433636906166753507 587169650455359250130261)
            ·
              refine ⟨430055896329608825779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 587169650455359250130261 430055896329608825779)
              ·
                rfl

theorem cell19_4240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_4240 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4240 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4240 prefixEnd_4240 := by exact prefixLift 4240
  have htrace : WordTrace (prefixWord ++ tailWord_4240) baseStart_4240 baseEnd_4240 := by
    simpa [prefixWord, tailWord_4240, baseEnd_4240] using wordTrace_append hprefix tailTrace_4240
  have hstable : (prefixWord ++ tailWord_4240).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240).length < 2 ^ (prefixWord ++ tailWord_4240).sum := by decide
  have hdescent : baseEnd_4240 < baseStart_4240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310 : List Nat := [5, 2, 1, 2, 1, 2, 2, 4]
def baseStart_4310 : Nat := 118140960795 + 4310 * 2 ^ 59
def prefixEnd_4310 : Nat := 4983230072969 + 3 ^ 40 * 4310 * 2
def baseEnd_4310 : Nat := 1311467627249404921591

theorem tailTrace_4310 : CollatzResearch.WordTrace tailWord_4310 prefixEnd_4310 1311467627249404921591 := by
  unfold tailWord_4310
  simp only [CollatzResearch.WordTrace]
  refine ⟨9824913399567558406649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104799076262053956337589 9824913399567558406649)
  ·
    refine ⟨7368685049675668804987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9824913399567558406649 7368685049675668804987)
    ·
      refine ⟨11053027574513503207481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7368685049675668804987 11053027574513503207481)
      ·
        refine ⟨8289770680885127405611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11053027574513503207481 8289770680885127405611)
        ·
          refine ⟨12434656021327691108417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8289770680885127405611 12434656021327691108417)
          ·
            refine ⟨9325992015995768331313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12434656021327691108417 9325992015995768331313)
            ·
              refine ⟨6994494011996826248485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9325992015995768331313 6994494011996826248485)
              ·
                refine ⟨1311467627249404921591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6994494011996826248485 1311467627249404921591)
                ·
                  rfl

theorem cell19_4310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_4310 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4310 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4310 prefixEnd_4310 := by exact prefixLift 4310
  have htrace : WordTrace (prefixWord ++ tailWord_4310) baseStart_4310 baseEnd_4310 := by
    simpa [prefixWord, tailWord_4310, baseEnd_4310] using wordTrace_append hprefix tailTrace_4310
  have hstable : (prefixWord ++ tailWord_4310).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310).length < 2 ^ (prefixWord ++ tailWord_4310).sum := by decide
  have hdescent : baseEnd_4310 < baseStart_4310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388 : List Nat := [2, 3, 1, 3, 1, 3, 3, 3]
def baseStart_4388 : Nat := 118140960795 + 4388 * 2 ^ 59
def prefixEnd_4388 : Nat := 4983230072969 + 3 ^ 40 * 4388 * 2
def baseEnd_4388 : Nat := 1335201844168335188045

theorem tailTrace_4388 : CollatzResearch.WordTrace tailWord_4388 prefixEnd_4388 1335201844168335188045 := by
  unfold tailWord_4388
  simp only [CollatzResearch.WordTrace]
  refine ⟨80021754055250127922909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106695672073666837230545 80021754055250127922909)
  ·
    refine ⟨30008157770718797971091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80021754055250127922909 30008157770718797971091)
    ·
      refine ⟨45012236656078196956637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30008157770718797971091 45012236656078196956637)
      ·
        refine ⟨16879588746029323858739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45012236656078196956637 16879588746029323858739)
        ·
          refine ⟨25319383119043985788109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16879588746029323858739 25319383119043985788109)
          ·
            refine ⟨9494768669641494670541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25319383119043985788109 9494768669641494670541)
            ·
              refine ⟨3560538251115560501453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9494768669641494670541 3560538251115560501453)
              ·
                refine ⟨1335201844168335188045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3560538251115560501453 1335201844168335188045)
                ·
                  rfl

theorem cell19_4388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_4388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4388 prefixEnd_4388 := by exact prefixLift 4388
  have htrace : WordTrace (prefixWord ++ tailWord_4388) baseStart_4388 baseEnd_4388 := by
    simpa [prefixWord, tailWord_4388, baseEnd_4388] using wordTrace_append hprefix tailTrace_4388
  have hstable : (prefixWord ++ tailWord_4388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388).length < 2 ^ (prefixWord ++ tailWord_4388).sum := by decide
  have hdescent : baseEnd_4388 < baseStart_4388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4409 : List Nat := [1, 2, 1, 6, 1, 2, 6]
def baseStart_4409 : Nat := 118140960795 + 4409 * 2 ^ 59
def prefixEnd_4409 : Nat := 4983230072969 + 3 ^ 40 * 4409 * 2
def baseEnd_4409 : Nat := 447197275215502907107

theorem tailTrace_4409 : CollatzResearch.WordTrace tailWord_4409 prefixEnd_4409 447197275215502907107 := by
  unfold tailWord_4409
  simp only [CollatzResearch.WordTrace]
  refine ⟨160809441034420842360281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107206294022947228240187 160809441034420842360281)
  ·
    refine ⟨120607080775815631770211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160809441034420842360281 120607080775815631770211)
    ·
      refine ⟨180910621163723447655317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120607080775815631770211 180910621163723447655317)
      ·
        refine ⟨8480185367049536608843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 180910621163723447655317 8480185367049536608843)
        ·
          refine ⟨12720278050574304913265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8480185367049536608843 12720278050574304913265)
          ·
            refine ⟨9540208537930728684949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12720278050574304913265 9540208537930728684949)
            ·
              refine ⟨447197275215502907107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9540208537930728684949 447197275215502907107)
              ·
                rfl

theorem cell19_4409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 6].length) (baseStart_4409 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4409 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4409 prefixEnd_4409 := by exact prefixLift 4409
  have htrace : WordTrace (prefixWord ++ tailWord_4409) baseStart_4409 baseEnd_4409 := by
    simpa [prefixWord, tailWord_4409, baseEnd_4409] using wordTrace_append hprefix tailTrace_4409
  have hstable : (prefixWord ++ tailWord_4409).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4409).length < 2 ^ (prefixWord ++ tailWord_4409).sum := by decide
  have hdescent : baseEnd_4409 < baseStart_4409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4447 : List Nat := [1, 1, 2, 3, 1, 2, 6, 3]
def baseStart_4447 : Nat := 118140960795 + 4447 * 2 ^ 59
def prefixEnd_4447 : Nat := 4983230072969 + 3 ^ 40 * 4447 * 2
def baseEnd_4447 : Nat := 1353154649273679876773

theorem tailTrace_4447 : CollatzResearch.WordTrace tailWord_4447 prefixEnd_4447 1353154649273679876773 := by
  unfold tailWord_4447
  simp only [CollatzResearch.WordTrace]
  refine ⟨162195414896753332243595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108130276597835554829063 162195414896753332243595)
  ·
    refine ⟨243293122345129998365393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162195414896753332243595 243293122345129998365393)
    ·
      refine ⟨182469841758847498774045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243293122345129998365393 182469841758847498774045)
      ·
        refine ⟨68426190659567812040267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182469841758847498774045 68426190659567812040267)
        ·
          refine ⟨102639285989351718060401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68426190659567812040267 102639285989351718060401)
          ·
            refine ⟨76979464492013788545301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102639285989351718060401 76979464492013788545301)
            ·
              refine ⟨3608412398063146338061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76979464492013788545301 3608412398063146338061)
              ·
                refine ⟨1353154649273679876773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3608412398063146338061 1353154649273679876773)
                ·
                  rfl

theorem cell19_4447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 3].length) (baseStart_4447 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4447 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4447 prefixEnd_4447 := by exact prefixLift 4447
  have htrace : WordTrace (prefixWord ++ tailWord_4447) baseStart_4447 baseEnd_4447 := by
    simpa [prefixWord, tailWord_4447, baseEnd_4447] using wordTrace_append hprefix tailTrace_4447
  have hstable : (prefixWord ++ tailWord_4447).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4447).length < 2 ^ (prefixWord ++ tailWord_4447).sum := by decide
  have hdescent : baseEnd_4447 < baseStart_4447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466 : List Nat := [3, 2, 1, 2, 1, 5, 5]
def baseStart_4466 : Nat := 118140960795 + 4466 * 2 ^ 59
def prefixEnd_4466 : Nat := 4983230072969 + 3 ^ 40 * 4466 * 2
def baseEnd_4466 : Nat := 452978687029088484833

theorem tailTrace_4466 : CollatzResearch.WordTrace tailWord_4466 prefixEnd_4466 452978687029088484833 := by
  unfold tailWord_4466
  simp only [CollatzResearch.WordTrace]
  refine ⟨40722100456979894296313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108592267885279718123501 40722100456979894296313)
  ·
    refine ⟨30541575342734920722235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40722100456979894296313 30541575342734920722235)
    ·
      refine ⟨45812363014102381083353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30541575342734920722235 45812363014102381083353)
      ·
        refine ⟨34359272260576785812515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45812363014102381083353 34359272260576785812515)
        ·
          refine ⟨51538908390865178718773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34359272260576785812515 51538908390865178718773)
          ·
            refine ⟨4831772661643610504885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51538908390865178718773 4831772661643610504885)
            ·
              refine ⟨452978687029088484833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4831772661643610504885 452978687029088484833)
              ·
                rfl

theorem cell19_4466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 5].length) (baseStart_4466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4466 prefixEnd_4466 := by exact prefixLift 4466
  have htrace : WordTrace (prefixWord ++ tailWord_4466) baseStart_4466 baseEnd_4466 := by
    simpa [prefixWord, tailWord_4466, baseEnd_4466] using wordTrace_append hprefix tailTrace_4466
  have hstable : (prefixWord ++ tailWord_4466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466).length < 2 ^ (prefixWord ++ tailWord_4466).sum := by decide
  have hdescent : baseEnd_4466 < baseStart_4466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504 : List Nat := [2, 1, 2, 5, 1, 1, 2, 5]
def baseStart_4504 : Nat := 118140960795 + 4504 * 2 ^ 59
def prefixEnd_4504 : Nat := 4983230072969 + 3 ^ 40 * 4504 * 2
def baseEnd_4504 : Nat := 1370498884714436609951

theorem tailTrace_4504 : CollatzResearch.WordTrace tailWord_4504 prefixEnd_4504 1370498884714436609951 := by
  unfold tailWord_4504
  simp only [CollatzResearch.WordTrace]
  refine ⟨82137187845126033534283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109516250460168044712377 82137187845126033534283)
  ·
    refine ⟨123205781767689050301425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82137187845126033534283 123205781767689050301425)
    ·
      refine ⟨92404336325766787726069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123205781767689050301425 92404336325766787726069)
      ·
        refine ⟨8662906530540636349319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92404336325766787726069 8662906530540636349319)
        ·
          refine ⟨12994359795810954523979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8662906530540636349319 12994359795810954523979)
          ·
            refine ⟨19491539693716431785969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12994359795810954523979 19491539693716431785969)
            ·
              refine ⟨14618654770287323839477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19491539693716431785969 14618654770287323839477)
              ·
                refine ⟨1370498884714436609951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14618654770287323839477 1370498884714436609951)
                ·
                  rfl

theorem cell19_4504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_4504 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4504 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4504 prefixEnd_4504 := by exact prefixLift 4504
  have htrace : WordTrace (prefixWord ++ tailWord_4504) baseStart_4504 baseEnd_4504 := by
    simpa [prefixWord, tailWord_4504, baseEnd_4504] using wordTrace_append hprefix tailTrace_4504
  have hstable : (prefixWord ++ tailWord_4504).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504).length < 2 ^ (prefixWord ++ tailWord_4504).sum := by decide
  have hdescent : baseEnd_4504 < baseStart_4504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4540 : List Nat := [2, 2, 2, 4, 1, 3, 1, 4]
def baseStart_4540 : Nat := 118140960795 + 4540 * 2 ^ 59
def prefixEnd_4540 : Nat := 4983230072969 + 3 ^ 40 * 4540 * 2
def baseEnd_4540 : Nat := 1381453138677019809853

theorem tailTrace_4540 : CollatzResearch.WordTrace tailWord_4540 prefixEnd_4540 1381453138677019809853 := by
  unfold tailWord_4540
  simp only [CollatzResearch.WordTrace]
  refine ⟨82793701779915107689537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110391602373220143586049 82793701779915107689537)
  ·
    refine ⟨62095276334936330767153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82793701779915107689537 62095276334936330767153)
    ·
      refine ⟨46571457251202248075365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62095276334936330767153 46571457251202248075365)
      ·
        refine ⟨8732148234600421514131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46571457251202248075365 8732148234600421514131)
        ·
          refine ⟨13098222351900632271197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8732148234600421514131 13098222351900632271197)
          ·
            refine ⟨4911833381962737101699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13098222351900632271197 4911833381962737101699)
            ·
              refine ⟨7367750072944105652549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4911833381962737101699 7367750072944105652549)
              ·
                refine ⟨1381453138677019809853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7367750072944105652549 1381453138677019809853)
                ·
                  rfl

theorem cell19_4540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_4540 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4540 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4540 prefixEnd_4540 := by exact prefixLift 4540
  have htrace : WordTrace (prefixWord ++ tailWord_4540) baseStart_4540 baseEnd_4540 := by
    simpa [prefixWord, tailWord_4540, baseEnd_4540] using wordTrace_append hprefix tailTrace_4540
  have hstable : (prefixWord ++ tailWord_4540).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4540).length < 2 ^ (prefixWord ++ tailWord_4540).sum := by decide
  have hdescent : baseEnd_4540 < baseStart_4540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542 : List Nat := [4, 2, 1, 1, 1, 1, 5, 4]
def baseStart_4542 : Nat := 118140960795 + 4542 * 2 ^ 59
def prefixEnd_4542 : Nat := 4983230072969 + 3 ^ 40 * 4542 * 2
def baseEnd_4542 : Nat := 1382061708341607765403

theorem tailTrace_4542 : CollatzResearch.WordTrace tailWord_4542 prefixEnd_4542 1382061708341607765403 := by
  unfold tailWord_4542
  simp only [CollatzResearch.WordTrace]
  refine ⟨20707543694073069618985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110440233035056371301253 20707543694073069618985)
  ·
    refine ⟨15530657770554802214239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20707543694073069618985 15530657770554802214239)
    ·
      refine ⟨23295986655832203321359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15530657770554802214239 23295986655832203321359)
      ·
        refine ⟨34943979983748304982039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23295986655832203321359 34943979983748304982039)
        ·
          refine ⟨52415969975622457473059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34943979983748304982039 52415969975622457473059)
          ·
            refine ⟨78623954963433686209589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52415969975622457473059 78623954963433686209589)
            ·
              refine ⟨7370995777821908082149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78623954963433686209589 7370995777821908082149)
              ·
                refine ⟨1382061708341607765403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7370995777821908082149 1382061708341607765403)
                ·
                  rfl

theorem cell19_4542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_4542 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4542 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4542 prefixEnd_4542 := by exact prefixLift 4542
  have htrace : WordTrace (prefixWord ++ tailWord_4542) baseStart_4542 baseEnd_4542 := by
    simpa [prefixWord, tailWord_4542, baseEnd_4542] using wordTrace_append hprefix tailTrace_4542
  have hstable : (prefixWord ++ tailWord_4542).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542).length < 2 ^ (prefixWord ++ tailWord_4542).sum := by decide
  have hdescent : baseEnd_4542 < baseStart_4542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4637 : List Nat := [1, 4, 2, 2, 1, 4, 5]
def baseStart_4637 : Nat := 118140960795 + 4637 * 2 ^ 59
def prefixEnd_4637 : Nat := 4983230072969 + 3 ^ 40 * 4637 * 2
def baseEnd_4637 : Nat := 470322922469845218011

theorem tailTrace_4637 : CollatzResearch.WordTrace tailWord_4637 prefixEnd_4637 470322922469845218011 := by
  unfold tailWord_4637
  simp only [CollatzResearch.WordTrace]
  refine ⟨169125284208415781660165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112750189472277187773443 169125284208415781660165)
  ·
    refine ⟨31710990789077959061281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169125284208415781660165 31710990789077959061281)
    ·
      refine ⟨23783243091808469295961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31710990789077959061281 23783243091808469295961)
      ·
        refine ⟨17837432318856351971971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23783243091808469295961 17837432318856351971971)
        ·
          refine ⟨26756148478284527957957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17837432318856351971971 26756148478284527957957)
          ·
            refine ⟨5016777839678348992117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26756148478284527957957 5016777839678348992117)
            ·
              refine ⟨470322922469845218011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5016777839678348992117 470322922469845218011)
              ·
                rfl

theorem cell19_4637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 5].length) (baseStart_4637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4637 prefixEnd_4637 := by exact prefixLift 4637
  have htrace : WordTrace (prefixWord ++ tailWord_4637) baseStart_4637 baseEnd_4637 := by
    simpa [prefixWord, tailWord_4637, baseEnd_4637] using wordTrace_append hprefix tailTrace_4637
  have hstable : (prefixWord ++ tailWord_4637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4637).length < 2 ^ (prefixWord ++ tailWord_4637).sum := by decide
  have hdescent : baseEnd_4637 < baseStart_4637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4654 : List Nat := [4, 1, 3, 1, 3, 1, 2, 4]
def baseStart_4654 : Nat := 118140960795 + 4654 * 2 ^ 59
def prefixEnd_4654 : Nat := 4983230072969 + 3 ^ 40 * 4654 * 2
def baseEnd_4654 : Nat := 1416141609558533276209

theorem tailTrace_4654 : CollatzResearch.WordTrace tailWord_4654 prefixEnd_4654 1416141609558533276209 := by
  unfold tailWord_4654
  simp only [CollatzResearch.WordTrace]
  refine ⟨21218165643353460628627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113163550097885123352677 21218165643353460628627)
  ·
    refine ⟨31827248465030190942941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21218165643353460628627 31827248465030190942941)
    ·
      refine ⟨11935218174386321603603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31827248465030190942941 11935218174386321603603)
      ·
        refine ⟨17902827261579482405405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11935218174386321603603 17902827261579482405405)
        ·
          refine ⟨6713560223092305902027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17902827261579482405405 6713560223092305902027)
          ·
            refine ⟨10070340334638458853041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6713560223092305902027 10070340334638458853041)
            ·
              refine ⟨7552755250978844139781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10070340334638458853041 7552755250978844139781)
              ·
                refine ⟨1416141609558533276209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7552755250978844139781 1416141609558533276209)
                ·
                  rfl

theorem cell19_4654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_4654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4654 prefixEnd_4654 := by exact prefixLift 4654
  have htrace : WordTrace (prefixWord ++ tailWord_4654) baseStart_4654 baseEnd_4654 := by
    simpa [prefixWord, tailWord_4654, baseEnd_4654] using wordTrace_append hprefix tailTrace_4654
  have hstable : (prefixWord ++ tailWord_4654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4654).length < 2 ^ (prefixWord ++ tailWord_4654).sum := by decide
  have hdescent : baseEnd_4654 < baseStart_4654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4658 : List Nat := [3, 2, 1, 1, 2, 1, 3, 6]
def baseStart_4658 : Nat := 118140960795 + 4658 * 2 ^ 59
def prefixEnd_4658 : Nat := 4983230072969 + 3 ^ 40 * 4658 * 2
def baseEnd_4658 : Nat := 1417358748887709187309

theorem tailTrace_4658 : CollatzResearch.WordTrace tailWord_4658 prefixEnd_4658 1417358748887709187309 := by
  unfold tailWord_4658
  simp only [CollatzResearch.WordTrace]
  refine ⟨42472804283084092043657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113260811421557578783085 42472804283084092043657)
  ·
    refine ⟨31854603212313069032743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42472804283084092043657 31854603212313069032743)
    ·
      refine ⟨47781904818469603549115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31854603212313069032743 47781904818469603549115)
      ·
        refine ⟨71672857227704405323673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47781904818469603549115 71672857227704405323673)
        ·
          refine ⟨53754642920778303992755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71672857227704405323673 53754642920778303992755)
          ·
            refine ⟨80631964381167455989133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53754642920778303992755 80631964381167455989133)
            ·
              refine ⟨30236986642937795995925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80631964381167455989133 30236986642937795995925)
              ·
                refine ⟨1417358748887709187309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30236986642937795995925 1417358748887709187309)
                ·
                  rfl

theorem cell19_4658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_4658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4658 prefixEnd_4658 := by exact prefixLift 4658
  have htrace : WordTrace (prefixWord ++ tailWord_4658) baseStart_4658 baseEnd_4658 := by
    simpa [prefixWord, tailWord_4658, baseEnd_4658] using wordTrace_append hprefix tailTrace_4658
  have hstable : (prefixWord ++ tailWord_4658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4658).length < 2 ^ (prefixWord ++ tailWord_4658).sum := by decide
  have hdescent : baseEnd_4658 < baseStart_4658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677 : List Nat := [1, 3, 1, 1, 1, 5, 2, 5]
def baseStart_4677 : Nat := 118140960795 + 4677 * 2 ^ 59
def prefixEnd_4677 : Nat := 4983230072969 + 3 ^ 40 * 4677 * 2
def baseEnd_4677 : Nat := 1423140160701294765035

theorem tailTrace_4677 : CollatzResearch.WordTrace tailWord_4677 prefixEnd_4677 1423140160701294765035 := by
  unfold tailWord_4677
  simp only [CollatzResearch.WordTrace]
  refine ⟨170584204063502613116285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113722802709001742077523 170584204063502613116285)
  ·
    refine ⟨63969076523813479918607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170584204063502613116285 63969076523813479918607)
    ·
      refine ⟨95953614785720219877911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63969076523813479918607 95953614785720219877911)
      ·
        refine ⟨143930422178580329816867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95953614785720219877911 143930422178580329816867)
        ·
          refine ⟨215895633267870494725301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143930422178580329816867 215895633267870494725301)
          ·
            refine ⟨20240215618862858880497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 215895633267870494725301 20240215618862858880497)
            ·
              refine ⟨15180161714147144160373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20240215618862858880497 15180161714147144160373)
              ·
                refine ⟨1423140160701294765035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15180161714147144160373 1423140160701294765035)
                ·
                  rfl

theorem cell19_4677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_4677 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4677 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4677 prefixEnd_4677 := by exact prefixLift 4677
  have htrace : WordTrace (prefixWord ++ tailWord_4677) baseStart_4677 baseEnd_4677 := by
    simpa [prefixWord, tailWord_4677, baseEnd_4677] using wordTrace_append hprefix tailTrace_4677
  have hstable : (prefixWord ++ tailWord_4677).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677).length < 2 ^ (prefixWord ++ tailWord_4677).sum := by decide
  have hdescent : baseEnd_4677 < baseStart_4677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694 : List Nat := [5, 2, 2, 10]
def baseStart_4694 : Nat := 118140960795 + 4694 * 2 ^ 59
def prefixEnd_4694 : Nat := 4983230072969 + 3 ^ 40 * 4694 * 2
def baseEnd_4694 : Nat := 17633493862349288731

theorem tailTrace_4694 : CollatzResearch.WordTrace tailWord_4694 prefixEnd_4694 17633493862349288731 := by
  unfold tailWord_4694
  simp only [CollatzResearch.WordTrace]
  refine ⟨10700265312619657280321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114136163334609677656757 10700265312619657280321)
  ·
    refine ⟨8025198984464742960241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10700265312619657280321 8025198984464742960241)
    ·
      refine ⟨6018899238348557220181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8025198984464742960241 6018899238348557220181)
      ·
        refine ⟨17633493862349288731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 6018899238348557220181 17633493862349288731)
        ·
          rfl

theorem cell19_4694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 10].length) (baseStart_4694 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4694 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4694 prefixEnd_4694 := by exact prefixLift 4694
  have htrace : WordTrace (prefixWord ++ tailWord_4694) baseStart_4694 baseEnd_4694 := by
    simpa [prefixWord, tailWord_4694, baseEnd_4694] using wordTrace_append hprefix tailTrace_4694
  have hstable : (prefixWord ++ tailWord_4694).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694).length < 2 ^ (prefixWord ++ tailWord_4694).sum := by decide
  have hdescent : baseEnd_4694 < baseStart_4694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4772 : List Nat := [2, 3, 1, 2, 2, 1, 2, 6]
def baseStart_4772 : Nat := 118140960795 + 4772 * 2 ^ 59
def prefixEnd_4772 : Nat := 4983230072969 + 3 ^ 40 * 4772 * 2
def baseEnd_4772 : Nat := 1452047219769222653665

theorem tailTrace_4772 : CollatzResearch.WordTrace tailWord_4772 prefixEnd_4772 1452047219769222653665 := by
  unfold tailWord_4772
  simp only [CollatzResearch.WordTrace]
  refine ⟨87024569359666918912285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116032759146222558549713 87024569359666918912285)
  ·
    refine ⟨32634213509875094592107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87024569359666918912285 32634213509875094592107)
    ·
      refine ⟨48951320264812641888161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32634213509875094592107 48951320264812641888161)
      ·
        refine ⟨36713490198609481416121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48951320264812641888161 36713490198609481416121)
        ·
          refine ⟨27535117648957111062091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36713490198609481416121 27535117648957111062091)
          ·
            refine ⟨41302676473435666593137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27535117648957111062091 41302676473435666593137)
            ·
              refine ⟨30977007355076749944853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41302676473435666593137 30977007355076749944853)
              ·
                refine ⟨1452047219769222653665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30977007355076749944853 1452047219769222653665)
                ·
                  rfl

theorem cell19_4772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_4772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4772 prefixEnd_4772 := by exact prefixLift 4772
  have htrace : WordTrace (prefixWord ++ tailWord_4772) baseStart_4772 baseEnd_4772 := by
    simpa [prefixWord, tailWord_4772, baseEnd_4772] using wordTrace_append hprefix tailTrace_4772
  have hstable : (prefixWord ++ tailWord_4772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4772).length < 2 ^ (prefixWord ++ tailWord_4772).sum := by decide
  have hdescent : baseEnd_4772 < baseStart_4772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785 : List Nat := [1, 2, 2, 6, 1, 2, 2, 3]
def baseStart_4785 : Nat := 118140960795 + 4785 * 2 ^ 59
def prefixEnd_4785 : Nat := 4983230072969 + 3 ^ 40 * 4785 * 2
def baseEnd_4785 : Nat := 1456002922589044364741

theorem tailTrace_4785 : CollatzResearch.WordTrace tailWord_4785 prefixEnd_4785 1456002922589044364741 := by
  unfold tailWord_4785
  simp only [CollatzResearch.WordTrace]
  refine ⟨174523287672237058047809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116348858448158038698539 174523287672237058047809)
  ·
    refine ⟨130892465754177793535857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174523287672237058047809 130892465754177793535857)
    ·
      refine ⟨98169349315633345151893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130892465754177793535857 98169349315633345151893)
      ·
        refine ⟨4601688249170313053995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98169349315633345151893 4601688249170313053995)
        ·
          refine ⟨6902532373755469580993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4601688249170313053995 6902532373755469580993)
          ·
            refine ⟨5176899280316602185745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6902532373755469580993 5176899280316602185745)
            ·
              refine ⟨3882674460237451639309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5176899280316602185745 3882674460237451639309)
              ·
                refine ⟨1456002922589044364741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3882674460237451639309 1456002922589044364741)
                ·
                  rfl

theorem cell19_4785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 3].length) (baseStart_4785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4785 prefixEnd_4785 := by exact prefixLift 4785
  have htrace : WordTrace (prefixWord ++ tailWord_4785) baseStart_4785 baseEnd_4785 := by
    simpa [prefixWord, tailWord_4785, baseEnd_4785] using wordTrace_append hprefix tailTrace_4785
  have hstable : (prefixWord ++ tailWord_4785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785).length < 2 ^ (prefixWord ++ tailWord_4785).sum := by decide
  have hdescent : baseEnd_4785 < baseStart_4785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4789 : List Nat := [1, 3, 3, 3, 1, 2, 1, 5]
def baseStart_4789 : Nat := 118140960795 + 4789 * 2 ^ 59
def prefixEnd_4789 : Nat := 4983230072969 + 3 ^ 40 * 4789 * 2
def baseEnd_4789 : Nat := 1457220061918220275841

theorem tailTrace_4789 : CollatzResearch.WordTrace tailWord_4789 prefixEnd_4789 1457220061918220275841 := by
  unfold tailWord_4789
  simp only [CollatzResearch.WordTrace]
  refine ⟨174669179657745741193421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116446119771830494128947 174669179657745741193421)
  ·
    refine ⟨65500942371654652947533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174669179657745741193421 65500942371654652947533)
    ·
      refine ⟨24562853389370494855325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65500942371654652947533 24562853389370494855325)
      ·
        refine ⟨9211070021013935570747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24562853389370494855325 9211070021013935570747)
        ·
          refine ⟨13816605031520903356121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9211070021013935570747 13816605031520903356121)
          ·
            refine ⟨10362453773640677517091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13816605031520903356121 10362453773640677517091)
            ·
              refine ⟨15543680660461016275637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10362453773640677517091 15543680660461016275637)
              ·
                refine ⟨1457220061918220275841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15543680660461016275637 1457220061918220275841)
                ·
                  rfl

theorem cell19_4789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_4789 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4789 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4789 prefixEnd_4789 := by exact prefixLift 4789
  have htrace : WordTrace (prefixWord ++ tailWord_4789) baseStart_4789 baseEnd_4789 := by
    simpa [prefixWord, tailWord_4789, baseEnd_4789] using wordTrace_append hprefix tailTrace_4789
  have hstable : (prefixWord ++ tailWord_4789).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4789).length < 2 ^ (prefixWord ++ tailWord_4789).sum := by decide
  have hdescent : baseEnd_4789 < baseStart_4789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810 : List Nat := [3, 1, 2, 1, 4, 1, 7]
def baseStart_4810 : Nat := 118140960795 + 4810 * 2 ^ 59
def prefixEnd_4810 : Nat := 4983230072969 + 3 ^ 40 * 4810 * 2
def baseEnd_4810 : Nat := 487870014465464603039

theorem tailTrace_4810 : CollatzResearch.WordTrace tailWord_4810 prefixEnd_4810 487870014465464603039 := by
  unfold tailWord_4810
  simp only [CollatzResearch.WordTrace]
  refine ⟨43858778145416581926971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116956741721110885138589 43858778145416581926971)
  ·
    refine ⟨65788167218124872890457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43858778145416581926971 65788167218124872890457)
    ·
      refine ⟨49341125413593654667843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65788167218124872890457 49341125413593654667843)
      ·
        refine ⟨74011688120390482001765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49341125413593654667843 74011688120390482001765)
        ·
          refine ⟨13877191522573215375331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74011688120390482001765 13877191522573215375331)
          ·
            refine ⟨20815787283859823062997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13877191522573215375331 20815787283859823062997)
            ·
              refine ⟨487870014465464603039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 20815787283859823062997 487870014465464603039)
              ·
                rfl

theorem cell19_4810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 7].length) (baseStart_4810 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4810 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4810 prefixEnd_4810 := by exact prefixLift 4810
  have htrace : WordTrace (prefixWord ++ tailWord_4810) baseStart_4810 baseEnd_4810 := by
    simpa [prefixWord, tailWord_4810, baseEnd_4810] using wordTrace_append hprefix tailTrace_4810
  have hstable : (prefixWord ++ tailWord_4810).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810).length < 2 ^ (prefixWord ++ tailWord_4810).sum := by decide
  have hdescent : baseEnd_4810 < baseStart_4810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4981 : List Nat := [1, 3, 4, 1, 1, 2, 7]
def baseStart_4981 : Nat := 118140960795 + 4981 * 2 ^ 59
def prefixEnd_4981 : Nat := 4983230072969 + 3 ^ 40 * 4981 * 2
def baseEnd_4981 : Nat := 505214249906221336217

theorem tailTrace_4981 : CollatzResearch.WordTrace tailWord_4981 prefixEnd_4981 505214249906221336217 := by
  unfold tailWord_4981
  simp only [CollatzResearch.WordTrace]
  refine ⟨181671994962162532182797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121114663308108354788531 181671994962162532182797)
  ·
    refine ⟨68126998110810949568549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181671994962162532182797 68126998110810949568549)
    ·
      refine ⟨12773812145777053044103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68126998110810949568549 12773812145777053044103)
      ·
        refine ⟨19160718218665579566155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12773812145777053044103 19160718218665579566155)
        ·
          refine ⟨28741077327998369349233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19160718218665579566155 28741077327998369349233)
          ·
            refine ⟨21555807995998777011925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28741077327998369349233 21555807995998777011925)
            ·
              refine ⟨505214249906221336217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21555807995998777011925 505214249906221336217)
              ·
                rfl

theorem cell19_4981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 7].length) (baseStart_4981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4981 prefixEnd_4981 := by exact prefixLift 4981
  have htrace : WordTrace (prefixWord ++ tailWord_4981) baseStart_4981 baseEnd_4981 := by
    simpa [prefixWord, tailWord_4981, baseEnd_4981] using wordTrace_append hprefix tailTrace_4981
  have hstable : (prefixWord ++ tailWord_4981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4981).length < 2 ^ (prefixWord ++ tailWord_4981).sum := by decide
  have hdescent : baseEnd_4981 < baseStart_4981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4994 : List Nat := [3, 4, 2, 2, 1, 1, 2, 4]
def baseStart_4994 : Nat := 118140960795 + 4994 * 2 ^ 59
def prefixEnd_4994 : Nat := 4983230072969 + 3 ^ 40 * 4994 * 2
def baseEnd_4994 : Nat := 1519598452538485719727

theorem tailTrace_4994 : CollatzResearch.WordTrace tailWord_4994 prefixEnd_4994 1519598452538485719727 := by
  unfold tailWord_4994
  simp only [CollatzResearch.WordTrace]
  refine ⟨45536535978766438101509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121430762610043834937357 45536535978766438101509)
  ·
    refine ⟨8538100496018707144033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45536535978766438101509 8538100496018707144033)
    ·
      refine ⟨6403575372014030358025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8538100496018707144033 6403575372014030358025)
      ·
        refine ⟨4802681529010522768519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6403575372014030358025 4802681529010522768519)
        ·
          refine ⟨7204022293515784152779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4802681529010522768519 7204022293515784152779)
          ·
            refine ⟨10806033440273676229169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7204022293515784152779 10806033440273676229169)
            ·
              refine ⟨8104525080205257171877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10806033440273676229169 8104525080205257171877)
              ·
                refine ⟨1519598452538485719727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8104525080205257171877 1519598452538485719727)
                ·
                  rfl

theorem cell19_4994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_4994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_4994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_4994 prefixEnd_4994 := by exact prefixLift 4994
  have htrace : WordTrace (prefixWord ++ tailWord_4994) baseStart_4994 baseEnd_4994 := by
    simpa [prefixWord, tailWord_4994, baseEnd_4994] using wordTrace_append hprefix tailTrace_4994
  have hstable : (prefixWord ++ tailWord_4994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4994).length < 2 ^ (prefixWord ++ tailWord_4994).sum := by decide
  have hdescent : baseEnd_4994 < baseStart_4994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000 : List Nat := [2, 1, 3, 3, 2, 1, 1, 6]
def baseStart_5000 : Nat := 118140960795 + 5000 * 2 ^ 59
def prefixEnd_5000 : Nat := 4983230072969 + 3 ^ 40 * 5000 * 2
def baseEnd_5000 : Nat := 1521424161532249586377

theorem tailTrace_5000 : CollatzResearch.WordTrace tailWord_5000 prefixEnd_5000 1521424161532249586377 := by
  unfold tailWord_5000
  simp only [CollatzResearch.WordTrace]
  refine ⟨91182490946664388562227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121576654595552518082969 91182490946664388562227)
  ·
    refine ⟨136773736419996582843341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91182490946664388562227 136773736419996582843341)
    ·
      refine ⟨51290151157498718566253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136773736419996582843341 51290151157498718566253)
      ·
        refine ⟨19233806684062019462345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51290151157498718566253 19233806684062019462345)
        ·
          refine ⟨14425355013046514596759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19233806684062019462345 14425355013046514596759)
          ·
            refine ⟨21638032519569771895139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14425355013046514596759 21638032519569771895139)
            ·
              refine ⟨32457048779354657842709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21638032519569771895139 32457048779354657842709)
              ·
                refine ⟨1521424161532249586377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32457048779354657842709 1521424161532249586377)
                ·
                  rfl

theorem cell19_5000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_5000 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5000 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5000 prefixEnd_5000 := by exact prefixLift 5000
  have htrace : WordTrace (prefixWord ++ tailWord_5000) baseStart_5000 baseEnd_5000 := by
    simpa [prefixWord, tailWord_5000, baseEnd_5000] using wordTrace_append hprefix tailTrace_5000
  have hstable : (prefixWord ++ tailWord_5000).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000).length < 2 ^ (prefixWord ++ tailWord_5000).sum := by decide
  have hdescent : baseEnd_5000 < baseStart_5000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053 : List Nat := [1, 4, 1, 2, 5, 1, 1, 4]
def baseStart_5053 : Nat := 118140960795 + 5053 * 2 ^ 59
def prefixEnd_5053 : Nat := 4983230072969 + 3 ^ 40 * 5053 * 2
def baseEnd_5053 : Nat := 1537551257643830408455

theorem tailTrace_5053 : CollatzResearch.WordTrace tailWord_5053 prefixEnd_5053 1537551257643830408455 := by
  unfold tailWord_5053
  simp only [CollatzResearch.WordTrace]
  refine ⟨184298050701318828803813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122865367134212552535875 184298050701318828803813)
  ·
    refine ⟨34555884506497280400715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184298050701318828803813 34555884506497280400715)
    ·
      refine ⟨51833826759745920601073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34555884506497280400715 51833826759745920601073)
      ·
        refine ⟨38875370069809440450805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51833826759745920601073 38875370069809440450805)
        ·
          refine ⟨3644565944044635042263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38875370069809440450805 3644565944044635042263)
          ·
            refine ⟨5466848916066952563395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3644565944044635042263 5466848916066952563395)
            ·
              refine ⟨8200273374100428845093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5466848916066952563395 8200273374100428845093)
              ·
                refine ⟨1537551257643830408455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8200273374100428845093 1537551257643830408455)
                ·
                  rfl

theorem cell19_5053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 4].length) (baseStart_5053 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5053 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5053 prefixEnd_5053 := by exact prefixLift 5053
  have htrace : WordTrace (prefixWord ++ tailWord_5053) baseStart_5053 baseEnd_5053 := by
    simpa [prefixWord, tailWord_5053, baseEnd_5053] using wordTrace_append hprefix tailTrace_5053
  have hstable : (prefixWord ++ tailWord_5053).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053).length < 2 ^ (prefixWord ++ tailWord_5053).sum := by decide
  have hdescent : baseEnd_5053 < baseStart_5053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5093 : List Nat := [1, 3, 1, 6, 1, 1, 6]
def baseStart_5093 : Nat := 118140960795 + 5093 * 2 ^ 59
def prefixEnd_5093 : Nat := 4983230072969 + 3 ^ 40 * 5093 * 2
def baseEnd_5093 : Nat := 516574216978529839819

theorem tailTrace_5093 : CollatzResearch.WordTrace tailWord_5093 prefixEnd_5093 516574216978529839819 := by
  unfold tailWord_5093
  simp only [CollatzResearch.WordTrace]
  refine ⟨185756970556405660259933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123837980370937106839955 185756970556405660259933)
  ·
    refine ⟨69658863958652122597475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185756970556405660259933 69658863958652122597475)
    ·
      refine ⟨104488295937978183896213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69658863958652122597475 104488295937978183896213)
      ·
        refine ⟨4897888872092727370135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104488295937978183896213 4897888872092727370135)
        ·
          refine ⟨7346833308139091055203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4897888872092727370135 7346833308139091055203)
          ·
            refine ⟨11020249962208636582805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7346833308139091055203 11020249962208636582805)
            ·
              refine ⟨516574216978529839819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11020249962208636582805 516574216978529839819)
              ·
                rfl

theorem cell19_5093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 6].length) (baseStart_5093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5093 prefixEnd_5093 := by exact prefixLift 5093
  have htrace : WordTrace (prefixWord ++ tailWord_5093) baseStart_5093 baseEnd_5093 := by
    simpa [prefixWord, tailWord_5093, baseEnd_5093] using wordTrace_append hprefix tailTrace_5093
  have hstable : (prefixWord ++ tailWord_5093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5093).length < 2 ^ (prefixWord ++ tailWord_5093).sum := by decide
  have hdescent : baseEnd_5093 < baseStart_5093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095 : List Nat := [1, 1, 5, 2, 2, 2, 6]
def baseStart_5095 : Nat := 118140960795 + 5095 * 2 ^ 59
def prefixEnd_5095 : Nat := 4983230072969 + 3 ^ 40 * 5095 * 2
def baseEnd_5095 : Nat := 516777073533392491669

theorem tailTrace_5095 : CollatzResearch.WordTrace tailWord_5095 prefixEnd_5095 516777073533392491669 := by
  unfold tailWord_5095
  simp only [CollatzResearch.WordTrace]
  refine ⟨185829916549160001832739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123886611032773334555159 185829916549160001832739)
  ·
    refine ⟨278744874823740002749109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185829916549160001832739 278744874823740002749109)
    ·
      refine ⟨26132332014725625257729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 278744874823740002749109 26132332014725625257729)
      ·
        refine ⟨19599249011044218943297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26132332014725625257729 19599249011044218943297)
        ·
          refine ⟨14699436758283164207473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19599249011044218943297 14699436758283164207473)
          ·
            refine ⟨11024577568712373155605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14699436758283164207473 11024577568712373155605)
            ·
              refine ⟨516777073533392491669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11024577568712373155605 516777073533392491669)
              ·
                rfl

theorem cell19_5095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 6].length) (baseStart_5095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5095 prefixEnd_5095 := by exact prefixLift 5095
  have htrace : WordTrace (prefixWord ++ tailWord_5095) baseStart_5095 baseEnd_5095 := by
    simpa [prefixWord, tailWord_5095, baseEnd_5095] using wordTrace_append hprefix tailTrace_5095
  have hstable : (prefixWord ++ tailWord_5095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095).length < 2 ^ (prefixWord ++ tailWord_5095).sum := by decide
  have hdescent : baseEnd_5095 < baseStart_5095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5131 : List Nat := [1, 1, 1, 1, 6, 4, 2, 3]
def baseStart_5131 : Nat := 118140960795 + 5131 * 2 ^ 59
def prefixEnd_5131 : Nat := 4983230072969 + 3 ^ 40 * 5131 * 2
def baseEnd_5131 : Nat := 1561285474562760674909

theorem tailTrace_5131 : CollatzResearch.WordTrace tailWord_5131 prefixEnd_5131 1561285474562760674909 := by
  unfold tailWord_5131
  simp only [CollatzResearch.WordTrace]
  refine ⟨187142944418738150143247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124761962945825433428831 187142944418738150143247)
  ·
    refine ⟨280714416628107225214871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187142944418738150143247 280714416628107225214871)
    ·
      refine ⟨421071624942160837822307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280714416628107225214871 421071624942160837822307)
      ·
        refine ⟨631607437413241256733461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421071624942160837822307 631607437413241256733461)
        ·
          refine ⟨29606598628745683909381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 631607437413241256733461 29606598628745683909381)
          ·
            refine ⟨5551237242889815733009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29606598628745683909381 5551237242889815733009)
            ·
              refine ⟨4163427932167361799757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5551237242889815733009 4163427932167361799757)
              ·
                refine ⟨1561285474562760674909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4163427932167361799757 1561285474562760674909)
                ·
                  rfl

theorem cell19_5131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 3].length) (baseStart_5131 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5131 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5131 prefixEnd_5131 := by exact prefixLift 5131
  have htrace : WordTrace (prefixWord ++ tailWord_5131) baseStart_5131 baseEnd_5131 := by
    simpa [prefixWord, tailWord_5131, baseEnd_5131] using wordTrace_append hprefix tailTrace_5131
  have hstable : (prefixWord ++ tailWord_5131).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5131).length < 2 ^ (prefixWord ++ tailWord_5131).sum := by decide
  have hdescent : baseEnd_5131 < baseStart_5131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192 : List Nat := [2, 1, 3, 1, 1, 1, 3, 7]
def baseStart_5192 : Nat := 118140960795 + 5192 * 2 ^ 59
def prefixEnd_5192 : Nat := 4983230072969 + 3 ^ 40 * 5192 * 2
def baseEnd_5192 : Nat := 1579846849332693319187

theorem tailTrace_5192 : CollatzResearch.WordTrace tailWord_5192 prefixEnd_5192 1579846849332693319187 := by
  unfold tailWord_5192
  simp only [CollatzResearch.WordTrace]
  refine ⟨94683898598872784056915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126245198131830378742553 94683898598872784056915)
  ·
    refine ⟨142025847898309176085373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94683898598872784056915 142025847898309176085373)
    ·
      refine ⟨53259692961865941032015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142025847898309176085373 53259692961865941032015)
      ·
        refine ⟨79889539442798911548023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53259692961865941032015 79889539442798911548023)
        ·
          refine ⟨119834309164198367322035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79889539442798911548023 119834309164198367322035)
          ·
            refine ⟨179751463746297550983053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119834309164198367322035 179751463746297550983053)
            ·
              refine ⟨67406798904861581618645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179751463746297550983053 67406798904861581618645)
              ·
                refine ⟨1579846849332693319187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 67406798904861581618645 1579846849332693319187)
                ·
                  rfl

theorem cell19_5192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_5192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5192 prefixEnd_5192 := by exact prefixLift 5192
  have htrace : WordTrace (prefixWord ++ tailWord_5192) baseStart_5192 baseEnd_5192 := by
    simpa [prefixWord, tailWord_5192, baseEnd_5192] using wordTrace_append hprefix tailTrace_5192
  have hstable : (prefixWord ++ tailWord_5192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192).length < 2 ^ (prefixWord ++ tailWord_5192).sum := by decide
  have hdescent : baseEnd_5192 < baseStart_5192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224 : List Nat := [2, 1, 4, 4, 1, 2, 1, 4]
def baseStart_5224 : Nat := 118140960795 + 5224 * 2 ^ 59
def prefixEnd_5224 : Nat := 4983230072969 + 3 ^ 40 * 5224 * 2
def baseEnd_5224 : Nat := 1589583963966100607989

theorem tailTrace_5224 : CollatzResearch.WordTrace tailWord_5224 prefixEnd_5224 1589583963966100607989 := by
  unfold tailWord_5224
  simp only [CollatzResearch.WordTrace]
  refine ⟨95267466540907516639363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127023288721210022185817 95267466540907516639363)
  ·
    refine ⟨142901199811361274959045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95267466540907516639363 142901199811361274959045)
    ·
      refine ⟨26793974964630239054821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142901199811361274959045 26793974964630239054821)
      ·
        refine ⟨5023870305868169822779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26793974964630239054821 5023870305868169822779)
        ·
          refine ⟨7535805458802254734169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5023870305868169822779 7535805458802254734169)
          ·
            refine ⟨5651854094101691050627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7535805458802254734169 5651854094101691050627)
            ·
              refine ⟨8477781141152536575941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5651854094101691050627 8477781141152536575941)
              ·
                refine ⟨1589583963966100607989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8477781141152536575941 1589583963966100607989)
                ·
                  rfl

theorem cell19_5224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_5224 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5224 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5224 prefixEnd_5224 := by exact prefixLift 5224
  have htrace : WordTrace (prefixWord ++ tailWord_5224) baseStart_5224 baseEnd_5224 := by
    simpa [prefixWord, tailWord_5224, baseEnd_5224] using wordTrace_append hprefix tailTrace_5224
  have hstable : (prefixWord ++ tailWord_5224).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224).length < 2 ^ (prefixWord ++ tailWord_5224).sum := by decide
  have hdescent : baseEnd_5224 < baseStart_5224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5226 : List Nat := [3, 1, 3, 2, 2, 3, 1, 4]
def baseStart_5226 : Nat := 118140960795 + 5226 * 2 ^ 59
def prefixEnd_5226 : Nat := 4983230072969 + 3 ^ 40 * 5226 * 2
def baseEnd_5226 : Nat := 1590192533630688563539

theorem tailTrace_5226 : CollatzResearch.WordTrace tailWord_5226 prefixEnd_5226 1590192533630688563539 := by
  unfold tailWord_5226
  simp only [CollatzResearch.WordTrace]
  refine ⟨47651969768642343712883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127071919383046249901021 47651969768642343712883)
  ·
    refine ⟨71477954652963515569325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47651969768642343712883 71477954652963515569325)
    ·
      refine ⟨26804232994861318338497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71477954652963515569325 26804232994861318338497)
      ·
        refine ⟨20103174746145988753873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26804232994861318338497 20103174746145988753873)
        ·
          refine ⟨15077381059609491565405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20103174746145988753873 15077381059609491565405)
          ·
            refine ⟨5654017897353559337027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15077381059609491565405 5654017897353559337027)
            ·
              refine ⟨8481026846030339005541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5654017897353559337027 8481026846030339005541)
              ·
                refine ⟨1590192533630688563539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8481026846030339005541 1590192533630688563539)
                ·
                  rfl

theorem cell19_5226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_5226 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5226 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5226 prefixEnd_5226 := by exact prefixLift 5226
  have htrace : WordTrace (prefixWord ++ tailWord_5226) baseStart_5226 baseEnd_5226 := by
    simpa [prefixWord, tailWord_5226, baseEnd_5226] using wordTrace_append hprefix tailTrace_5226
  have hstable : (prefixWord ++ tailWord_5226).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5226).length < 2 ^ (prefixWord ++ tailWord_5226).sum := by decide
  have hdescent : baseEnd_5226 < baseStart_5226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5266 : List Nat := [3, 2, 3, 1, 1, 3, 6]
def baseStart_5266 : Nat := 118140960795 + 5266 * 2 ^ 59
def prefixEnd_5266 : Nat := 4983230072969 + 3 ^ 40 * 5266 * 2
def baseEnd_5266 : Nat := 534121308974149224847

theorem tailTrace_5266 : CollatzResearch.WordTrace tailWord_5266 prefixEnd_5266 534121308974149224847 := by
  unfold tailWord_5266
  simp only [CollatzResearch.WordTrace]
  refine ⟨48016699732414051576913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128044532619770804205101 48016699732414051576913)
  ·
    refine ⟨36012524799310538682685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48016699732414051576913 36012524799310538682685)
    ·
      refine ⟨13504696799741452006007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36012524799310538682685 13504696799741452006007)
      ·
        refine ⟨20257045199612178009011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13504696799741452006007 20257045199612178009011)
        ·
          refine ⟨30385567799418267013517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20257045199612178009011 30385567799418267013517)
          ·
            refine ⟨11394587924781850130069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30385567799418267013517 11394587924781850130069)
            ·
              refine ⟨534121308974149224847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11394587924781850130069 534121308974149224847)
              ·
                rfl

theorem cell19_5266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 6].length) (baseStart_5266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5266 prefixEnd_5266 := by exact prefixLift 5266
  have htrace : WordTrace (prefixWord ++ tailWord_5266) baseStart_5266 baseEnd_5266 := by
    simpa [prefixWord, tailWord_5266, baseEnd_5266] using wordTrace_append hprefix tailTrace_5266
  have hstable : (prefixWord ++ tailWord_5266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5266).length < 2 ^ (prefixWord ++ tailWord_5266).sum := by decide
  have hdescent : baseEnd_5266 < baseStart_5266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344 : List Nat := [2, 1, 1, 3, 1, 4, 1, 6]
def baseStart_5344 : Nat := 118140960795 + 5344 * 2 ^ 59
def prefixEnd_5344 : Nat := 4983230072969 + 3 ^ 40 * 5344 * 2
def baseEnd_5344 : Nat := 1626098143841377940995

theorem tailTrace_5344 : CollatzResearch.WordTrace tailWord_5344 prefixEnd_5344 1626098143841377940995 := by
  unfold tailWord_5344
  simp only [CollatzResearch.WordTrace]
  refine ⟨97455846323537763823543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129941128431383685098057 97455846323537763823543)
  ·
    refine ⟨146183769485306645735315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97455846323537763823543 146183769485306645735315)
    ·
      refine ⟨219275654227959968602973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146183769485306645735315 219275654227959968602973)
      ·
        refine ⟨82228370335484988226115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219275654227959968602973 82228370335484988226115)
        ·
          refine ⟨123342555503227482339173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82228370335484988226115 123342555503227482339173)
          ·
            refine ⟨23126729156855152938595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123342555503227482339173 23126729156855152938595)
            ·
              refine ⟨34690093735282729407893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23126729156855152938595 34690093735282729407893)
              ·
                refine ⟨1626098143841377940995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34690093735282729407893 1626098143841377940995)
                ·
                  rfl

theorem cell19_5344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_5344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5344 prefixEnd_5344 := by exact prefixLift 5344
  have htrace : WordTrace (prefixWord ++ tailWord_5344) baseStart_5344 baseEnd_5344 := by
    simpa [prefixWord, tailWord_5344, baseEnd_5344] using wordTrace_append hprefix tailTrace_5344
  have hstable : (prefixWord ++ tailWord_5344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344).length < 2 ^ (prefixWord ++ tailWord_5344).sum := by decide
  have hdescent : baseEnd_5344 < baseStart_5344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363 : List Nat := [1, 1, 1, 2, 2, 5, 2, 5]
def baseStart_5363 : Nat := 118140960795 + 5363 * 2 ^ 59
def prefixEnd_5363 : Nat := 4983230072969 + 3 ^ 40 * 5363 * 2
def baseEnd_5363 : Nat := 1631879555654963518721

theorem tailTrace_5363 : CollatzResearch.WordTrace tailWord_5363 prefixEnd_5363 1631879555654963518721 := by
  unfold tailWord_5363
  simp only [CollatzResearch.WordTrace]
  refine ⟨195604679578241772588743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130403119718827848392495 195604679578241772588743)
  ·
    refine ⟨293407019367362658883115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195604679578241772588743 293407019367362658883115)
    ·
      refine ⟨440110529051043988324673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293407019367362658883115 440110529051043988324673)
      ·
        refine ⟨330082896788282991243505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440110529051043988324673 330082896788282991243505)
        ·
          refine ⟨247562172591212243432629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330082896788282991243505 247562172591212243432629)
          ·
            refine ⟨23208953680426147821809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 247562172591212243432629 23208953680426147821809)
            ·
              refine ⟨17406715260319610866357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23208953680426147821809 17406715260319610866357)
              ·
                refine ⟨1631879555654963518721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17406715260319610866357 1631879555654963518721)
                ·
                  rfl

theorem cell19_5363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_5363 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5363 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5363 prefixEnd_5363 := by exact prefixLift 5363
  have htrace : WordTrace (prefixWord ++ tailWord_5363) baseStart_5363 baseEnd_5363 := by
    simpa [prefixWord, tailWord_5363, baseEnd_5363] using wordTrace_append hprefix tailTrace_5363
  have hstable : (prefixWord ++ tailWord_5363).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363).length < 2 ^ (prefixWord ++ tailWord_5363).sum := by decide
  have hdescent : baseEnd_5363 < baseStart_5363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378 : List Nat := [3, 4, 1, 1, 4, 6]
def baseStart_5378 : Nat := 118140960795 + 5378 * 2 ^ 59
def prefixEnd_5378 : Nat := 4983230072969 + 3 ^ 40 * 5378 * 2
def baseEnd_5378 : Nat := 181827092015485909483

theorem tailTrace_5378 : CollatzResearch.WordTrace tailWord_5378 prefixEnd_5378 181827092015485909483 := by
  unfold tailWord_5378
  simp only [CollatzResearch.WordTrace]
  refine ⟨49037943630974833596197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130767849682599556256525 49037943630974833596197)
  ·
    refine ⟨9194614430807781299287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49037943630974833596197 9194614430807781299287)
    ·
      refine ⟨13791921646211671948931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9194614430807781299287 13791921646211671948931)
      ·
        refine ⟨20687882469317507923397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13791921646211671948931 20687882469317507923397)
        ·
          refine ⟨3878977962997032735637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20687882469317507923397 3878977962997032735637)
          ·
            refine ⟨181827092015485909483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3878977962997032735637 181827092015485909483)
            ·
              rfl

theorem cell19_5378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 6].length) (baseStart_5378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5378 prefixEnd_5378 := by exact prefixLift 5378
  have htrace : WordTrace (prefixWord ++ tailWord_5378) baseStart_5378 baseEnd_5378 := by
    simpa [prefixWord, tailWord_5378, baseEnd_5378] using wordTrace_append hprefix tailTrace_5378
  have hstable : (prefixWord ++ tailWord_5378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378).length < 2 ^ (prefixWord ++ tailWord_5378).sum := by decide
  have hdescent : baseEnd_5378 < baseStart_5378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5416 : List Nat := [2, 1, 5, 1, 2, 2, 3, 3]
def baseStart_5416 : Nat := 118140960795 + 5416 * 2 ^ 59
def prefixEnd_5416 : Nat := 4983230072969 + 3 ^ 40 * 5416 * 2
def baseEnd_5416 : Nat := 1648006651766544340799

theorem tailTrace_5416 : CollatzResearch.WordTrace tailWord_5416 prefixEnd_5416 1648006651766544340799 := by
  unfold tailWord_5416
  simp only [CollatzResearch.WordTrace]
  refine ⟨98768874193115912134051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131691832257487882845401 98768874193115912134051)
  ·
    refine ⟨148153311289673868201077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98768874193115912134051 148153311289673868201077)
    ·
      refine ⟨13889372933406925143851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148153311289673868201077 13889372933406925143851)
      ·
        refine ⟨20834059400110387715777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13889372933406925143851 20834059400110387715777)
        ·
          refine ⟨15625544550082790786833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20834059400110387715777 15625544550082790786833)
          ·
            refine ⟨11719158412562093090125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15625544550082790786833 11719158412562093090125)
            ·
              refine ⟨4394684404710784908797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11719158412562093090125 4394684404710784908797)
              ·
                refine ⟨1648006651766544340799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4394684404710784908797 1648006651766544340799)
                ·
                  rfl

theorem cell19_5416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_5416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5416 prefixEnd_5416 := by exact prefixLift 5416
  have htrace : WordTrace (prefixWord ++ tailWord_5416) baseStart_5416 baseEnd_5416 := by
    simpa [prefixWord, tailWord_5416, baseEnd_5416] using wordTrace_append hprefix tailTrace_5416
  have hstable : (prefixWord ++ tailWord_5416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5416).length < 2 ^ (prefixWord ++ tailWord_5416).sum := by decide
  have hdescent : baseEnd_5416 < baseStart_5416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439 : List Nat := [1, 1, 2, 2, 4, 3, 6]
def baseStart_5439 : Nat := 118140960795 + 5439 * 2 ^ 59
def prefixEnd_5439 : Nat := 4983230072969 + 3 ^ 40 * 5439 * 2
def baseEnd_5439 : Nat := 551668400969768609875

theorem tailTrace_5439 : CollatzResearch.WordTrace tailWord_5439 prefixEnd_5439 551668400969768609875 := by
  unfold tailWord_5439
  simp only [CollatzResearch.WordTrace]
  refine ⟨198376627302906752355371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132251084868604501570247 198376627302906752355371)
  ·
    refine ⟨297564940954360128533057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198376627302906752355371 297564940954360128533057)
    ·
      refine ⟨223173705715770096399793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297564940954360128533057 223173705715770096399793)
      ·
        refine ⟨167380279286827572299845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223173705715770096399793 167380279286827572299845)
        ·
          refine ⟨31383802366280169806221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167380279286827572299845 31383802366280169806221)
          ·
            refine ⟨11768925887355063677333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31383802366280169806221 11768925887355063677333)
            ·
              refine ⟨551668400969768609875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11768925887355063677333 551668400969768609875)
              ·
                rfl

theorem cell19_5439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 6].length) (baseStart_5439 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5439 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5439 prefixEnd_5439 := by exact prefixLift 5439
  have htrace : WordTrace (prefixWord ++ tailWord_5439) baseStart_5439 baseEnd_5439 := by
    simpa [prefixWord, tailWord_5439, baseEnd_5439] using wordTrace_append hprefix tailTrace_5439
  have hstable : (prefixWord ++ tailWord_5439).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439).length < 2 ^ (prefixWord ++ tailWord_5439).sum := by decide
  have hdescent : baseEnd_5439 < baseStart_5439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458 : List Nat := [3, 2, 2, 1, 1, 1, 1, 8]
def baseStart_5458 : Nat := 118140960795 + 5458 * 2 ^ 59
def prefixEnd_5458 : Nat := 4983230072969 + 3 ^ 40 * 5458 * 2
def baseEnd_5458 : Nat := 1660786614722891407351

theorem tailTrace_5458 : CollatzResearch.WordTrace tailWord_5458 prefixEnd_5458 1660786614722891407351 := by
  unfold tailWord_5458
  simp only [CollatzResearch.WordTrace]
  refine ⟨49767403558518249324257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132713076156048664864685 49767403558518249324257)
  ·
    refine ⟨37325552668888686993193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49767403558518249324257 37325552668888686993193)
    ·
      refine ⟨27994164501666515244895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37325552668888686993193 27994164501666515244895)
      ·
        refine ⟨41991246752499772867343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27994164501666515244895 41991246752499772867343)
        ·
          refine ⟨62986870128749659301015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41991246752499772867343 62986870128749659301015)
          ·
            refine ⟨94480305193124488951523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62986870128749659301015 94480305193124488951523)
            ·
              refine ⟨141720457789686733427285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94480305193124488951523 141720457789686733427285)
              ·
                refine ⟨1660786614722891407351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 141720457789686733427285 1660786614722891407351)
                ·
                  rfl

theorem cell19_5458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_5458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5458 prefixEnd_5458 := by exact prefixLift 5458
  have htrace : WordTrace (prefixWord ++ tailWord_5458) baseStart_5458 baseEnd_5458 := by
    simpa [prefixWord, tailWord_5458, baseEnd_5458] using wordTrace_append hprefix tailTrace_5458
  have hstable : (prefixWord ++ tailWord_5458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458).length < 2 ^ (prefixWord ++ tailWord_5458).sum := by decide
  have hdescent : baseEnd_5458 < baseStart_5458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475 : List Nat := [1, 1, 1, 5, 2, 2, 4, 3]
def baseStart_5475 : Nat := 118140960795 + 5475 * 2 ^ 59
def prefixEnd_5475 : Nat := 4983230072969 + 3 ^ 40 * 5475 * 2
def baseEnd_5475 : Nat := 1665959456871889029527

theorem tailTrace_5475 : CollatzResearch.WordTrace tailWord_5475 prefixEnd_5475 1665959456871889029527 := by
  unfold tailWord_5475
  simp only [CollatzResearch.WordTrace]
  refine ⟨199689655172484900665879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133126436781656600443919 199689655172484900665879)
  ·
    refine ⟨299534482758727350998819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199689655172484900665879 299534482758727350998819)
    ·
      refine ⟨449301724138091026498229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299534482758727350998819 449301724138091026498229)
      ·
        refine ⟨42122036637946033734209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 449301724138091026498229 42122036637946033734209)
        ·
          refine ⟨31591527478459525300657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42122036637946033734209 31591527478459525300657)
          ·
            refine ⟨23693645608844643975493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31591527478459525300657 23693645608844643975493)
            ·
              refine ⟨4442558551658370745405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23693645608844643975493 4442558551658370745405)
              ·
                refine ⟨1665959456871889029527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4442558551658370745405 1665959456871889029527)
                ·
                  rfl

theorem cell19_5475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 3].length) (baseStart_5475 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5475 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5475 prefixEnd_5475 := by exact prefixLift 5475
  have htrace : WordTrace (prefixWord ++ tailWord_5475) baseStart_5475 baseEnd_5475 := by
    simpa [prefixWord, tailWord_5475, baseEnd_5475] using wordTrace_append hprefix tailTrace_5475
  have hstable : (prefixWord ++ tailWord_5475).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475).length < 2 ^ (prefixWord ++ tailWord_5475).sum := by decide
  have hdescent : baseEnd_5475 < baseStart_5475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477 : List Nat := [1, 3, 1, 3, 1, 2, 3, 5]
def baseStart_5477 : Nat := 118140960795 + 5477 * 2 ^ 59
def prefixEnd_5477 : Nat := 4983230072969 + 3 ^ 40 * 5477 * 2
def baseEnd_5477 : Nat := 1666568026536476985077

theorem tailTrace_5477 : CollatzResearch.WordTrace tailWord_5477 prefixEnd_5477 1666568026536476985077 := by
  unfold tailWord_5477
  simp only [CollatzResearch.WordTrace]
  refine ⟨199762601165239242238685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133175067443492828159123 199762601165239242238685)
  ·
    refine ⟨74910975436964715839507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199762601165239242238685 74910975436964715839507)
    ·
      refine ⟨112366463155447073759261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74910975436964715839507 112366463155447073759261)
      ·
        refine ⟨42137423683292652659723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112366463155447073759261 42137423683292652659723)
        ·
          refine ⟨63206135524938978989585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42137423683292652659723 63206135524938978989585)
          ·
            refine ⟨47404601643704234242189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63206135524938978989585 47404601643704234242189)
            ·
              refine ⟨17776725616389087840821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47404601643704234242189 17776725616389087840821)
              ·
                refine ⟨1666568026536476985077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17776725616389087840821 1666568026536476985077)
                ·
                  rfl

theorem cell19_5477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_5477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5477 prefixEnd_5477 := by exact prefixLift 5477
  have htrace : WordTrace (prefixWord ++ tailWord_5477) baseStart_5477 baseEnd_5477 := by
    simpa [prefixWord, tailWord_5477, baseEnd_5477] using wordTrace_append hprefix tailTrace_5477
  have hstable : (prefixWord ++ tailWord_5477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477).length < 2 ^ (prefixWord ++ tailWord_5477).sum := by decide
  have hdescent : baseEnd_5477 < baseStart_5477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5513 : List Nat := [1, 2, 1, 1, 7, 1, 2, 4]
def baseStart_5513 : Nat := 118140960795 + 5513 * 2 ^ 59
def prefixEnd_5513 : Nat := 4983230072969 + 3 ^ 40 * 5513 * 2
def baseEnd_5513 : Nat := 1677522280499060184979

theorem tailTrace_5513 : CollatzResearch.WordTrace tailWord_5513 prefixEnd_5513 1677522280499060184979 := by
  unfold tailWord_5513
  simp only [CollatzResearch.WordTrace]
  refine ⟨201075629034817390549193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134050419356544927032795 201075629034817390549193)
  ·
    refine ⟨150806721776113042911895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201075629034817390549193 150806721776113042911895)
    ·
      refine ⟨226210082664169564367843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150806721776113042911895 226210082664169564367843)
      ·
        refine ⟨339315123996254346551765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226210082664169564367843 339315123996254346551765)
        ·
          refine ⟨7952698218662211247307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 339315123996254346551765 7952698218662211247307)
          ·
            refine ⟨11929047327993316870961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7952698218662211247307 11929047327993316870961)
            ·
              refine ⟨8946785495994987653221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11929047327993316870961 8946785495994987653221)
              ·
                refine ⟨1677522280499060184979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8946785495994987653221 1677522280499060184979)
                ·
                  rfl

theorem cell19_5513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_5513 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5513 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5513 prefixEnd_5513 := by exact prefixLift 5513
  have htrace : WordTrace (prefixWord ++ tailWord_5513) baseStart_5513 baseEnd_5513 := by
    simpa [prefixWord, tailWord_5513, baseEnd_5513] using wordTrace_append hprefix tailTrace_5513
  have hstable : (prefixWord ++ tailWord_5513).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5513).length < 2 ^ (prefixWord ++ tailWord_5513).sum := by decide
  have hdescent : baseEnd_5513 < baseStart_5513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515 : List Nat := [1, 1, 1, 1, 4, 3, 4, 4]
def baseStart_5515 : Nat := 118140960795 + 5515 * 2 ^ 59
def prefixEnd_5515 : Nat := 4983230072969 + 3 ^ 40 * 5515 * 2
def baseEnd_5515 : Nat := 1678130850163648140529

theorem tailTrace_5515 : CollatzResearch.WordTrace tailWord_5515 prefixEnd_5515 1678130850163648140529 := by
  unfold tailWord_5515
  simp only [CollatzResearch.WordTrace]
  refine ⟨201148575027571732121999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134099050018381154747999 201148575027571732121999)
  ·
    refine ⟨301722862541357598182999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201148575027571732121999 301722862541357598182999)
    ·
      refine ⟨452584293812036397274499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301722862541357598182999 452584293812036397274499)
      ·
        refine ⟨678876440718054595911749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452584293812036397274499 678876440718054595911749)
        ·
          refine ⟨127289332634635236733453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 678876440718054595911749 127289332634635236733453)
          ·
            refine ⟨47733499737988213775045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127289332634635236733453 47733499737988213775045)
            ·
              refine ⟨8950031200872790082821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47733499737988213775045 8950031200872790082821)
              ·
                refine ⟨1678130850163648140529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8950031200872790082821 1678130850163648140529)
                ·
                  rfl

theorem cell19_5515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_5515 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5515 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5515 prefixEnd_5515 := by exact prefixLift 5515
  have htrace : WordTrace (prefixWord ++ tailWord_5515) baseStart_5515 baseEnd_5515 := by
    simpa [prefixWord, tailWord_5515, baseEnd_5515] using wordTrace_append hprefix tailTrace_5515
  have hstable : (prefixWord ++ tailWord_5515).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515).length < 2 ^ (prefixWord ++ tailWord_5515).sum := by decide
  have hdescent : baseEnd_5515 < baseStart_5515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5589 : List Nat := [1, 3, 2, 3, 1, 1, 5, 3]
def baseStart_5589 : Nat := 118140960795 + 5589 * 2 ^ 59
def prefixEnd_5589 : Nat := 4983230072969 + 3 ^ 40 * 5589 * 2
def baseEnd_5589 : Nat := 1700647927753402495883

theorem tailTrace_5589 : CollatzResearch.WordTrace tailWord_5589 prefixEnd_5589 1700647927753402495883 := by
  unfold tailWord_5589
  simp only [CollatzResearch.WordTrace]
  refine ⟨203847576759482370315821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135898384506321580210547 203847576759482370315821)
  ·
    refine ⟨76442841284805888868433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203847576759482370315821 76442841284805888868433)
    ·
      refine ⟨57332130963604416651325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76442841284805888868433 57332130963604416651325)
      ·
        refine ⟨21499549111351656244247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57332130963604416651325 21499549111351656244247)
        ·
          refine ⟨32249323667027484366371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21499549111351656244247 32249323667027484366371)
          ·
            refine ⟨48373985500541226549557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32249323667027484366371 48373985500541226549557)
            ·
              refine ⟨4535061140675739989021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48373985500541226549557 4535061140675739989021)
              ·
                refine ⟨1700647927753402495883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4535061140675739989021 1700647927753402495883)
                ·
                  rfl

theorem cell19_5589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 3].length) (baseStart_5589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5589 prefixEnd_5589 := by exact prefixLift 5589
  have htrace : WordTrace (prefixWord ++ tailWord_5589) baseStart_5589 baseEnd_5589 := by
    simpa [prefixWord, tailWord_5589, baseEnd_5589] using wordTrace_append hprefix tailTrace_5589
  have hstable : (prefixWord ++ tailWord_5589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5589).length < 2 ^ (prefixWord ++ tailWord_5589).sum := by decide
  have hdescent : baseEnd_5589 < baseStart_5589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5638 : List Nat := [6, 2, 1, 1, 2, 2, 2, 3]
def baseStart_5638 : Nat := 118140960795 + 5638 * 2 ^ 59
def prefixEnd_5638 : Nat := 4983230072969 + 3 ^ 40 * 5638 * 2
def baseEnd_5638 : Nat := 1715557884535807406861

theorem tailTrace_5638 : CollatzResearch.WordTrace tailWord_5638 prefixEnd_5638 1715557884535807406861 := by
  unfold tailWord_5638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6426086049436366839049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 137089835721309159233045 6426086049436366839049)
  ·
    refine ⟨4819564537077275129287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6426086049436366839049 4819564537077275129287)
    ·
      refine ⟨7229346805615912693931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4819564537077275129287 7229346805615912693931)
      ·
        refine ⟨10844020208423869040897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7229346805615912693931 10844020208423869040897)
        ·
          refine ⟨8133015156317901780673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10844020208423869040897 8133015156317901780673)
          ·
            refine ⟨6099761367238426335505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8133015156317901780673 6099761367238426335505)
            ·
              refine ⟨4574821025428819751629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6099761367238426335505 4574821025428819751629)
              ·
                refine ⟨1715557884535807406861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4574821025428819751629 1715557884535807406861)
                ·
                  rfl

theorem cell19_5638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_5638 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5638 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5638 prefixEnd_5638 := by exact prefixLift 5638
  have htrace : WordTrace (prefixWord ++ tailWord_5638) baseStart_5638 baseEnd_5638 := by
    simpa [prefixWord, tailWord_5638, baseEnd_5638] using wordTrace_append hprefix tailTrace_5638
  have hstable : (prefixWord ++ tailWord_5638).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5638).length < 2 ^ (prefixWord ++ tailWord_5638).sum := by decide
  have hdescent : baseEnd_5638 < baseStart_5638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644 : List Nat := [2, 2, 1, 2, 5, 2, 2, 3]
def baseStart_5644 : Nat := 118140960795 + 5644 * 2 ^ 59
def prefixEnd_5644 : Nat := 4983230072969 + 3 ^ 40 * 5644 * 2
def baseEnd_5644 : Nat := 1717383593529571273511

theorem tailTrace_5644 : CollatzResearch.WordTrace tailWord_5644 prefixEnd_5644 1717383593529571273511 := by
  unfold tailWord_5644
  simp only [CollatzResearch.WordTrace]
  refine ⟨102926795780113381783993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137235727706817842378657 102926795780113381783993)
  ·
    refine ⟨77195096835085036337995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102926795780113381783993 77195096835085036337995)
    ·
      refine ⟨115792645252627554506993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77195096835085036337995 115792645252627554506993)
      ·
        refine ⟨86844483939470665880245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115792645252627554506993 86844483939470665880245)
        ·
          refine ⟨8141670369325374926273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86844483939470665880245 8141670369325374926273)
          ·
            refine ⟨6106252776994031194705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8141670369325374926273 6106252776994031194705)
            ·
              refine ⟨4579689582745523396029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6106252776994031194705 4579689582745523396029)
              ·
                refine ⟨1717383593529571273511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4579689582745523396029 1717383593529571273511)
                ·
                  rfl

theorem cell19_5644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_5644 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5644 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5644 prefixEnd_5644 := by exact prefixLift 5644
  have htrace : WordTrace (prefixWord ++ tailWord_5644) baseStart_5644 baseEnd_5644 := by
    simpa [prefixWord, tailWord_5644, baseEnd_5644] using wordTrace_append hprefix tailTrace_5644
  have hstable : (prefixWord ++ tailWord_5644).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644).length < 2 ^ (prefixWord ++ tailWord_5644).sum := by decide
  have hdescent : baseEnd_5644 < baseStart_5644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646 : List Nat := [4, 1, 1, 2, 4, 1, 1, 5]
def baseStart_5646 : Nat := 118140960795 + 5646 * 2 ^ 59
def prefixEnd_5646 : Nat := 4983230072969 + 3 ^ 40 * 5646 * 2
def baseEnd_5646 : Nat := 1717992163194159229061

theorem tailTrace_5646 : CollatzResearch.WordTrace tailWord_5646 prefixEnd_5646 1717992163194159229061 := by
  unfold tailWord_5646
  simp only [CollatzResearch.WordTrace]
  refine ⟨25740817194122638142599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137284358368654070093861 25740817194122638142599)
  ·
    refine ⟨38611225791183957213899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25740817194122638142599 38611225791183957213899)
    ·
      refine ⟨57916838686775935820849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38611225791183957213899 57916838686775935820849)
      ·
        refine ⟨43437629015081951865637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57916838686775935820849 43437629015081951865637)
        ·
          refine ⟨8144555440327865974807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43437629015081951865637 8144555440327865974807)
          ·
            refine ⟨12216833160491798962211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8144555440327865974807 12216833160491798962211)
            ·
              refine ⟨18325249740737698443317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12216833160491798962211 18325249740737698443317)
              ·
                refine ⟨1717992163194159229061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18325249740737698443317 1717992163194159229061)
                ·
                  rfl

theorem cell19_5646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_5646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5646 prefixEnd_5646 := by exact prefixLift 5646
  have htrace : WordTrace (prefixWord ++ tailWord_5646) baseStart_5646 baseEnd_5646 := by
    simpa [prefixWord, tailWord_5646, baseEnd_5646] using wordTrace_append hprefix tailTrace_5646
  have hstable : (prefixWord ++ tailWord_5646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646).length < 2 ^ (prefixWord ++ tailWord_5646).sum := by decide
  have hdescent : baseEnd_5646 < baseStart_5646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5718 : List Nat := [5, 2, 2, 2, 2, 6]
def baseStart_5718 : Nat := 118140960795 + 5718 * 2 ^ 59
def prefixEnd_5718 : Nat := 4983230072969 + 3 ^ 40 * 5718 * 2
def baseEnd_5718 : Nat := 193322296791036180985

theorem tailTrace_5718 : CollatzResearch.WordTrace tailWord_5718 prefixEnd_5718 193322296791036180985 := by
  unfold tailWord_5718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13034537080758587610113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139035062194758267841205 13034537080758587610113)
  ·
    refine ⟨9775902810568940707585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13034537080758587610113 9775902810568940707585)
    ·
      refine ⟨7331927107926705530689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9775902810568940707585 7331927107926705530689)
      ·
        refine ⟨5498945330945029148017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7331927107926705530689 5498945330945029148017)
        ·
          refine ⟨4124208998208771861013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5498945330945029148017 4124208998208771861013)
          ·
            refine ⟨193322296791036180985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4124208998208771861013 193322296791036180985)
            ·
              rfl

theorem cell19_5718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 6].length) (baseStart_5718 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5718 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5718 prefixEnd_5718 := by exact prefixLift 5718
  have htrace : WordTrace (prefixWord ++ tailWord_5718) baseStart_5718 baseEnd_5718 := by
    simpa [prefixWord, tailWord_5718, baseEnd_5718] using wordTrace_append hprefix tailTrace_5718
  have hstable : (prefixWord ++ tailWord_5718).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5718).length < 2 ^ (prefixWord ++ tailWord_5718).sum := by decide
  have hdescent : baseEnd_5718 < baseStart_5718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724 : List Nat := [2, 2, 4, 1, 2, 8]
def baseStart_5724 : Nat := 118140960795 + 5724 * 2 ^ 59
def prefixEnd_5724 : Nat := 4983230072969 + 3 ^ 40 * 5724 * 2
def baseEnd_5724 : Nat := 193525153345898832835

theorem tailTrace_5724 : CollatzResearch.WordTrace tailWord_5724 prefixEnd_5724 193525153345898832835 := by
  unfold tailWord_5724
  simp only [CollatzResearch.WordTrace]
  refine ⟨104385715635200213240113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139180954180266950986817 104385715635200213240113)
  ·
    refine ⟨78289286726400159930085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104385715635200213240113 78289286726400159930085)
    ·
      refine ⟨14679241261200029986891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78289286726400159930085 14679241261200029986891)
      ·
        refine ⟨22018861891800044980337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14679241261200029986891 22018861891800044980337)
        ·
          refine ⟨16514146418850033735253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22018861891800044980337 16514146418850033735253)
          ·
            refine ⟨193525153345898832835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 16514146418850033735253 193525153345898832835)
            ·
              rfl

theorem cell19_5724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 8].length) (baseStart_5724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5724 prefixEnd_5724 := by exact prefixLift 5724
  have htrace : WordTrace (prefixWord ++ tailWord_5724) baseStart_5724 baseEnd_5724 := by
    simpa [prefixWord, tailWord_5724, baseEnd_5724] using wordTrace_append hprefix tailTrace_5724
  have hstable : (prefixWord ++ tailWord_5724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724).length < 2 ^ (prefixWord ++ tailWord_5724).sum := by decide
  have hdescent : baseEnd_5724 < baseStart_5724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813 : List Nat := [1, 3, 3, 3, 3, 1, 2, 3]
def baseStart_5813 : Nat := 118140960795 + 5813 * 2 ^ 59
def prefixEnd_5813 : Nat := 4983230072969 + 3 ^ 40 * 5813 * 2
def baseEnd_5813 : Nat := 1768807730187253517495

theorem tailTrace_5813 : CollatzResearch.WordTrace tailWord_5813 prefixEnd_5813 1768807730187253517495 := by
  unfold tailWord_5813
  simp only [CollatzResearch.WordTrace]
  refine ⟨212017527947968626470093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141345018631979084313395 212017527947968626470093)
  ·
    refine ⟨79506572980488234926285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212017527947968626470093 79506572980488234926285)
    ·
      refine ⟨29814964867683088097357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79506572980488234926285 29814964867683088097357)
      ·
        refine ⟨11180611825381158036509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29814964867683088097357 11180611825381158036509)
        ·
          refine ⟨4192729434517934263691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11180611825381158036509 4192729434517934263691)
          ·
            refine ⟨6289094151776901395537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4192729434517934263691 6289094151776901395537)
            ·
              refine ⟨4716820613832676046653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6289094151776901395537 4716820613832676046653)
              ·
                refine ⟨1768807730187253517495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4716820613832676046653 1768807730187253517495)
                ·
                  rfl

theorem cell19_5813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 3].length) (baseStart_5813 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5813 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5813 prefixEnd_5813 := by exact prefixLift 5813
  have htrace : WordTrace (prefixWord ++ tailWord_5813) baseStart_5813 baseEnd_5813 := by
    simpa [prefixWord, tailWord_5813, baseEnd_5813] using wordTrace_append hprefix tailTrace_5813
  have hstable : (prefixWord ++ tailWord_5813).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813).length < 2 ^ (prefixWord ++ tailWord_5813).sum := by decide
  have hdescent : baseEnd_5813 < baseStart_5813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836 : List Nat := [2, 2, 1, 5, 2, 2, 5]
def baseStart_5836 : Nat := 118140960795 + 5836 * 2 ^ 59
def prefixEnd_5836 : Nat := 4983230072969 + 3 ^ 40 * 5836 * 2
def baseEnd_5836 : Nat := 591935427110005002107

theorem tailTrace_5836 : CollatzResearch.WordTrace tailWord_5836 prefixEnd_5836 591935427110005002107 := by
  unfold tailWord_5836
  simp only [CollatzResearch.WordTrace]
  refine ⟨106428203432321777278681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141904271243095703038241 106428203432321777278681)
  ·
    refine ⟨79821152574241332959011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106428203432321777278681 79821152574241332959011)
    ·
      refine ⟨119731728861361999438517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79821152574241332959011 119731728861361999438517)
      ·
        refine ⟨11224849580752687447361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119731728861361999438517 11224849580752687447361)
        ·
          refine ⟨8418637185564515585521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11224849580752687447361 8418637185564515585521)
          ·
            refine ⟨6313977889173386689141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8418637185564515585521 6313977889173386689141)
            ·
              refine ⟨591935427110005002107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6313977889173386689141 591935427110005002107)
              ·
                rfl

theorem cell19_5836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 5].length) (baseStart_5836 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5836 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5836 prefixEnd_5836 := by exact prefixLift 5836
  have htrace : WordTrace (prefixWord ++ tailWord_5836) baseStart_5836 baseEnd_5836 := by
    simpa [prefixWord, tailWord_5836, baseEnd_5836] using wordTrace_append hprefix tailTrace_5836
  have hstable : (prefixWord ++ tailWord_5836).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836).length < 2 ^ (prefixWord ++ tailWord_5836).sum := by decide
  have hdescent : baseEnd_5836 < baseStart_5836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5853 : List Nat := [1, 4, 3, 3, 1, 1, 2, 4]
def baseStart_5853 : Nat := 118140960795 + 5853 * 2 ^ 59
def prefixEnd_5853 : Nat := 4983230072969 + 3 ^ 40 * 5853 * 2
def baseEnd_5853 : Nat := 1780979123479012628497

theorem tailTrace_5853 : CollatzResearch.WordTrace tailWord_5853 prefixEnd_5853 1780979123479012628497 := by
  unfold tailWord_5853
  simp only [CollatzResearch.WordTrace]
  refine ⟨213476447803055457926213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142317631868703638617475 213476447803055457926213)
  ·
    refine ⟨40026833963072898361165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213476447803055457926213 40026833963072898361165)
    ·
      refine ⟨15010062736152336885437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40026833963072898361165 15010062736152336885437)
      ·
        refine ⟨5628773526057126332039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15010062736152336885437 5628773526057126332039)
        ·
          refine ⟨8443160289085689498059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5628773526057126332039 8443160289085689498059)
          ·
            refine ⟨12664740433628534247089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8443160289085689498059 12664740433628534247089)
            ·
              refine ⟨9498555325221400685317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12664740433628534247089 9498555325221400685317)
              ·
                refine ⟨1780979123479012628497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9498555325221400685317 1780979123479012628497)
                ·
                  rfl

theorem cell19_5853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 4].length) (baseStart_5853 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5853 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5853 prefixEnd_5853 := by exact prefixLift 5853
  have htrace : WordTrace (prefixWord ++ tailWord_5853) baseStart_5853 baseEnd_5853 := by
    simpa [prefixWord, tailWord_5853, baseEnd_5853] using wordTrace_append hprefix tailTrace_5853
  have hstable : (prefixWord ++ tailWord_5853).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5853).length < 2 ^ (prefixWord ++ tailWord_5853).sum := by decide
  have hdescent : baseEnd_5853 < baseStart_5853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5895 : List Nat := [1, 1, 4, 4, 2, 7]
def baseStart_5895 : Nat := 118140960795 + 5895 * 2 ^ 59
def prefixEnd_5895 : Nat := 4983230072969 + 3 ^ 40 * 5895 * 2
def baseEnd_5895 : Nat := 199306565159484410561

theorem tailTrace_5895 : CollatzResearch.WordTrace tailWord_5895 prefixEnd_5895 199306565159484410561 := by
  unfold tailWord_5895
  simp only [CollatzResearch.WordTrace]
  refine ⟨215008313650896630955139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143338875767264420636759 215008313650896630955139)
  ·
    refine ⟨322512470476344946432709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215008313650896630955139 322512470476344946432709)
    ·
      refine ⟨60471088214314677456133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 322512470476344946432709 60471088214314677456133)
      ·
        refine ⟨11338329040184002023025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60471088214314677456133 11338329040184002023025)
        ·
          refine ⟨8503746780138001517269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11338329040184002023025 8503746780138001517269)
          ·
            refine ⟨199306565159484410561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 8503746780138001517269 199306565159484410561)
            ·
              rfl

theorem cell19_5895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 7].length) (baseStart_5895 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5895 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5895 prefixEnd_5895 := by exact prefixLift 5895
  have htrace : WordTrace (prefixWord ++ tailWord_5895) baseStart_5895 baseEnd_5895 := by
    simpa [prefixWord, tailWord_5895, baseEnd_5895] using wordTrace_append hprefix tailTrace_5895
  have hstable : (prefixWord ++ tailWord_5895).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5895).length < 2 ^ (prefixWord ++ tailWord_5895).sum := by decide
  have hdescent : baseEnd_5895 < baseStart_5895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914 : List Nat := [3, 1, 1, 3, 2, 2, 3, 4]
def baseStart_5914 : Nat := 118140960795 + 5914 * 2 ^ 59
def prefixEnd_5914 : Nat := 4983230072969 + 3 ^ 40 * 5914 * 2
def baseEnd_5914 : Nat := 1799540498248945272775

theorem tailTrace_5914 : CollatzResearch.WordTrace tailWord_5914 prefixEnd_5914 1799540498248945272775 := by
  unfold tailWord_5914
  simp only [CollatzResearch.WordTrace]
  refine ⟨53925325145515718974199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143800867054708583931197 53925325145515718974199)
  ·
    refine ⟨80887987718273578461299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53925325145515718974199 80887987718273578461299)
    ·
      refine ⟨121331981577410367691949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80887987718273578461299 121331981577410367691949)
      ·
        refine ⟨45499493091528887884481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121331981577410367691949 45499493091528887884481)
        ·
          refine ⟨34124619818646665913361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45499493091528887884481 34124619818646665913361)
          ·
            refine ⟨25593464863984999435021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34124619818646665913361 25593464863984999435021)
            ·
              refine ⟨9597549323994374788133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25593464863984999435021 9597549323994374788133)
              ·
                refine ⟨1799540498248945272775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9597549323994374788133 1799540498248945272775)
                ·
                  rfl

theorem cell19_5914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_5914 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5914 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5914 prefixEnd_5914 := by exact prefixLift 5914
  have htrace : WordTrace (prefixWord ++ tailWord_5914) baseStart_5914 baseEnd_5914 := by
    simpa [prefixWord, tailWord_5914, baseEnd_5914] using wordTrace_append hprefix tailTrace_5914
  have hstable : (prefixWord ++ tailWord_5914).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914).length < 2 ^ (prefixWord ++ tailWord_5914).sum := by decide
  have hdescent : baseEnd_5914 < baseStart_5914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5986 : List Nat := [3, 3, 2, 1, 2, 3, 2, 3]
def baseStart_5986 : Nat := 118140960795 + 5986 * 2 ^ 59
def prefixEnd_5986 : Nat := 4983230072969 + 3 ^ 40 * 5986 * 2
def baseEnd_5986 : Nat := 1821449006174111672579

theorem tailTrace_5986 : CollatzResearch.WordTrace tailWord_5986 prefixEnd_5986 1821449006174111672579 := by
  unfold tailWord_5986
  simp only [CollatzResearch.WordTrace]
  refine ⟨54581839080304793129453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145551570880812781678541 54581839080304793129453)
  ·
    refine ⟨20468189655114297423545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54581839080304793129453 20468189655114297423545)
    ·
      refine ⟨15351142241335723067659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20468189655114297423545 15351142241335723067659)
      ·
        refine ⟨23026713362003584601489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15351142241335723067659 23026713362003584601489)
        ·
          refine ⟨17270035021502688451117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23026713362003584601489 17270035021502688451117)
          ·
            refine ⟨6476263133063508169169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17270035021502688451117 6476263133063508169169)
            ·
              refine ⟨4857197349797631126877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6476263133063508169169 4857197349797631126877)
              ·
                refine ⟨1821449006174111672579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4857197349797631126877 1821449006174111672579)
                ·
                  rfl

theorem cell19_5986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_5986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_5986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_5986 prefixEnd_5986 := by exact prefixLift 5986
  have htrace : WordTrace (prefixWord ++ tailWord_5986) baseStart_5986 baseEnd_5986 := by
    simpa [prefixWord, tailWord_5986, baseEnd_5986] using wordTrace_append hprefix tailTrace_5986
  have hstable : (prefixWord ++ tailWord_5986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5986).length < 2 ^ (prefixWord ++ tailWord_5986).sum := by decide
  have hdescent : baseEnd_5986 < baseStart_5986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6026 : List Nat := [3, 1, 2, 4, 2, 1, 2, 4]
def baseStart_6026 : Nat := 118140960795 + 6026 * 2 ^ 59
def prefixEnd_6026 : Nat := 4983230072969 + 3 ^ 40 * 6026 * 2
def baseEnd_6026 : Nat := 1833620399465870783581

theorem tailTrace_6026 : CollatzResearch.WordTrace tailWord_6026 prefixEnd_6026 1833620399465870783581 := by
  unfold tailWord_6026
  simp only [CollatzResearch.WordTrace]
  refine ⟨54946569044076500993483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146524184117537335982621 54946569044076500993483)
  ·
    refine ⟨82419853566114751490225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54946569044076500993483 82419853566114751490225)
    ·
      refine ⟨61814890174586063617669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82419853566114751490225 61814890174586063617669)
      ·
        refine ⟨11590291907734886928313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61814890174586063617669 11590291907734886928313)
        ·
          refine ⟨8692718930801165196235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11590291907734886928313 8692718930801165196235)
          ·
            refine ⟨13039078396201747794353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8692718930801165196235 13039078396201747794353)
            ·
              refine ⟨9779308797151310845765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13039078396201747794353 9779308797151310845765)
              ·
                refine ⟨1833620399465870783581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9779308797151310845765 1833620399465870783581)
                ·
                  rfl

theorem cell19_6026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_6026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6026 prefixEnd_6026 := by exact prefixLift 6026
  have htrace : WordTrace (prefixWord ++ tailWord_6026) baseStart_6026 baseEnd_6026 := by
    simpa [prefixWord, tailWord_6026, baseEnd_6026] using wordTrace_append hprefix tailTrace_6026
  have hstable : (prefixWord ++ tailWord_6026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6026).length < 2 ^ (prefixWord ++ tailWord_6026).sum := by decide
  have hdescent : baseEnd_6026 < baseStart_6026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062 : List Nat := [4, 1, 5, 1, 1, 7]
def baseStart_6062 : Nat := 118140960795 + 6062 * 2 ^ 59
def prefixEnd_6062 : Nat := 4983230072969 + 3 ^ 40 * 6062 * 2
def baseEnd_6062 : Nat := 204952739269828220387

theorem tailTrace_6062 : CollatzResearch.WordTrace tailWord_6062 prefixEnd_6062 204952739269828220387 := by
  unfold tailWord_6062
  simp only [CollatzResearch.WordTrace]
  refine ⟨27637413005735519035555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147399536030589434856293 27637413005735519035555)
  ·
    refine ⟨41456119508603278553333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27637413005735519035555 41456119508603278553333)
    ·
      refine ⟨3886511203931557364375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41456119508603278553333 3886511203931557364375)
      ·
        refine ⟨5829766805897336046563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3886511203931557364375 5829766805897336046563)
        ·
          refine ⟨8744650208846004069845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5829766805897336046563 8744650208846004069845)
          ·
            refine ⟨204952739269828220387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 8744650208846004069845 204952739269828220387)
            ·
              rfl

theorem cell19_6062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 7].length) (baseStart_6062 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6062 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6062 prefixEnd_6062 := by exact prefixLift 6062
  have htrace : WordTrace (prefixWord ++ tailWord_6062) baseStart_6062 baseEnd_6062 := by
    simpa [prefixWord, tailWord_6062, baseEnd_6062] using wordTrace_append hprefix tailTrace_6062
  have hstable : (prefixWord ++ tailWord_6062).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062).length < 2 ^ (prefixWord ++ tailWord_6062).sum := by decide
  have hdescent : baseEnd_6062 < baseStart_6062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104 : List Nat := [2, 1, 2, 2, 2, 2, 5, 3]
def baseStart_6104 : Nat := 118140960795 + 6104 * 2 ^ 59
def prefixEnd_6104 : Nat := 4983230072969 + 3 ^ 40 * 6104 * 2
def baseEnd_6104 : Nat := 1857354616384801050035

theorem tailTrace_6104 : CollatzResearch.WordTrace tailWord_6104 prefixEnd_6104 1857354616384801050035 := by
  unfold tailWord_6104
  simp only [CollatzResearch.WordTrace]
  refine ⟨111315584946862662656683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148420779929150216875577 111315584946862662656683)
  ·
    refine ⟨166973377420293993985025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111315584946862662656683 166973377420293993985025)
    ·
      refine ⟨125230033065220495488769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166973377420293993985025 125230033065220495488769)
      ·
        refine ⟨93922524798915371616577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125230033065220495488769 93922524798915371616577)
        ·
          refine ⟨70441893599186528712433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93922524798915371616577 70441893599186528712433)
          ·
            refine ⟨52831420199389896534325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70441893599186528712433 52831420199389896534325)
            ·
              refine ⟨4952945643692802800093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52831420199389896534325 4952945643692802800093)
              ·
                refine ⟨1857354616384801050035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4952945643692802800093 1857354616384801050035)
                ·
                  rfl

theorem cell19_6104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_6104 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6104 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6104 prefixEnd_6104 := by exact prefixLift 6104
  have htrace : WordTrace (prefixWord ++ tailWord_6104) baseStart_6104 baseEnd_6104 := by
    simpa [prefixWord, tailWord_6104, baseEnd_6104] using wordTrace_append hprefix tailTrace_6104
  have hstable : (prefixWord ++ tailWord_6104).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104).length < 2 ^ (prefixWord ++ tailWord_6104).sum := by decide
  have hdescent : baseEnd_6104 < baseStart_6104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220 : List Nat := [2, 2, 1, 3, 1, 1, 4, 5]
def baseStart_6220 : Nat := 118140960795 + 6220 * 2 ^ 59
def prefixEnd_6220 : Nat := 4983230072969 + 3 ^ 40 * 6220 * 2
def baseEnd_6220 : Nat := 1892651656930902471941

theorem tailTrace_6220 : CollatzResearch.WordTrace tailWord_6220 prefixEnd_6220 1892651656930902471941 := by
  unfold tailWord_6220
  simp only [CollatzResearch.WordTrace]
  refine ⟨113431018736738568268057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151241358315651424357409 113431018736738568268057)
  ·
    refine ⟨85073264052553926201043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113431018736738568268057 85073264052553926201043)
    ·
      refine ⟨127609896078830889301565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85073264052553926201043 127609896078830889301565)
      ·
        refine ⟨47853711029561583488087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127609896078830889301565 47853711029561583488087)
        ·
          refine ⟨71780566544342375232131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47853711029561583488087 71780566544342375232131)
          ·
            refine ⟨107670849816513562848197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71780566544342375232131 107670849816513562848197)
            ·
              refine ⟨20188284340596293034037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107670849816513562848197 20188284340596293034037)
              ·
                refine ⟨1892651656930902471941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20188284340596293034037 1892651656930902471941)
                ·
                  rfl

theorem cell19_6220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_6220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6220 prefixEnd_6220 := by exact prefixLift 6220
  have htrace : WordTrace (prefixWord ++ tailWord_6220) baseStart_6220 baseEnd_6220 := by
    simpa [prefixWord, tailWord_6220, baseEnd_6220] using wordTrace_append hprefix tailTrace_6220
  have hstable : (prefixWord ++ tailWord_6220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220).length < 2 ^ (prefixWord ++ tailWord_6220).sum := by decide
  have hdescent : baseEnd_6220 < baseStart_6220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237 : List Nat := [1, 4, 4, 1, 1, 8]
def baseStart_6237 : Nat := 118140960795 + 6237 * 2 ^ 59
def prefixEnd_6237 : Nat := 4983230072969 + 3 ^ 40 * 6237 * 2
def baseEnd_6237 : Nat := 210869388786655566013

theorem tailTrace_6237 : CollatzResearch.WordTrace tailWord_6237 prefixEnd_6237 210869388786655566013 := by
  unfold tailWord_6237
  simp only [CollatzResearch.WordTrace]
  refine ⟨227482078411889039904965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151654718941259359936643 227482078411889039904965)
  ·
    refine ⟨42652889702229194982181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227482078411889039904965 42652889702229194982181)
    ·
      refine ⟨7997416819167974059159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42652889702229194982181 7997416819167974059159)
      ·
        refine ⟨11996125228751961088739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7997416819167974059159 11996125228751961088739)
        ·
          refine ⟨17994187843127941633109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11996125228751961088739 17994187843127941633109)
          ·
            refine ⟨210869388786655566013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 17994187843127941633109 210869388786655566013)
            ·
              rfl

theorem cell19_6237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 8].length) (baseStart_6237 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6237 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6237 prefixEnd_6237 := by exact prefixLift 6237
  have htrace : WordTrace (prefixWord ++ tailWord_6237) baseStart_6237 baseEnd_6237 := by
    simpa [prefixWord, tailWord_6237, baseEnd_6237] using wordTrace_append hprefix tailTrace_6237
  have hstable : (prefixWord ++ tailWord_6237).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237).length < 2 ^ (prefixWord ++ tailWord_6237).sum := by decide
  have hdescent : baseEnd_6237 < baseStart_6237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256 : List Nat := [2, 1, 1, 1, 5, 4, 1, 4]
def baseStart_6256 : Nat := 118140960795 + 6256 * 2 ^ 59
def prefixEnd_6256 : Nat := 4983230072969 + 3 ^ 40 * 6256 * 2
def baseEnd_6256 : Nat := 1903605910893485671843

theorem tailTrace_6256 : CollatzResearch.WordTrace tailWord_6256 prefixEnd_6256 1903605910893485671843 := by
  unfold tailWord_6256
  simp only [CollatzResearch.WordTrace]
  refine ⟨114087532671527642423311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152116710228703523231081 114087532671527642423311)
  ·
    refine ⟨171131299007291463634967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114087532671527642423311 171131299007291463634967)
    ·
      refine ⟨256696948510937195452451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171131299007291463634967 256696948510937195452451)
      ·
        refine ⟨385045422766405793178677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256696948510937195452451 385045422766405793178677)
        ·
          refine ⟨36098008384350543110501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 385045422766405793178677 36098008384350543110501)
          ·
            refine ⟨6768376572065726833219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36098008384350543110501 6768376572065726833219)
            ·
              refine ⟨10152564858098590249829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6768376572065726833219 10152564858098590249829)
              ·
                refine ⟨1903605910893485671843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10152564858098590249829 1903605910893485671843)
                ·
                  rfl

theorem cell19_6256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_6256 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6256 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6256 prefixEnd_6256 := by exact prefixLift 6256
  have htrace : WordTrace (prefixWord ++ tailWord_6256) baseStart_6256 baseEnd_6256 := by
    simpa [prefixWord, tailWord_6256, baseEnd_6256] using wordTrace_append hprefix tailTrace_6256
  have hstable : (prefixWord ++ tailWord_6256).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256).length < 2 ^ (prefixWord ++ tailWord_6256).sum := by decide
  have hdescent : baseEnd_6256 < baseStart_6256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273 : List Nat := [1, 2, 4, 2, 3, 1, 3, 3]
def baseStart_6273 : Nat := 118140960795 + 6273 * 2 ^ 59
def prefixEnd_6273 : Nat := 4983230072969 + 3 ^ 40 * 6273 * 2
def baseEnd_6273 : Nat := 1908778753042483294019

theorem tailTrace_6273 : CollatzResearch.WordTrace tailWord_6273 prefixEnd_6273 1908778753042483294019 := by
  unfold tailWord_6273
  simp only [CollatzResearch.WordTrace]
  refine ⟨228795106281467188215473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152530070854311458810315 228795106281467188215473)
  ·
    refine ⟨171596329711100391161605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228795106281467188215473 171596329711100391161605)
    ·
      refine ⟨32174311820831323342801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171596329711100391161605 32174311820831323342801)
      ·
        refine ⟨24130733865623492507101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32174311820831323342801 24130733865623492507101)
        ·
          refine ⟨9049025199608809690163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24130733865623492507101 9049025199608809690163)
          ·
            refine ⟨13573537799413214535245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9049025199608809690163 13573537799413214535245)
            ·
              refine ⟨5090076674779955450717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13573537799413214535245 5090076674779955450717)
              ·
                refine ⟨1908778753042483294019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5090076674779955450717 1908778753042483294019)
                ·
                  rfl

theorem cell19_6273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 3].length) (baseStart_6273 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6273 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6273 prefixEnd_6273 := by exact prefixLift 6273
  have htrace : WordTrace (prefixWord ++ tailWord_6273) baseStart_6273 baseEnd_6273 := by
    simpa [prefixWord, tailWord_6273, baseEnd_6273] using wordTrace_append hprefix tailTrace_6273
  have hstable : (prefixWord ++ tailWord_6273).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273).length < 2 ^ (prefixWord ++ tailWord_6273).sum := by decide
  have hdescent : baseEnd_6273 < baseStart_6273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275 : List Nat := [1, 1, 1, 3, 3, 4, 3, 3]
def baseStart_6275 : Nat := 118140960795 + 6275 * 2 ^ 59
def prefixEnd_6275 : Nat := 4983230072969 + 3 ^ 40 * 6275 * 2
def baseEnd_6275 : Nat := 1909387322707071249569

theorem tailTrace_6275 : CollatzResearch.WordTrace tailWord_6275 prefixEnd_6275 1909387322707071249569 := by
  unfold tailWord_6275
  simp only [CollatzResearch.WordTrace]
  refine ⟨228868052274221529788279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152578701516147686525519 228868052274221529788279)
  ·
    refine ⟨343302078411332294682419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228868052274221529788279 343302078411332294682419)
    ·
      refine ⟨514953117616998442023629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343302078411332294682419 514953117616998442023629)
      ·
        refine ⟨193107419106374415758861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 514953117616998442023629 193107419106374415758861)
        ·
          refine ⟨72415282164890405909573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193107419106374415758861 72415282164890405909573)
          ·
            refine ⟨13577865405916951108045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72415282164890405909573 13577865405916951108045)
            ·
              refine ⟨5091699527218856665517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13577865405916951108045 5091699527218856665517)
              ·
                refine ⟨1909387322707071249569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5091699527218856665517 1909387322707071249569)
                ·
                  rfl

theorem cell19_6275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 3].length) (baseStart_6275 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6275 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6275 prefixEnd_6275 := by exact prefixLift 6275
  have htrace : WordTrace (prefixWord ++ tailWord_6275) baseStart_6275 baseEnd_6275 := by
    simpa [prefixWord, tailWord_6275, baseEnd_6275] using wordTrace_append hprefix tailTrace_6275
  have hstable : (prefixWord ++ tailWord_6275).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275).length < 2 ^ (prefixWord ++ tailWord_6275).sum := by decide
  have hdescent : baseEnd_6275 < baseStart_6275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292 : List Nat := [2, 4, 2, 3, 1, 1, 6]
def baseStart_6292 : Nat := 118140960795 + 6292 * 2 ^ 59
def prefixEnd_6292 : Nat := 4983230072969 + 3 ^ 40 * 6292 * 2
def baseEnd_6292 : Nat := 638186721618689623915

theorem tailTrace_6292 : CollatzResearch.WordTrace tailWord_6292 prefixEnd_6292 638186721618689623915 := by
  unfold tailWord_6292
  simp only [CollatzResearch.WordTrace]
  refine ⟨114744046606316716578565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152992062141755622104753 114744046606316716578565)
  ·
    refine ⟨21514508738684384358481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114744046606316716578565 21514508738684384358481)
    ·
      refine ⟨16135881554013288268861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21514508738684384358481 16135881554013288268861)
      ·
        refine ⟨6050955582754983100823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16135881554013288268861 6050955582754983100823)
        ·
          refine ⟨9076433374132474651235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6050955582754983100823 9076433374132474651235)
          ·
            refine ⟨13614650061198711976853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9076433374132474651235 13614650061198711976853)
            ·
              refine ⟨638186721618689623915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13614650061198711976853 638186721618689623915)
              ·
                rfl

theorem cell19_6292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 6].length) (baseStart_6292 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6292 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6292 prefixEnd_6292 := by exact prefixLift 6292
  have htrace : WordTrace (prefixWord ++ tailWord_6292) baseStart_6292 baseEnd_6292 := by
    simpa [prefixWord, tailWord_6292, baseEnd_6292] using wordTrace_append hprefix tailTrace_6292
  have hstable : (prefixWord ++ tailWord_6292).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292).length < 2 ^ (prefixWord ++ tailWord_6292).sum := by decide
  have hdescent : baseEnd_6292 < baseStart_6292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6324 : List Nat := [2, 5, 3, 1, 1, 2, 2, 3]
def baseStart_6324 : Nat := 118140960795 + 6324 * 2 ^ 59
def prefixEnd_6324 : Nat := 4983230072969 + 3 ^ 40 * 6324 * 2
def baseEnd_6324 : Nat := 1924297279489476160547

theorem tailTrace_6324 : CollatzResearch.WordTrace tailWord_6324 prefixEnd_6324 1924297279489476160547 := by
  unfold tailWord_6324
  simp only [CollatzResearch.WordTrace]
  refine ⟨115327614548351449161013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153770152731135265548017 115327614548351449161013)
  ·
    refine ⟨10811963863907948358845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115327614548351449161013 10811963863907948358845)
    ·
      refine ⟨4054486448965480634567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10811963863907948358845 4054486448965480634567)
      ·
        refine ⟨6081729673448220951851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4054486448965480634567 6081729673448220951851)
        ·
          refine ⟨9122594510172331427777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6081729673448220951851 9122594510172331427777)
          ·
            refine ⟨6841945882629248570833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9122594510172331427777 6841945882629248570833)
            ·
              refine ⟨5131459411971936428125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6841945882629248570833 5131459411971936428125)
              ·
                refine ⟨1924297279489476160547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5131459411971936428125 1924297279489476160547)
                ·
                  rfl

theorem cell19_6324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_6324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6324 prefixEnd_6324 := by exact prefixLift 6324
  have htrace : WordTrace (prefixWord ++ tailWord_6324) baseStart_6324 baseEnd_6324 := by
    simpa [prefixWord, tailWord_6324, baseEnd_6324] using wordTrace_append hprefix tailTrace_6324
  have hstable : (prefixWord ++ tailWord_6324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6324).length < 2 ^ (prefixWord ++ tailWord_6324).sum := by decide
  have hdescent : baseEnd_6324 < baseStart_6324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6332 : List Nat := [2, 2, 2, 3, 3, 1, 1, 5]
def baseStart_6332 : Nat := 118140960795 + 6332 * 2 ^ 59
def prefixEnd_6332 : Nat := 4983230072969 + 3 ^ 40 * 6332 * 2
def baseEnd_6332 : Nat := 1926731558147827982747

theorem tailTrace_6332 : CollatzResearch.WordTrace tailWord_6332 prefixEnd_6332 1926731558147827982747 := by
  unfold tailWord_6332
  simp only [CollatzResearch.WordTrace]
  refine ⟨115473506533860132306625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153964675378480176408833 115473506533860132306625)
  ·
    refine ⟨86605129900395099229969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115473506533860132306625 86605129900395099229969)
    ·
      refine ⟨64953847425296324422477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86605129900395099229969 64953847425296324422477)
      ·
        refine ⟨24357692784486121658429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64953847425296324422477 24357692784486121658429)
        ·
          refine ⟨9134134794182295621911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24357692784486121658429 9134134794182295621911)
          ·
            refine ⟨13701202191273443432867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9134134794182295621911 13701202191273443432867)
            ·
              refine ⟨20551803286910165149301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13701202191273443432867 20551803286910165149301)
              ·
                refine ⟨1926731558147827982747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20551803286910165149301 1926731558147827982747)
                ·
                  rfl

theorem cell19_6332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_6332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6332 prefixEnd_6332 := by exact prefixLift 6332
  have htrace : WordTrace (prefixWord ++ tailWord_6332) baseStart_6332 baseEnd_6332 := by
    simpa [prefixWord, tailWord_6332, baseEnd_6332] using wordTrace_append hprefix tailTrace_6332
  have hstable : (prefixWord ++ tailWord_6332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6332).length < 2 ^ (prefixWord ++ tailWord_6332).sum := by decide
  have hdescent : baseEnd_6332 < baseStart_6332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465 : List Nat := [1, 2, 5, 2, 2, 1, 6]
def baseStart_6465 : Nat := 118140960795 + 6465 * 2 ^ 59
def prefixEnd_6465 : Nat := 4983230072969 + 3 ^ 40 * 6465 * 2
def baseEnd_6465 : Nat := 655733813614309008943

theorem tailTrace_6465 : CollatzResearch.WordTrace tailWord_6465 prefixEnd_6465 655733813614309008943 := by
  unfold tailWord_6465
  simp only [CollatzResearch.WordTrace]
  refine ⟨235797921585883979204849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157198614390589319469899 235797921585883979204849)
  ·
    refine ⟨176848441189412984403637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235797921585883979204849 176848441189412984403637)
    ·
      refine ⟨16579541361507467287841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176848441189412984403637 16579541361507467287841)
      ·
        refine ⟨12434656021130600465881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16579541361507467287841 12434656021130600465881)
        ·
          refine ⟨9325992015847950349411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12434656021130600465881 9325992015847950349411)
          ·
            refine ⟨13988988023771925524117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9325992015847950349411 13988988023771925524117)
            ·
              refine ⟨655733813614309008943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13988988023771925524117 655733813614309008943)
              ·
                rfl

theorem cell19_6465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 6].length) (baseStart_6465 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6465 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6465 prefixEnd_6465 := by exact prefixLift 6465
  have htrace : WordTrace (prefixWord ++ tailWord_6465) baseStart_6465 baseEnd_6465 := by
    simpa [prefixWord, tailWord_6465, baseEnd_6465] using wordTrace_append hprefix tailTrace_6465
  have hstable : (prefixWord ++ tailWord_6465).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465).length < 2 ^ (prefixWord ++ tailWord_6465).sum := by decide
  have hdescent : baseEnd_6465 < baseStart_6465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503 : List Nat := [1, 1, 5, 1, 3, 1, 4, 3]
def baseStart_6503 : Nat := 118140960795 + 6503 * 2 ^ 59
def prefixEnd_6503 : Nat := 4983230072969 + 3 ^ 40 * 6503 * 2
def baseEnd_6503 : Nat := 1978764264470098182281

theorem tailTrace_6503 : CollatzResearch.WordTrace tailWord_6503 prefixEnd_6503 1978764264470098182281 := by
  unfold tailWord_6503
  simp only [CollatzResearch.WordTrace]
  refine ⟨237183895448216469088163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158122596965477646058775 237183895448216469088163)
  ·
    refine ⟨355775843172324703632245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237183895448216469088163 355775843172324703632245)
    ·
      refine ⟨33353985297405440965523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 355775843172324703632245 33353985297405440965523)
      ·
        refine ⟨50030977946108161448285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33353985297405440965523 50030977946108161448285)
        ·
          refine ⟨18761616729790560543107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50030977946108161448285 18761616729790560543107)
          ·
            refine ⟨28142425094685840814661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18761616729790560543107 28142425094685840814661)
            ·
              refine ⟨5276704705253595152749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28142425094685840814661 5276704705253595152749)
              ·
                refine ⟨1978764264470098182281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5276704705253595152749 1978764264470098182281)
                ·
                  rfl

theorem cell19_6503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 3].length) (baseStart_6503 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6503 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6503 prefixEnd_6503 := by exact prefixLift 6503
  have htrace : WordTrace (prefixWord ++ tailWord_6503) baseStart_6503 baseEnd_6503 := by
    simpa [prefixWord, tailWord_6503, baseEnd_6503] using wordTrace_append hprefix tailTrace_6503
  have hstable : (prefixWord ++ tailWord_6503).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503).length < 2 ^ (prefixWord ++ tailWord_6503).sum := by decide
  have hdescent : baseEnd_6503 < baseStart_6503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507 : List Nat := [1, 1, 1, 1, 2, 2, 2, 9]
def baseStart_6507 : Nat := 118140960795 + 6507 * 2 ^ 59
def prefixEnd_6507 : Nat := 4983230072969 + 3 ^ 40 * 6507 * 2
def baseEnd_6507 : Nat := 1979981403799274093381

theorem tailTrace_6507 : CollatzResearch.WordTrace tailWord_6507 prefixEnd_6507 1979981403799274093381 := by
  unfold tailWord_6507
  simp only [CollatzResearch.WordTrace]
  refine ⟨237329787433725152233775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158219858289150101489183 237329787433725152233775)
  ·
    refine ⟨355994681150587728350663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237329787433725152233775 355994681150587728350663)
    ·
      refine ⟨533992021725881592525995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355994681150587728350663 533992021725881592525995)
      ·
        refine ⟨800988032588822388788993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533992021725881592525995 800988032588822388788993)
        ·
          refine ⟨600741024441616791591745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 800988032588822388788993 600741024441616791591745)
          ·
            refine ⟨450555768331212593693809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600741024441616791591745 450555768331212593693809)
            ·
              refine ⟨337916826248409445270357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450555768331212593693809 337916826248409445270357)
              ·
                refine ⟨1979981403799274093381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 337916826248409445270357 1979981403799274093381)
                ·
                  rfl

theorem cell19_6507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_6507 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6507 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6507 prefixEnd_6507 := by exact prefixLift 6507
  have htrace : WordTrace (prefixWord ++ tailWord_6507) baseStart_6507 baseEnd_6507 := by
    simpa [prefixWord, tailWord_6507, baseEnd_6507] using wordTrace_append hprefix tailTrace_6507
  have hstable : (prefixWord ++ tailWord_6507).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507).length < 2 ^ (prefixWord ++ tailWord_6507).sum := by decide
  have hdescent : baseEnd_6507 < baseStart_6507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518 : List Nat := [5, 1, 1, 4, 2, 1, 5]
def baseStart_6518 : Nat := 118140960795 + 6518 * 2 ^ 59
def prefixEnd_6518 : Nat := 4983230072969 + 3 ^ 40 * 6518 * 2
def baseEnd_6518 : Nat := 661109512318169282969

theorem tailTrace_6518 : CollatzResearch.WordTrace tailWord_6518 prefixEnd_6518 661109512318169282969 := by
  unfold tailWord_6518
  simp only [CollatzResearch.WordTrace]
  refine ⟨14858186899617126930263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158487326929249353922805 14858186899617126930263)
  ·
    refine ⟨22287280349425690395395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14858186899617126930263 22287280349425690395395)
    ·
      refine ⟨33430920524138535593093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22287280349425690395395 33430920524138535593093)
      ·
        refine ⟨6268297598275975423705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33430920524138535593093 6268297598275975423705)
        ·
          refine ⟨4701223198706981567779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6268297598275975423705 4701223198706981567779)
          ·
            refine ⟨7051834798060472351669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701223198706981567779 7051834798060472351669)
            ·
              refine ⟨661109512318169282969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7051834798060472351669 661109512318169282969)
              ·
                rfl

theorem cell19_6518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 5].length) (baseStart_6518 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6518 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6518 prefixEnd_6518 := by exact prefixLift 6518
  have htrace : WordTrace (prefixWord ++ tailWord_6518) baseStart_6518 baseEnd_6518 := by
    simpa [prefixWord, tailWord_6518, baseEnd_6518] using wordTrace_append hprefix tailTrace_6518
  have hstable : (prefixWord ++ tailWord_6518).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518).length < 2 ^ (prefixWord ++ tailWord_6518).sum := by decide
  have hdescent : baseEnd_6518 < baseStart_6518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562 : List Nat := [3, 3, 1, 2, 1, 1, 1, 7]
def baseStart_6562 : Nat := 118140960795 + 6562 * 2 ^ 59
def prefixEnd_6562 : Nat := 4983230072969 + 3 ^ 40 * 6562 * 2
def baseEnd_6562 : Nat := 1996717069575442871009

theorem tailTrace_6562 : CollatzResearch.WordTrace tailWord_6562 prefixEnd_6562 1996717069575442871009 := by
  unfold tailWord_6562
  simp only [CollatzResearch.WordTrace]
  refine ⟨59833950558617386371485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159557201489646363657293 59833950558617386371485)
  ·
    refine ⟨22437731459481519889307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59833950558617386371485 22437731459481519889307)
    ·
      refine ⟨33656597189222279833961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22437731459481519889307 33656597189222279833961)
      ·
        refine ⟨25242447891916709875471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33656597189222279833961 25242447891916709875471)
        ·
          refine ⟨37863671837875064813207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25242447891916709875471 37863671837875064813207)
          ·
            refine ⟨56795507756812597219811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37863671837875064813207 56795507756812597219811)
            ·
              refine ⟨85193261635218895829717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56795507756812597219811 85193261635218895829717)
              ·
                refine ⟨1996717069575442871009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 85193261635218895829717 1996717069575442871009)
                ·
                  rfl

theorem cell19_6562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_6562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6562 prefixEnd_6562 := by exact prefixLift 6562
  have htrace : WordTrace (prefixWord ++ tailWord_6562) baseStart_6562 baseEnd_6562 := by
    simpa [prefixWord, tailWord_6562, baseEnd_6562] using wordTrace_append hprefix tailTrace_6562
  have hstable : (prefixWord ++ tailWord_6562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562).length < 2 ^ (prefixWord ++ tailWord_6562).sum := by decide
  have hdescent : baseEnd_6562 < baseStart_6562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6581 : List Nat := [1, 3, 3, 2, 3, 7]
def baseStart_6581 : Nat := 118140960795 + 6581 * 2 ^ 59
def prefixEnd_6581 : Nat := 4983230072969 + 3 ^ 40 * 6581 * 2
def baseEnd_6581 : Nat := 222499831265447605415

theorem tailTrace_6581 : CollatzResearch.WordTrace tailWord_6581 prefixEnd_6581 222499831265447605415 := by
  unfold tailWord_6581
  simp only [CollatzResearch.WordTrace]
  refine ⟨240028789165635790427597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160019192777090526951731 240028789165635790427597)
  ·
    refine ⟨90010795937113421410349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240028789165635790427597 90010795937113421410349)
    ·
      refine ⟨33754048476417533028881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90010795937113421410349 33754048476417533028881)
      ·
        refine ⟨25315536357313149771661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33754048476417533028881 25315536357313149771661)
        ·
          refine ⟨9493326133992431164373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25315536357313149771661 9493326133992431164373)
          ·
            refine ⟨222499831265447605415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 9493326133992431164373 222499831265447605415)
            ·
              rfl

theorem cell19_6581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 7].length) (baseStart_6581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6581 prefixEnd_6581 := by exact prefixLift 6581
  have htrace : WordTrace (prefixWord ++ tailWord_6581) baseStart_6581 baseEnd_6581 := by
    simpa [prefixWord, tailWord_6581, baseEnd_6581] using wordTrace_append hprefix tailTrace_6581
  have hstable : (prefixWord ++ tailWord_6581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6581).length < 2 ^ (prefixWord ++ tailWord_6581).sum := by decide
  have hdescent : baseEnd_6581 < baseStart_6581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6583 : List Nat := [1, 1, 3, 1, 3, 10]
def baseStart_6583 : Nat := 118140960795 + 6583 * 2 ^ 59
def prefixEnd_6583 : Nat := 4983230072969 + 3 ^ 40 * 6583 * 2
def baseEnd_6583 : Nat := 222567450117068489365

theorem tailTrace_6583 : CollatzResearch.WordTrace tailWord_6583 prefixEnd_6583 222567450117068489365 := by
  unfold tailWord_6583
  simp only [CollatzResearch.WordTrace]
  refine ⟨240101735158390132000403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160067823438926754666935 240101735158390132000403)
  ·
    refine ⟨360152602737585198000605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240101735158390132000403 360152602737585198000605)
    ·
      refine ⟨135057226026594449250227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360152602737585198000605 135057226026594449250227)
      ·
        refine ⟨202585839039891673875341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135057226026594449250227 202585839039891673875341)
        ·
          refine ⟨75969689639959377703253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202585839039891673875341 75969689639959377703253)
          ·
            refine ⟨222567450117068489365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 75969689639959377703253 222567450117068489365)
            ·
              rfl

theorem cell19_6583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 10].length) (baseStart_6583 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6583 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6583 prefixEnd_6583 := by exact prefixLift 6583
  have htrace : WordTrace (prefixWord ++ tailWord_6583) baseStart_6583 baseEnd_6583 := by
    simpa [prefixWord, tailWord_6583, baseEnd_6583] using wordTrace_append hprefix tailTrace_6583
  have hstable : (prefixWord ++ tailWord_6583).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6583).length < 2 ^ (prefixWord ++ tailWord_6583).sum := by decide
  have hdescent : baseEnd_6583 < baseStart_6583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596 : List Nat := [2, 3, 3, 2, 2, 2, 1, 4]
def baseStart_6596 : Nat := 118140960795 + 6596 * 2 ^ 59
def prefixEnd_6596 : Nat := 4983230072969 + 3 ^ 40 * 6596 * 2
def baseEnd_6596 : Nat := 2007062753873438115361

theorem tailTrace_6596 : CollatzResearch.WordTrace tailWord_6596 prefixEnd_6596 2007062753873438115361 := by
  unfold tailWord_6596
  simp only [CollatzResearch.WordTrace]
  refine ⟨120287942055646676111821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160383922740862234815761 120287942055646676111821)
  ·
    refine ⟨45107978270867503541933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120287942055646676111821 45107978270867503541933)
    ·
      refine ⟨16915491851575313828225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45107978270867503541933 16915491851575313828225)
      ·
        refine ⟨12686618888681485371169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16915491851575313828225 12686618888681485371169)
        ·
          refine ⟨9514964166511114028377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12686618888681485371169 9514964166511114028377)
          ·
            refine ⟨7136223124883335521283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9514964166511114028377 7136223124883335521283)
            ·
              refine ⟨10704334687325003281925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7136223124883335521283 10704334687325003281925)
              ·
                refine ⟨2007062753873438115361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10704334687325003281925 2007062753873438115361)
                ·
                  rfl

theorem cell19_6596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_6596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6596 prefixEnd_6596 := by exact prefixLift 6596
  have htrace : WordTrace (prefixWord ++ tailWord_6596) baseStart_6596 baseEnd_6596 := by
    simpa [prefixWord, tailWord_6596, baseEnd_6596] using wordTrace_append hprefix tailTrace_6596
  have hstable : (prefixWord ++ tailWord_6596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596).length < 2 ^ (prefixWord ++ tailWord_6596).sum := by decide
  have hdescent : baseEnd_6596 < baseStart_6596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600 : List Nat := [2, 1, 3, 1, 3, 2, 3, 4]
def baseStart_6600 : Nat := 118140960795 + 6600 * 2 ^ 59
def prefixEnd_6600 : Nat := 4983230072969 + 3 ^ 40 * 6600 * 2
def baseEnd_6600 : Nat := 2008279893202614026461

theorem tailTrace_6600 : CollatzResearch.WordTrace tailWord_6600 prefixEnd_6600 2008279893202614026461 := by
  unfold tailWord_6600
  simp only [CollatzResearch.WordTrace]
  refine ⟨120360888048401017684627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160481184064534690246169 120360888048401017684627)
  ·
    refine ⟨180541332072601526526941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120360888048401017684627 180541332072601526526941)
    ·
      refine ⟨67702999527225572447603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180541332072601526526941 67702999527225572447603)
      ·
        refine ⟨101554499290838358671405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67702999527225572447603 101554499290838358671405)
        ·
          refine ⟨38082937234064384501777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101554499290838358671405 38082937234064384501777)
          ·
            refine ⟨28562202925548288376333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38082937234064384501777 28562202925548288376333)
            ·
              refine ⟨10710826097080608141125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28562202925548288376333 10710826097080608141125)
              ·
                refine ⟨2008279893202614026461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10710826097080608141125 2008279893202614026461)
                ·
                  rfl

theorem cell19_6600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_6600 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6600 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6600 prefixEnd_6600 := by exact prefixLift 6600
  have htrace : WordTrace (prefixWord ++ tailWord_6600) baseStart_6600 baseEnd_6600 := by
    simpa [prefixWord, tailWord_6600, baseEnd_6600] using wordTrace_append hprefix tailTrace_6600
  have hstable : (prefixWord ++ tailWord_6600).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600).length < 2 ^ (prefixWord ++ tailWord_6600).sum := by decide
  have hdescent : baseEnd_6600 < baseStart_6600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6638 : List Nat := [4, 1, 2, 1, 2, 3, 6]
def baseStart_6638 : Nat := 118140960795 + 6638 * 2 ^ 59
def prefixEnd_6638 : Nat := 4983230072969 + 3 ^ 40 * 6638 * 2
def baseEnd_6638 : Nat := 673280905609928393971

theorem tailTrace_6638 : CollatzResearch.WordTrace tailWord_6638 prefixEnd_6638 673280905609928393971 := by
  unfold tailWord_6638
  simp only [CollatzResearch.WordTrace]
  refine ⟨30263468744891815656571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161405166639423016835045 30263468744891815656571)
  ·
    refine ⟨45395203117337723484857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30263468744891815656571 45395203117337723484857)
    ·
      refine ⟨34046402338003292613643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45395203117337723484857 34046402338003292613643)
      ·
        refine ⟨51069603507004938920465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34046402338003292613643 51069603507004938920465)
        ·
          refine ⟨38302202630253704190349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51069603507004938920465 38302202630253704190349)
          ·
            refine ⟨14363325986345139071381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38302202630253704190349 14363325986345139071381)
            ·
              refine ⟨673280905609928393971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14363325986345139071381 673280905609928393971)
              ·
                rfl

theorem cell19_6638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 6].length) (baseStart_6638 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6638 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6638 prefixEnd_6638 := by exact prefixLift 6638
  have htrace : WordTrace (prefixWord ++ tailWord_6638) baseStart_6638 baseEnd_6638 := by
    simpa [prefixWord, tailWord_6638, baseEnd_6638] using wordTrace_append hprefix tailTrace_6638
  have hstable : (prefixWord ++ tailWord_6638).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6638).length < 2 ^ (prefixWord ++ tailWord_6638).sum := by decide
  have hdescent : baseEnd_6638 < baseStart_6638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640 : List Nat := [2, 1, 1, 1, 3, 3, 8]
def baseStart_6640 : Nat := 118140960795 + 6640 * 2 ^ 59
def prefixEnd_6640 : Nat := 4983230072969 + 3 ^ 40 * 6640 * 2
def baseEnd_6640 : Nat := 673483762164791045821

theorem tailTrace_6640 : CollatzResearch.WordTrace tailWord_6640 prefixEnd_6640 673483762164791045821 := by
  unfold tailWord_6640
  simp only [CollatzResearch.WordTrace]
  refine ⟨121090347975944433412687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161453797301259244550249 121090347975944433412687)
  ·
    refine ⟨181635521963916650119031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121090347975944433412687 181635521963916650119031)
    ·
      refine ⟨272453282945874975178547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181635521963916650119031 272453282945874975178547)
      ·
        refine ⟨408679924418812462767821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272453282945874975178547 408679924418812462767821)
        ·
          refine ⟨153254971657054673537933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 408679924418812462767821 153254971657054673537933)
          ·
            refine ⟨57470614371395502576725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153254971657054673537933 57470614371395502576725)
            ·
              refine ⟨673483762164791045821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 57470614371395502576725 673483762164791045821)
              ·
                rfl

theorem cell19_6640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_6640 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6640 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6640 prefixEnd_6640 := by exact prefixLift 6640
  have htrace : WordTrace (prefixWord ++ tailWord_6640) baseStart_6640 baseEnd_6640 := by
    simpa [prefixWord, tailWord_6640, baseEnd_6640] using wordTrace_append hprefix tailTrace_6640
  have hstable : (prefixWord ++ tailWord_6640).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640).length < 2 ^ (prefixWord ++ tailWord_6640).sum := by decide
  have hdescent : baseEnd_6640 < baseStart_6640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659 : List Nat := [1, 1, 1, 3, 2, 1, 4, 6]
def baseStart_6659 : Nat := 118140960795 + 6659 * 2 ^ 59
def prefixEnd_6659 : Nat := 4983230072969 + 3 ^ 40 * 6659 * 2
def baseEnd_6659 : Nat := 2026232698307958715189

theorem tailTrace_6659 : CollatzResearch.WordTrace tailWord_6659 prefixEnd_6659 2026232698307958715189 := by
  unfold tailWord_6659
  simp only [CollatzResearch.WordTrace]
  refine ⟨242873682883055111767031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161915788588703407844687 242873682883055111767031)
  ·
    refine ⟨364310524324582667650547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242873682883055111767031 364310524324582667650547)
    ·
      refine ⟨546465786486874001475821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364310524324582667650547 546465786486874001475821)
      ·
        refine ⟨204924669932577750553433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 546465786486874001475821 204924669932577750553433)
        ·
          refine ⟨153693502449433312915075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204924669932577750553433 153693502449433312915075)
          ·
            refine ⟨230540253674149969372613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153693502449433312915075 230540253674149969372613)
            ·
              refine ⟨43226297563903119257365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230540253674149969372613 43226297563903119257365)
              ·
                refine ⟨2026232698307958715189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43226297563903119257365 2026232698307958715189)
                ·
                  rfl

theorem cell19_6659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_6659 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6659 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6659 prefixEnd_6659 := by exact prefixLift 6659
  have htrace : WordTrace (prefixWord ++ tailWord_6659) baseStart_6659 baseEnd_6659 := by
    simpa [prefixWord, tailWord_6659, baseEnd_6659] using wordTrace_append hprefix tailTrace_6659
  have hstable : (prefixWord ++ tailWord_6659).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659).length < 2 ^ (prefixWord ++ tailWord_6659).sum := by decide
  have hdescent : baseEnd_6659 < baseStart_6659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714 : List Nat := [3, 1, 1, 1, 3, 4, 2, 4]
def baseStart_6714 : Nat := 118140960795 + 6714 * 2 ^ 59
def prefixEnd_6714 : Nat := 4983230072969 + 3 ^ 40 * 6714 * 2
def baseEnd_6714 : Nat := 2042968364084127492817

theorem tailTrace_6714 : CollatzResearch.WordTrace tailWord_6714 prefixEnd_6714 2042968364084127492817 := by
  unfold tailWord_6714
  simp only [CollatzResearch.WordTrace]
  refine ⟨61219924420949876254799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163253131789199670012797 61219924420949876254799)
  ·
    refine ⟨91829886631424814382199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61219924420949876254799 91829886631424814382199)
    ·
      refine ⟨137744829947137221573299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91829886631424814382199 137744829947137221573299)
      ·
        refine ⟨206617244920705832359949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137744829947137221573299 206617244920705832359949)
        ·
          refine ⟨77481466845264687134981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206617244920705832359949 77481466845264687134981)
          ·
            refine ⟨14527775033487128837809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77481466845264687134981 14527775033487128837809)
            ·
              refine ⟨10895831275115346628357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14527775033487128837809 10895831275115346628357)
              ·
                refine ⟨2042968364084127492817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10895831275115346628357 2042968364084127492817)
                ·
                  rfl

theorem cell19_6714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_6714 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6714 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6714 prefixEnd_6714 := by exact prefixLift 6714
  have htrace : WordTrace (prefixWord ++ tailWord_6714) baseStart_6714 baseEnd_6714 := by
    simpa [prefixWord, tailWord_6714, baseEnd_6714] using wordTrace_append hprefix tailTrace_6714
  have hstable : (prefixWord ++ tailWord_6714).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714).length < 2 ^ (prefixWord ++ tailWord_6714).sum := by decide
  have hdescent : baseEnd_6714 < baseStart_6714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735 : List Nat := [1, 1, 2, 1, 1, 2, 6, 5]
def baseStart_6735 : Nat := 118140960795 + 6735 * 2 ^ 59
def prefixEnd_6735 : Nat := 4983230072969 + 3 ^ 40 * 6735 * 2
def baseEnd_6735 : Nat := 2049358345562301026093

theorem tailTrace_6735 : CollatzResearch.WordTrace tailWord_6735 prefixEnd_6735 2049358345562301026093 := by
  unfold tailWord_6735
  simp only [CollatzResearch.WordTrace]
  refine ⟨245645630607720091533659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163763753738480061022439 245645630607720091533659)
  ·
    refine ⟨368468445911580137300489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245645630607720091533659 368468445911580137300489)
    ·
      refine ⟨276351334433685102975367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368468445911580137300489 276351334433685102975367)
      ·
        refine ⟨414527001650527654463051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276351334433685102975367 414527001650527654463051)
        ·
          refine ⟨621790502475791481694577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414527001650527654463051 621790502475791481694577)
          ·
            refine ⟨466342876856843611270933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621790502475791481694577 466342876856843611270933)
            ·
              refine ⟨21859822352664544278325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 466342876856843611270933 21859822352664544278325)
              ·
                refine ⟨2049358345562301026093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21859822352664544278325 2049358345562301026093)
                ·
                  rfl

theorem cell19_6735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_6735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6735 prefixEnd_6735 := by exact prefixLift 6735
  have htrace : WordTrace (prefixWord ++ tailWord_6735) baseStart_6735 baseEnd_6735 := by
    simpa [prefixWord, tailWord_6735, baseEnd_6735] using wordTrace_append hprefix tailTrace_6735
  have hstable : (prefixWord ++ tailWord_6735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735).length < 2 ^ (prefixWord ++ tailWord_6735).sum := by decide
  have hdescent : baseEnd_6735 < baseStart_6735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6788 : List Nat := [2, 3, 2, 1, 3, 2, 3, 3]
def baseStart_6788 : Nat := 118140960795 + 6788 * 2 ^ 59
def prefixEnd_6788 : Nat := 4983230072969 + 3 ^ 40 * 6788 * 2
def baseEnd_6788 : Nat := 2065485441673881848171

theorem tailTrace_6788 : CollatzResearch.WordTrace tailWord_6788 prefixEnd_6788 2065485441673881848171 := by
  unfold tailWord_6788
  simp only [CollatzResearch.WordTrace]
  refine ⟨123789349707855071606509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165052466277140095475345 123789349707855071606509)
  ·
    refine ⟨46421006140445651852441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123789349707855071606509 46421006140445651852441)
    ·
      refine ⟨34815754605334238889331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46421006140445651852441 34815754605334238889331)
      ·
        refine ⟨52223631908001358333997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34815754605334238889331 52223631908001358333997)
        ·
          refine ⟨19583861965500509375249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52223631908001358333997 19583861965500509375249)
          ·
            refine ⟨14687896474125382031437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19583861965500509375249 14687896474125382031437)
            ·
              refine ⟨5507961177797018261789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14687896474125382031437 5507961177797018261789)
              ·
                refine ⟨2065485441673881848171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5507961177797018261789 2065485441673881848171)
                ·
                  rfl

theorem cell19_6788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_6788 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6788 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6788 prefixEnd_6788 := by exact prefixLift 6788
  have htrace : WordTrace (prefixWord ++ tailWord_6788) baseStart_6788 baseEnd_6788 := by
    simpa [prefixWord, tailWord_6788, baseEnd_6788] using wordTrace_append hprefix tailTrace_6788
  have hstable : (prefixWord ++ tailWord_6788).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6788).length < 2 ^ (prefixWord ++ tailWord_6788).sum := by decide
  have hdescent : baseEnd_6788 < baseStart_6788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845 : List Nat := [1, 4, 1, 2, 1, 5, 2, 3]
def baseStart_6845 : Nat := 118140960795 + 6845 * 2 ^ 59
def prefixEnd_6845 : Nat := 4983230072969 + 3 ^ 40 * 6845 * 2
def baseEnd_6845 : Nat := 2082829677114638581349

theorem tailTrace_6845 : CollatzResearch.WordTrace tailWord_6845 prefixEnd_6845 2082829677114638581349 := by
  unfold tailWord_6845
  simp only [CollatzResearch.WordTrace]
  refine ⟨249657660209208878037989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166438440139472585358659 249657660209208878037989)
  ·
    refine ⟨46810811289226664632123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249657660209208878037989 46810811289226664632123)
    ·
      refine ⟨70216216933839996948185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46810811289226664632123 70216216933839996948185)
      ·
        refine ⟨52662162700379997711139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70216216933839996948185 52662162700379997711139)
        ·
          refine ⟨78993244050569996566709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52662162700379997711139 78993244050569996566709)
          ·
            refine ⟨7405616629740937178129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78993244050569996566709 7405616629740937178129)
            ·
              refine ⟨5554212472305702883597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7405616629740937178129 5554212472305702883597)
              ·
                refine ⟨2082829677114638581349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5554212472305702883597 2082829677114638581349)
                ·
                  rfl

theorem cell19_6845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 3].length) (baseStart_6845 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6845 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6845 prefixEnd_6845 := by exact prefixLift 6845
  have htrace : WordTrace (prefixWord ++ tailWord_6845) baseStart_6845 baseEnd_6845 := by
    simpa [prefixWord, tailWord_6845, baseEnd_6845] using wordTrace_append hprefix tailTrace_6845
  have hstable : (prefixWord ++ tailWord_6845).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845).length < 2 ^ (prefixWord ++ tailWord_6845).sum := by decide
  have hdescent : baseEnd_6845 < baseStart_6845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847 : List Nat := [1, 1, 2, 2, 2, 4, 4, 3]
def baseStart_6847 : Nat := 118140960795 + 6847 * 2 ^ 59
def prefixEnd_6847 : Nat := 4983230072969 + 3 ^ 40 * 6847 * 2
def baseEnd_6847 : Nat := 2083438246779226536899

theorem tailTrace_6847 : CollatzResearch.WordTrace tailWord_6847 prefixEnd_6847 2083438246779226536899 := by
  unfold tailWord_6847
  simp only [CollatzResearch.WordTrace]
  refine ⟨249730606201963219610795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166487070801308813073863 249730606201963219610795)
  ·
    refine ⟨374595909302944829416193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249730606201963219610795 374595909302944829416193)
    ·
      refine ⟨280946931977208622062145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374595909302944829416193 280946931977208622062145)
      ·
        refine ⟨210710198982906466546609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280946931977208622062145 210710198982906466546609)
        ·
          refine ⟨158032649237179849909957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210710198982906466546609 158032649237179849909957)
          ·
            refine ⟨29631121731971221858117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158032649237179849909957 29631121731971221858117)
            ·
              refine ⟨5555835324744604098397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29631121731971221858117 5555835324744604098397)
              ·
                refine ⟨2083438246779226536899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5555835324744604098397 2083438246779226536899)
                ·
                  rfl

theorem cell19_6847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 3].length) (baseStart_6847 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6847 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6847 prefixEnd_6847 := by exact prefixLift 6847
  have htrace : WordTrace (prefixWord ++ tailWord_6847) baseStart_6847 baseEnd_6847 := by
    simpa [prefixWord, tailWord_6847, baseEnd_6847] using wordTrace_append hprefix tailTrace_6847
  have hstable : (prefixWord ++ tailWord_6847).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847).length < 2 ^ (prefixWord ++ tailWord_6847).sum := by decide
  have hdescent : baseEnd_6847 < baseStart_6847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6885 : List Nat := [1, 3, 1, 4, 1, 3, 2, 4]
def baseStart_6885 : Nat := 118140960795 + 6885 * 2 ^ 59
def prefixEnd_6885 : Nat := 4983230072969 + 3 ^ 40 * 6885 * 2
def baseEnd_6885 : Nat := 2095001070406397692351

theorem tailTrace_6885 : CollatzResearch.WordTrace tailWord_6885 prefixEnd_6885 2095001070406397692351 := by
  unfold tailWord_6885
  simp only [CollatzResearch.WordTrace]
  refine ⟨251116580064295709494109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167411053376197139662739 251116580064295709494109)
  ·
    refine ⟨94168717524110891060291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251116580064295709494109 94168717524110891060291)
    ·
      refine ⟨141253076286166336590437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94168717524110891060291 141253076286166336590437)
      ·
        refine ⟨26484951803656188110707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141253076286166336590437 26484951803656188110707)
        ·
          refine ⟨39727427705484282166061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26484951803656188110707 39727427705484282166061)
          ·
            refine ⟨14897785389556605812273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39727427705484282166061 14897785389556605812273)
            ·
              refine ⟨11173339042167454359205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14897785389556605812273 11173339042167454359205)
              ·
                refine ⟨2095001070406397692351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11173339042167454359205 2095001070406397692351)
                ·
                  rfl

theorem cell19_6885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_6885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6885 prefixEnd_6885 := by exact prefixLift 6885
  have htrace : WordTrace (prefixWord ++ tailWord_6885) baseStart_6885 baseEnd_6885 := by
    simpa [prefixWord, tailWord_6885, baseEnd_6885] using wordTrace_append hprefix tailTrace_6885
  have hstable : (prefixWord ++ tailWord_6885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6885).length < 2 ^ (prefixWord ++ tailWord_6885).sum := by decide
  have hdescent : baseEnd_6885 < baseStart_6885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906 : List Nat := [3, 1, 1, 1, 1, 3, 4, 5]
def baseStart_6906 : Nat := 118140960795 + 6906 * 2 ^ 59
def prefixEnd_6906 : Nat := 4983230072969 + 3 ^ 40 * 6906 * 2
def baseEnd_6906 : Nat := 2101391051884571225627

theorem tailTrace_6906 : CollatzResearch.WordTrace tailWord_6906 prefixEnd_6906 2101391051884571225627 := by
  unfold tailWord_6906
  simp only [CollatzResearch.WordTrace]
  refine ⟨62970628247054074002143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167921675325477530672381 62970628247054074002143)
  ·
    refine ⟨94455942370581111003215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62970628247054074002143 94455942370581111003215)
    ·
      refine ⟨141683913555871666504823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94455942370581111003215 141683913555871666504823)
      ·
        refine ⟨212525870333807499757235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141683913555871666504823 212525870333807499757235)
        ·
          refine ⟨318788805500711249635853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212525870333807499757235 318788805500711249635853)
          ·
            refine ⟨119545802062766718613445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318788805500711249635853 119545802062766718613445)
            ·
              refine ⟨22414837886768759740021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119545802062766718613445 22414837886768759740021)
              ·
                refine ⟨2101391051884571225627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22414837886768759740021 2101391051884571225627)
                ·
                  rfl

theorem cell19_6906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_6906 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6906 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6906 prefixEnd_6906 := by exact prefixLift 6906
  have htrace : WordTrace (prefixWord ++ tailWord_6906) baseStart_6906 baseEnd_6906 := by
    simpa [prefixWord, tailWord_6906, baseEnd_6906] using wordTrace_append hprefix tailTrace_6906
  have hstable : (prefixWord ++ tailWord_6906).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906).length < 2 ^ (prefixWord ++ tailWord_6906).sum := by decide
  have hdescent : baseEnd_6906 < baseStart_6906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961 : List Nat := [1, 2, 2, 3, 2, 1, 5, 3]
def baseStart_6961 : Nat := 118140960795 + 6961 * 2 ^ 59
def prefixEnd_6961 : Nat := 4983230072969 + 3 ^ 40 * 6961 * 2
def baseEnd_6961 : Nat := 2118126717660740003255

theorem tailTrace_6961 : CollatzResearch.WordTrace tailWord_6961 prefixEnd_6961 2118126717660740003255 := by
  unfold tailWord_6961
  simp only [CollatzResearch.WordTrace]
  refine ⟨253888527788960689260737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169259018525973792840491 253888527788960689260737)
  ·
    refine ⟨190416395841720516945553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253888527788960689260737 190416395841720516945553)
    ·
      refine ⟨142812296881290387709165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190416395841720516945553 142812296881290387709165)
      ·
        refine ⟨53554611330483895390937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142812296881290387709165 53554611330483895390937)
        ·
          refine ⟨40165958497862921543203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53554611330483895390937 40165958497862921543203)
          ·
            refine ⟨60248937746794382314805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40165958497862921543203 60248937746794382314805)
            ·
              refine ⟨5648337913761973342013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60248937746794382314805 5648337913761973342013)
              ·
                refine ⟨2118126717660740003255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5648337913761973342013 2118126717660740003255)
                ·
                  rfl

theorem cell19_6961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 3].length) (baseStart_6961 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_6961 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_6961 prefixEnd_6961 := by exact prefixLift 6961
  have htrace : WordTrace (prefixWord ++ tailWord_6961) baseStart_6961 baseEnd_6961 := by
    simpa [prefixWord, tailWord_6961, baseEnd_6961] using wordTrace_append hprefix tailTrace_6961
  have hstable : (prefixWord ++ tailWord_6961).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961).length < 2 ^ (prefixWord ++ tailWord_6961).sum := by decide
  have hdescent : baseEnd_6961 < baseStart_6961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7016 : List Nat := [2, 1, 4, 2, 1, 4, 2, 3]
def baseStart_7016 : Nat := 118140960795 + 7016 * 2 ^ 59
def prefixEnd_7016 : Nat := 4983230072969 + 3 ^ 40 * 7016 * 2
def baseEnd_7016 : Nat := 2134862383436908780883

theorem tailTrace_7016 : CollatzResearch.WordTrace tailWord_7016 prefixEnd_7016 2134862383436908780883 := by
  unfold tailWord_7016
  simp only [CollatzResearch.WordTrace]
  refine ⟨127947271294852541256451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170596361726470055008601 127947271294852541256451)
  ·
    refine ⟨191920906942278811884677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127947271294852541256451 191920906942278811884677)
    ·
      refine ⟨35985170051677277228377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191920906942278811884677 35985170051677277228377)
      ·
        refine ⟨26988877538757957921283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35985170051677277228377 26988877538757957921283)
        ·
          refine ⟨40483316308136936881925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26988877538757957921283 40483316308136936881925)
          ·
            refine ⟨7590621807775675665361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40483316308136936881925 7590621807775675665361)
            ·
              refine ⟨5692966355831756749021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7590621807775675665361 5692966355831756749021)
              ·
                refine ⟨2134862383436908780883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5692966355831756749021 2134862383436908780883)
                ·
                  rfl

theorem cell19_7016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_7016 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7016 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7016 prefixEnd_7016 := by exact prefixLift 7016
  have htrace : WordTrace (prefixWord ++ tailWord_7016) baseStart_7016 baseEnd_7016 := by
    simpa [prefixWord, tailWord_7016, baseEnd_7016] using wordTrace_append hprefix tailTrace_7016
  have hstable : (prefixWord ++ tailWord_7016).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7016).length < 2 ^ (prefixWord ++ tailWord_7016).sum := by decide
  have hdescent : baseEnd_7016 < baseStart_7016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7020 : List Nat := [2, 2, 1, 1, 4, 1, 3, 5]
def baseStart_7020 : Nat := 118140960795 + 7020 * 2 ^ 59
def prefixEnd_7020 : Nat := 4983230072969 + 3 ^ 40 * 7020 * 2
def baseEnd_7020 : Nat := 2136079522766084691983

theorem tailTrace_7020 : CollatzResearch.WordTrace tailWord_7020 prefixEnd_7020 2136079522766084691983 := by
  unfold tailWord_7020
  simp only [CollatzResearch.WordTrace]
  refine ⟨128020217287606882829257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170693623050142510439009 128020217287606882829257)
  ·
    refine ⟨96015162965705162121943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128020217287606882829257 96015162965705162121943)
    ·
      refine ⟨144022744448557743182915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96015162965705162121943 144022744448557743182915)
      ·
        refine ⟨216034116672836614774373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144022744448557743182915 216034116672836614774373)
        ·
          refine ⟨40506396876156865270195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216034116672836614774373 40506396876156865270195)
          ·
            refine ⟨60759595314235297905293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40506396876156865270195 60759595314235297905293)
            ·
              refine ⟨22784848242838236714485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60759595314235297905293 22784848242838236714485)
              ·
                refine ⟨2136079522766084691983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22784848242838236714485 2136079522766084691983)
                ·
                  rfl

theorem cell19_7020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_7020 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7020 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7020 prefixEnd_7020 := by exact prefixLift 7020
  have htrace : WordTrace (prefixWord ++ tailWord_7020) baseStart_7020 baseEnd_7020 := by
    simpa [prefixWord, tailWord_7020, baseEnd_7020] using wordTrace_append hprefix tailTrace_7020
  have hstable : (prefixWord ++ tailWord_7020).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7020).length < 2 ^ (prefixWord ++ tailWord_7020).sum := by decide
  have hdescent : baseEnd_7020 < baseStart_7020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115 : List Nat := [1, 1, 1, 1, 3, 5, 3, 4]
def baseStart_7115 : Nat := 118140960795 + 7115 * 2 ^ 59
def prefixEnd_7115 : Nat := 4983230072969 + 3 ^ 40 * 7115 * 2
def baseEnd_7115 : Nat := 2164986581834012580613

theorem tailTrace_7115 : CollatzResearch.WordTrace tailWord_7115 prefixEnd_7115 2164986581834012580613 := by
  unfold tailWord_7115
  simp only [CollatzResearch.WordTrace]
  refine ⟨259505369231044990366799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173003579487363326911199 259505369231044990366799)
  ·
    refine ⟨389258053846567485550199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259505369231044990366799 389258053846567485550199)
    ·
      refine ⟨583887080769851228325299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389258053846567485550199 583887080769851228325299)
      ·
        refine ⟨875830621154776842487949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583887080769851228325299 875830621154776842487949)
        ·
          refine ⟨328436482933041315932981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 875830621154776842487949 328436482933041315932981)
          ·
            refine ⟨30790920274972623368717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 328436482933041315932981 30790920274972623368717)
            ·
              refine ⟨11546595103114733763269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30790920274972623368717 11546595103114733763269)
              ·
                refine ⟨2164986581834012580613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11546595103114733763269 2164986581834012580613)
                ·
                  rfl

theorem cell19_7115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_7115 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7115 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7115 prefixEnd_7115 := by exact prefixLift 7115
  have htrace : WordTrace (prefixWord ++ tailWord_7115) baseStart_7115 baseEnd_7115 := by
    simpa [prefixWord, tailWord_7115, baseEnd_7115] using wordTrace_append hprefix tailTrace_7115
  have hstable : (prefixWord ++ tailWord_7115).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115).length < 2 ^ (prefixWord ++ tailWord_7115).sum := by decide
  have hdescent : baseEnd_7115 < baseStart_7115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7153 : List Nat := [1, 2, 2, 2, 4, 2, 6]
def baseStart_7153 : Nat := 118140960795 + 7153 * 2 ^ 59
def prefixEnd_7153 : Nat := 4983230072969 + 3 ^ 40 * 7153 * 2
def baseEnd_7153 : Nat := 725516468487061245355

theorem tailTrace_7153 : CollatzResearch.WordTrace tailWord_7153 prefixEnd_7153 725516468487061245355 := by
  unfold tailWord_7153
  simp only [CollatzResearch.WordTrace]
  refine ⟨260891343093377480250113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173927562062251653500075 260891343093377480250113)
  ·
    refine ⟨195668507320033110187585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260891343093377480250113 195668507320033110187585)
    ·
      refine ⟨146751380490024832640689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195668507320033110187585 146751380490024832640689)
      ·
        refine ⟨110063535367518624480517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146751380490024832640689 110063535367518624480517)
        ·
          refine ⟨20636912881409742090097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110063535367518624480517 20636912881409742090097)
          ·
            refine ⟨15477684661057306567573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20636912881409742090097 15477684661057306567573)
            ·
              refine ⟨725516468487061245355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15477684661057306567573 725516468487061245355)
              ·
                rfl

theorem cell19_7153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 6].length) (baseStart_7153 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7153 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7153 prefixEnd_7153 := by exact prefixLift 7153
  have htrace : WordTrace (prefixWord ++ tailWord_7153) baseStart_7153 baseEnd_7153 := by
    simpa [prefixWord, tailWord_7153, baseEnd_7153] using wordTrace_append hprefix tailTrace_7153
  have hstable : (prefixWord ++ tailWord_7153).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7153).length < 2 ^ (prefixWord ++ tailWord_7153).sum := by decide
  have hdescent : baseEnd_7153 < baseStart_7153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7189 : List Nat := [1, 3, 2, 1, 4, 1, 4, 3]
def baseStart_7189 : Nat := 118140960795 + 7189 * 2 ^ 59
def prefixEnd_7189 : Nat := 4983230072969 + 3 ^ 40 * 7189 * 2
def baseEnd_7189 : Nat := 2187503659423766935967

theorem tailTrace_7189 : CollatzResearch.WordTrace tailWord_7189 prefixEnd_7189 2187503659423766935967 := by
  unfold tailWord_7189
  simp only [CollatzResearch.WordTrace]
  refine ⟨262204370962955628560621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174802913975303752373747 262204370962955628560621)
  ·
    refine ⟨98326639111108360710233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262204370962955628560621 98326639111108360710233)
    ·
      refine ⟨73744979333331270532675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98326639111108360710233 73744979333331270532675)
      ·
        refine ⟨110617468999996905799013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73744979333331270532675 110617468999996905799013)
        ·
          refine ⟨20740775437499419837315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110617468999996905799013 20740775437499419837315)
          ·
            refine ⟨31111163156249129755973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20740775437499419837315 31111163156249129755973)
            ·
              refine ⟨5833343091796711829245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31111163156249129755973 5833343091796711829245)
              ·
                refine ⟨2187503659423766935967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5833343091796711829245 2187503659423766935967)
                ·
                  rfl

theorem cell19_7189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 3].length) (baseStart_7189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7189 prefixEnd_7189 := by exact prefixLift 7189
  have htrace : WordTrace (prefixWord ++ tailWord_7189) baseStart_7189 baseEnd_7189 := by
    simpa [prefixWord, tailWord_7189, baseEnd_7189] using wordTrace_append hprefix tailTrace_7189
  have hstable : (prefixWord ++ tailWord_7189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7189).length < 2 ^ (prefixWord ++ tailWord_7189).sum := by decide
  have hdescent : baseEnd_7189 < baseStart_7189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7229 : List Nat := [1, 4, 1, 3, 1, 2, 1, 6]
def baseStart_7229 : Nat := 118140960795 + 7229 * 2 ^ 59
def prefixEnd_7229 : Nat := 4983230072969 + 3 ^ 40 * 7229 * 2
def baseEnd_7229 : Nat := 2199675052715526046969

theorem tailTrace_7229 : CollatzResearch.WordTrace tailWord_7229 prefixEnd_7229 2199675052715526046969 := by
  unfold tailWord_7229
  simp only [CollatzResearch.WordTrace]
  refine ⟨263663290818042460016741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175775527212028306677827 263663290818042460016741)
  ·
    refine ⟨49436867028382961253139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263663290818042460016741 49436867028382961253139)
    ·
      refine ⟨74155300542574441879709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49436867028382961253139 74155300542574441879709)
      ·
        refine ⟨27808237703465415704891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74155300542574441879709 27808237703465415704891)
        ·
          refine ⟨41712356555198123557337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27808237703465415704891 41712356555198123557337)
          ·
            refine ⟨31284267416398592668003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41712356555198123557337 31284267416398592668003)
            ·
              refine ⟨46926401124597889002005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31284267416398592668003 46926401124597889002005)
              ·
                refine ⟨2199675052715526046969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46926401124597889002005 2199675052715526046969)
                ·
                  rfl

theorem cell19_7229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_7229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7229 prefixEnd_7229 := by exact prefixLift 7229
  have htrace : WordTrace (prefixWord ++ tailWord_7229) baseStart_7229 baseEnd_7229 := by
    simpa [prefixWord, tailWord_7229, baseEnd_7229] using wordTrace_append hprefix tailTrace_7229
  have hstable : (prefixWord ++ tailWord_7229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7229).length < 2 ^ (prefixWord ++ tailWord_7229).sum := by decide
  have hdescent : baseEnd_7229 < baseStart_7229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7307 : List Nat := [1, 1, 1, 1, 4, 1, 1, 9]
def baseStart_7307 : Nat := 118140960795 + 7307 * 2 ^ 59
def prefixEnd_7307 : Nat := 4983230072969 + 3 ^ 40 * 7307 * 2
def baseEnd_7307 : Nat := 2223409269634456313423

theorem tailTrace_7307 : CollatzResearch.WordTrace tailWord_7307 prefixEnd_7307 2223409269634456313423 := by
  unfold tailWord_7307
  simp only [CollatzResearch.WordTrace]
  refine ⟨266508184535461781356175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177672123023641187570783 266508184535461781356175)
  ·
    refine ⟨399762276803192672034263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266508184535461781356175 399762276803192672034263)
    ·
      refine ⟨599643415204789008051395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399762276803192672034263 599643415204789008051395)
      ·
        refine ⟨899465122807183512077093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599643415204789008051395 899465122807183512077093)
        ·
          refine ⟨168649710526346908514455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 899465122807183512077093 168649710526346908514455)
          ·
            refine ⟨252974565789520362771683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168649710526346908514455 252974565789520362771683)
            ·
              refine ⟨379461848684280544157525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252974565789520362771683 379461848684280544157525)
              ·
                refine ⟨2223409269634456313423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 379461848684280544157525 2223409269634456313423)
                ·
                  rfl

theorem cell19_7307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_7307 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7307 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7307 prefixEnd_7307 := by exact prefixLift 7307
  have htrace : WordTrace (prefixWord ++ tailWord_7307) baseStart_7307 baseEnd_7307 := by
    simpa [prefixWord, tailWord_7307, baseEnd_7307] using wordTrace_append hprefix tailTrace_7307
  have hstable : (prefixWord ++ tailWord_7307).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7307).length < 2 ^ (prefixWord ++ tailWord_7307).sum := by decide
  have hdescent : baseEnd_7307 < baseStart_7307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324 : List Nat := [2, 2, 3, 2, 1, 3, 6]
def baseStart_7324 : Nat := 118140960795 + 7324 * 2 ^ 59
def prefixEnd_7324 : Nat := 4983230072969 + 3 ^ 40 * 7324 * 2
def baseEnd_7324 : Nat := 742860703927817978533

theorem tailTrace_7324 : CollatzResearch.WordTrace tailWord_7324 prefixEnd_7324 742860703927817978533 := by
  unfold tailWord_7324
  simp only [CollatzResearch.WordTrace]
  refine ⟨133564112736936842362513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178085483649249123150017 133564112736936842362513)
  ·
    refine ⟨100173084552702631771885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133564112736936842362513 100173084552702631771885)
    ·
      refine ⟨37564906707263486914457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100173084552702631771885 37564906707263486914457)
      ·
        refine ⟨28173680030447615185843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37564906707263486914457 28173680030447615185843)
        ·
          refine ⟨42260520045671422778765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28173680030447615185843 42260520045671422778765)
          ·
            refine ⟨15847695017126783542037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42260520045671422778765 15847695017126783542037)
            ·
              refine ⟨742860703927817978533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15847695017126783542037 742860703927817978533)
              ·
                rfl

theorem cell19_7324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 6].length) (baseStart_7324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7324 prefixEnd_7324 := by exact prefixLift 7324
  have htrace : WordTrace (prefixWord ++ tailWord_7324) baseStart_7324 baseEnd_7324 := by
    simpa [prefixWord, tailWord_7324, baseEnd_7324] using wordTrace_append hprefix tailTrace_7324
  have hstable : (prefixWord ++ tailWord_7324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324).length < 2 ^ (prefixWord ++ tailWord_7324).sum := by decide
  have hdescent : baseEnd_7324 < baseStart_7324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7358 : List Nat := [4, 2, 1, 1, 3, 3, 2, 3]
def baseStart_7358 : Nat := 118140960795 + 7358 * 2 ^ 59
def prefixEnd_7358 : Nat := 4983230072969 + 3 ^ 40 * 7358 * 2
def baseEnd_7358 : Nat := 2238927796081449179951

theorem tailTrace_7358 : CollatzResearch.WordTrace tailWord_7358 prefixEnd_7358 2238927796081449179951 := by
  unfold tailWord_7358
  simp only [CollatzResearch.WordTrace]
  refine ⟨33546038418837186432841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178912204900464994308485 33546038418837186432841)
  ·
    refine ⟨25159528814127889824631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33546038418837186432841 25159528814127889824631)
    ·
      refine ⟨37739293221191834736947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25159528814127889824631 37739293221191834736947)
      ·
        refine ⟨56608939831787752105421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37739293221191834736947 56608939831787752105421)
        ·
          refine ⟨21228352436920407039533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56608939831787752105421 21228352436920407039533)
          ·
            refine ⟨7960632163845152639825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21228352436920407039533 7960632163845152639825)
            ·
              refine ⟨5970474122883864479869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7960632163845152639825 5970474122883864479869)
              ·
                refine ⟨2238927796081449179951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5970474122883864479869 2238927796081449179951)
                ·
                  rfl

theorem cell19_7358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_7358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7358 prefixEnd_7358 := by exact prefixLift 7358
  have htrace : WordTrace (prefixWord ++ tailWord_7358) baseStart_7358 baseEnd_7358 := by
    simpa [prefixWord, tailWord_7358, baseEnd_7358] using wordTrace_append hprefix tailTrace_7358
  have hstable : (prefixWord ++ tailWord_7358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7358).length < 2 ^ (prefixWord ++ tailWord_7358).sum := by decide
  have hdescent : baseEnd_7358 < baseStart_7358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381 : List Nat := [1, 3, 2, 4, 1, 1, 7]
def baseStart_7381 : Nat := 118140960795 + 7381 * 2 ^ 59
def prefixEnd_7381 : Nat := 4983230072969 + 3 ^ 40 * 7381 * 2
def baseEnd_7381 : Nat := 748642115741403556259

theorem tailTrace_7381 : CollatzResearch.WordTrace tailWord_7381 prefixEnd_7381 748642115741403556259 := by
  unfold tailWord_7381
  simp only [CollatzResearch.WordTrace]
  refine ⟨269207186267372419549997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179471457511581613033331 269207186267372419549997)
  ·
    refine ⟨100952694850264657331249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269207186267372419549997 100952694850264657331249)
    ·
      refine ⟨75714521137698492998437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100952694850264657331249 75714521137698492998437)
      ·
        refine ⟨14196472713318467437207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75714521137698492998437 14196472713318467437207)
        ·
          refine ⟨21294709069977701155811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14196472713318467437207 21294709069977701155811)
          ·
            refine ⟨31942063604966551733717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21294709069977701155811 31942063604966551733717)
            ·
              refine ⟨748642115741403556259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31942063604966551733717 748642115741403556259)
              ·
                rfl

theorem cell19_7381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 7].length) (baseStart_7381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7381 prefixEnd_7381 := by exact prefixLift 7381
  have htrace : WordTrace (prefixWord ++ tailWord_7381) baseStart_7381 baseEnd_7381 := by
    simpa [prefixWord, tailWord_7381, baseEnd_7381] using wordTrace_append hprefix tailTrace_7381
  have hstable : (prefixWord ++ tailWord_7381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381).length < 2 ^ (prefixWord ++ tailWord_7381).sum := by decide
  have hdescent : baseEnd_7381 < baseStart_7381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383 : List Nat := [1, 1, 3, 2, 1, 2, 9]
def baseStart_7383 : Nat := 118140960795 + 7383 * 2 ^ 59
def prefixEnd_7383 : Nat := 4983230072969 + 3 ^ 40 * 7383 * 2
def baseEnd_7383 : Nat := 748844972296266208109

theorem tailTrace_7383 : CollatzResearch.WordTrace tailWord_7383 prefixEnd_7383 748844972296266208109 := by
  unfold tailWord_7383
  simp only [CollatzResearch.WordTrace]
  refine ⟨269280132260126761122803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179520088173417840748535 269280132260126761122803)
  ·
    refine ⟨403920198390190141684205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269280132260126761122803 403920198390190141684205)
    ·
      refine ⟨151470074396321303131577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403920198390190141684205 151470074396321303131577)
      ·
        refine ⟨113602555797240977348683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151470074396321303131577 113602555797240977348683)
        ·
          refine ⟨170403833695861466023025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113602555797240977348683 170403833695861466023025)
          ·
            refine ⟨127802875271896099517269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170403833695861466023025 127802875271896099517269)
            ·
              refine ⟨748844972296266208109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 127802875271896099517269 748844972296266208109)
              ·
                rfl

theorem cell19_7383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_7383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7383 prefixEnd_7383 := by exact prefixLift 7383
  have htrace : WordTrace (prefixWord ++ tailWord_7383) baseStart_7383 baseEnd_7383 := by
    simpa [prefixWord, tailWord_7383, baseEnd_7383] using wordTrace_append hprefix tailTrace_7383
  have hstable : (prefixWord ++ tailWord_7383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383).length < 2 ^ (prefixWord ++ tailWord_7383).sum := by decide
  have hdescent : baseEnd_7383 < baseStart_7383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7400 : List Nat := [2, 1, 4, 1, 2, 1, 4, 4]
def baseStart_7400 : Nat := 118140960795 + 7400 * 2 ^ 59
def prefixEnd_7400 : Nat := 4983230072969 + 3 ^ 40 * 7400 * 2
def baseEnd_7400 : Nat := 2251707759037796246503

theorem tailTrace_7400 : CollatzResearch.WordTrace tailWord_7400 prefixEnd_7400 2251707759037796246503 := by
  unfold tailWord_7400
  simp only [CollatzResearch.WordTrace]
  refine ⟨134950086599269332245827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179933448799025776327769 134950086599269332245827)
  ·
    refine ⟨202425129898903998368741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134950086599269332245827 202425129898903998368741)
    ·
      refine ⟨37954711856044499694139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202425129898903998368741 37954711856044499694139)
      ·
        refine ⟨56932067784066749541209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37954711856044499694139 56932067784066749541209)
        ·
          refine ⟨42699050838050062155907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56932067784066749541209 42699050838050062155907)
          ·
            refine ⟨64048576257075093233861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42699050838050062155907 64048576257075093233861)
            ·
              refine ⟨12009108048201579981349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64048576257075093233861 12009108048201579981349)
              ·
                refine ⟨2251707759037796246503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12009108048201579981349 2251707759037796246503)
                ·
                  rfl

theorem cell19_7400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_7400 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7400 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7400 prefixEnd_7400 := by exact prefixLift 7400
  have htrace : WordTrace (prefixWord ++ tailWord_7400) baseStart_7400 baseEnd_7400 := by
    simpa [prefixWord, tailWord_7400, baseEnd_7400] using wordTrace_append hprefix tailTrace_7400
  have hstable : (prefixWord ++ tailWord_7400).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7400).length < 2 ^ (prefixWord ++ tailWord_7400).sum := by decide
  have hdescent : baseEnd_7400 < baseStart_7400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455 : List Nat := [1, 1, 2, 4, 4, 2, 1, 4]
def baseStart_7455 : Nat := 118140960795 + 7455 * 2 ^ 59
def prefixEnd_7455 : Nat := 4983230072969 + 3 ^ 40 * 7455 * 2
def baseEnd_7455 : Nat := 2268443424813965024131

theorem tailTrace_7455 : CollatzResearch.WordTrace tailWord_7455 prefixEnd_7455 2268443424813965024131 := by
  unfold tailWord_7455
  simp only [CollatzResearch.WordTrace]
  refine ⟨271906187999283057743819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181270791999522038495879 271906187999283057743819)
  ·
    refine ⟨407859281998924586615729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271906187999283057743819 407859281998924586615729)
    ·
      refine ⟨305894461499193439961797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407859281998924586615729 305894461499193439961797)
      ·
        refine ⟨57355211531098769992837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305894461499193439961797 57355211531098769992837)
        ·
          refine ⟨10754102162081019373657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57355211531098769992837 10754102162081019373657)
          ·
            refine ⟨8065576621560764530243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10754102162081019373657 8065576621560764530243)
            ·
              refine ⟨12098364932341146795365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8065576621560764530243 12098364932341146795365)
              ·
                refine ⟨2268443424813965024131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12098364932341146795365 2268443424813965024131)
                ·
                  rfl

theorem cell19_7455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_7455 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7455 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7455 prefixEnd_7455 := by exact prefixLift 7455
  have htrace : WordTrace (prefixWord ++ tailWord_7455) baseStart_7455 baseEnd_7455 := by
    simpa [prefixWord, tailWord_7455, baseEnd_7455] using wordTrace_append hprefix tailTrace_7455
  have hstable : (prefixWord ++ tailWord_7455).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455).length < 2 ^ (prefixWord ++ tailWord_7455).sum := by decide
  have hdescent : baseEnd_7455 < baseStart_7455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474 : List Nat := [3, 2, 1, 1, 4, 2, 3, 3]
def baseStart_7474 : Nat := 118140960795 + 7474 * 2 ^ 59
def prefixEnd_7474 : Nat := 4983230072969 + 3 ^ 40 * 7474 * 2
def baseEnd_7474 : Nat := 2274224836627550601857

theorem tailTrace_7474 : CollatzResearch.WordTrace tailWord_7474 prefixEnd_7474 2274224836627550601857 := by
  unfold tailWord_7474
  simp only [CollatzResearch.WordTrace]
  refine ⟨68149793732612325671369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181732783286966201790317 68149793732612325671369)
  ·
    refine ⟨51112345299459244253527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68149793732612325671369 51112345299459244253527)
    ·
      refine ⟨76668517949188866380291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51112345299459244253527 76668517949188866380291)
      ·
        refine ⟨115002776923783299570437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76668517949188866380291 115002776923783299570437)
        ·
          refine ⟨21563020673209368669457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115002776923783299570437 21563020673209368669457)
          ·
            refine ⟨16172265504907026502093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21563020673209368669457 16172265504907026502093)
            ·
              refine ⟨6064599564340134938285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16172265504907026502093 6064599564340134938285)
              ·
                refine ⟨2274224836627550601857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6064599564340134938285 2274224836627550601857)
                ·
                  rfl

theorem cell19_7474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_7474 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7474 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7474 prefixEnd_7474 := by exact prefixLift 7474
  have htrace : WordTrace (prefixWord ++ tailWord_7474) baseStart_7474 baseEnd_7474 := by
    simpa [prefixWord, tailWord_7474, baseEnd_7474] using wordTrace_append hprefix tailTrace_7474
  have hstable : (prefixWord ++ tailWord_7474).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474).length < 2 ^ (prefixWord ++ tailWord_7474).sum := by decide
  have hdescent : baseEnd_7474 < baseStart_7474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7533 : List Nat := [1, 5, 1, 1, 1, 4, 1, 5]
def baseStart_7533 : Nat := 118140960795 + 7533 * 2 ^ 59
def prefixEnd_7533 : Nat := 4983230072969 + 3 ^ 40 * 7533 * 2
def baseEnd_7533 : Nat := 2292177641732895290585

theorem tailTrace_7533 : CollatzResearch.WordTrace tailWord_7533 prefixEnd_7533 2292177641732895290585 := by
  unfold tailWord_7533
  simp only [CollatzResearch.WordTrace]
  refine ⟨274751081716702379083253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183167387811134919388835 274751081716702379083253)
  ·
    refine ⟨25757913910940848039055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274751081716702379083253 25757913910940848039055)
    ·
      refine ⟨38636870866411272058583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25757913910940848039055 38636870866411272058583)
      ·
        refine ⟨57955306299616908087875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38636870866411272058583 57955306299616908087875)
        ·
          refine ⟨86932959449425362131813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57955306299616908087875 86932959449425362131813)
          ·
            refine ⟨16299929896767255399715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86932959449425362131813 16299929896767255399715)
            ·
              refine ⟨24449894845150883099573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16299929896767255399715 24449894845150883099573)
              ·
                refine ⟨2292177641732895290585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24449894845150883099573 2292177641732895290585)
                ·
                  rfl

theorem cell19_7533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_7533 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7533 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7533 prefixEnd_7533 := by exact prefixLift 7533
  have htrace : WordTrace (prefixWord ++ tailWord_7533) baseStart_7533 baseEnd_7533 := by
    simpa [prefixWord, tailWord_7533, baseEnd_7533] using wordTrace_append hprefix tailTrace_7533
  have hstable : (prefixWord ++ tailWord_7533).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7533).length < 2 ^ (prefixWord ++ tailWord_7533).sum := by decide
  have hdescent : baseEnd_7533 < baseStart_7533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7535 : List Nat := [1, 1, 2, 1, 3, 1, 5, 5]
def baseStart_7535 : Nat := 118140960795 + 7535 * 2 ^ 59
def prefixEnd_7535 : Nat := 4983230072969 + 3 ^ 40 * 7535 * 2
def baseEnd_7535 : Nat := 2292786211397483246135

theorem tailTrace_7535 : CollatzResearch.WordTrace tailWord_7535 prefixEnd_7535 2292786211397483246135 := by
  unfold tailWord_7535
  simp only [CollatzResearch.WordTrace]
  refine ⟨274824027709456720656059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183216018472971147104039 274824027709456720656059)
  ·
    refine ⟨412236041564185080984089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274824027709456720656059 412236041564185080984089)
    ·
      refine ⟨309177031173138810738067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412236041564185080984089 309177031173138810738067)
      ·
        refine ⟨463765546759708216107101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309177031173138810738067 463765546759708216107101)
        ·
          refine ⟨173912080034890581040163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463765546759708216107101 173912080034890581040163)
          ·
            refine ⟨260868120052335871560245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173912080034890581040163 260868120052335871560245)
            ·
              refine ⟨24456386254906487958773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 260868120052335871560245 24456386254906487958773)
              ·
                refine ⟨2292786211397483246135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24456386254906487958773 2292786211397483246135)
                ·
                  rfl

theorem cell19_7535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_7535 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7535 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7535 prefixEnd_7535 := by exact prefixLift 7535
  have htrace : WordTrace (prefixWord ++ tailWord_7535) baseStart_7535 baseEnd_7535 := by
    simpa [prefixWord, tailWord_7535, baseEnd_7535] using wordTrace_append hprefix tailTrace_7535
  have hstable : (prefixWord ++ tailWord_7535).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7535).length < 2 ^ (prefixWord ++ tailWord_7535).sum := by decide
  have hdescent : baseEnd_7535 < baseStart_7535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573 : List Nat := [1, 3, 2, 1, 1, 2, 3, 6]
def baseStart_7573 : Nat := 118140960795 + 7573 * 2 ^ 59
def prefixEnd_7573 : Nat := 4983230072969 + 3 ^ 40 * 7573 * 2
def baseEnd_7573 : Nat := 2304349035024654401587

theorem tailTrace_7573 : CollatzResearch.WordTrace tailWord_7573 prefixEnd_7573 2304349035024654401587 := by
  unfold tailWord_7573
  simp only [CollatzResearch.WordTrace]
  refine ⟨276210001571789210539373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184140001047859473692915 276210001571789210539373)
  ·
    refine ⟨103578750589420953952265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276210001571789210539373 103578750589420953952265)
    ·
      refine ⟨77684062942065715464199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103578750589420953952265 77684062942065715464199)
      ·
        refine ⟨116526094413098573196299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77684062942065715464199 116526094413098573196299)
        ·
          refine ⟨174789141619647859794449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116526094413098573196299 174789141619647859794449)
          ·
            refine ⟨131091856214735894845837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174789141619647859794449 131091856214735894845837)
            ·
              refine ⟨49159446080525960567189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131091856214735894845837 49159446080525960567189)
              ·
                refine ⟨2304349035024654401587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49159446080525960567189 2304349035024654401587)
                ·
                  rfl

theorem cell19_7573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_7573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7573 prefixEnd_7573 := by exact prefixLift 7573
  have htrace : WordTrace (prefixWord ++ tailWord_7573) baseStart_7573 baseEnd_7573 := by
    simpa [prefixWord, tailWord_7573, baseEnd_7573] using wordTrace_append hprefix tailTrace_7573
  have hstable : (prefixWord ++ tailWord_7573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573).length < 2 ^ (prefixWord ++ tailWord_7573).sum := by decide
  have hdescent : baseEnd_7573 < baseStart_7573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609 : List Nat := [1, 2, 1, 4, 5, 6]
def baseStart_7609 : Nat := 118140960795 + 7609 * 2 ^ 59
def prefixEnd_7609 : Nat := 4983230072969 + 3 ^ 40 * 7609 * 2
def baseEnd_7609 : Nat := 257255920998581955721

theorem tailTrace_7609 : CollatzResearch.WordTrace tailWord_7609 prefixEnd_7609 257255920998581955721 := by
  unfold tailWord_7609
  simp only [CollatzResearch.WordTrace]
  refine ⟨277523029441367358849881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185015352960911572566587 277523029441367358849881)
  ·
    refine ⟨208142272081025519137411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277523029441367358849881 208142272081025519137411)
    ·
      refine ⟨312213408121538278706117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208142272081025519137411 312213408121538278706117)
      ·
        refine ⟨58540014022788427257397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312213408121538278706117 58540014022788427257397)
        ·
          refine ⟨5488126314636415055381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58540014022788427257397 5488126314636415055381)
          ·
            refine ⟨257255920998581955721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5488126314636415055381 257255920998581955721)
            ·
              rfl

theorem cell19_7609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 6].length) (baseStart_7609 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7609 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7609 prefixEnd_7609 := by exact prefixLift 7609
  have htrace : WordTrace (prefixWord ++ tailWord_7609) baseStart_7609 baseEnd_7609 := by
    simpa [prefixWord, tailWord_7609, baseEnd_7609] using wordTrace_append hprefix tailTrace_7609
  have hstable : (prefixWord ++ tailWord_7609).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609).length < 2 ^ (prefixWord ++ tailWord_7609).sum := by decide
  have hdescent : baseEnd_7609 < baseStart_7609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7618 : List Nat := [3, 5, 2, 1, 2, 1, 1, 4]
def baseStart_7618 : Nat := 118140960795 + 7618 * 2 ^ 59
def prefixEnd_7618 : Nat := 4983230072969 + 3 ^ 40 * 7618 * 2
def baseEnd_7618 : Nat := 2318041852477883401465

theorem tailTrace_7618 : CollatzResearch.WordTrace tailWord_7618 prefixEnd_7618 2318041852477883401465 := by
  unfold tailWord_7618
  simp only [CollatzResearch.WordTrace]
  refine ⟨69462821602190473981877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185234190939174597285005 69462821602190473981877)
  ·
    refine ⟨6512139525205356935801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69462821602190473981877 6512139525205356935801)
    ·
      refine ⟨4884104643904017701851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6512139525205356935801 4884104643904017701851)
      ·
        refine ⟨7326156965856026552777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4884104643904017701851 7326156965856026552777)
        ·
          refine ⟨5494617724392019914583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7326156965856026552777 5494617724392019914583)
          ·
            refine ⟨8241926586588029871875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5494617724392019914583 8241926586588029871875)
            ·
              refine ⟨12362889879882044807813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241926586588029871875 12362889879882044807813)
              ·
                refine ⟨2318041852477883401465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12362889879882044807813 2318041852477883401465)
                ·
                  rfl

theorem cell19_7618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_7618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7618 prefixEnd_7618 := by exact prefixLift 7618
  have htrace : WordTrace (prefixWord ++ tailWord_7618) baseStart_7618 baseEnd_7618 := by
    simpa [prefixWord, tailWord_7618, baseEnd_7618] using wordTrace_append hprefix tailTrace_7618
  have hstable : (prefixWord ++ tailWord_7618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7618).length < 2 ^ (prefixWord ++ tailWord_7618).sum := by decide
  have hdescent : baseEnd_7618 < baseStart_7618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628 : List Nat := [2, 2, 1, 4, 2, 1, 3, 4]
def baseStart_7628 : Nat := 118140960795 + 7628 * 2 ^ 59
def prefixEnd_7628 : Nat := 4983230072969 + 3 ^ 40 * 7628 * 2
def baseEnd_7628 : Nat := 2321084700800823179215

theorem tailTrace_7628 : CollatzResearch.WordTrace tailWord_7628 prefixEnd_7628 2321084700800823179215 := by
  unfold tailWord_7628
  simp only [CollatzResearch.WordTrace]
  refine ⟨139108008186266801895769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185477344248355735861025 139108008186266801895769)
  ·
    refine ⟨104331006139700101421827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139108008186266801895769 104331006139700101421827)
    ·
      refine ⟨156496509209550152132741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104331006139700101421827 156496509209550152132741)
      ·
        refine ⟨29343095476790653524889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156496509209550152132741 29343095476790653524889)
        ·
          refine ⟨22007321607592990143667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29343095476790653524889 22007321607592990143667)
          ·
            refine ⟨33010982411389485215501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22007321607592990143667 33010982411389485215501)
            ·
              refine ⟨12379118404271056955813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33010982411389485215501 12379118404271056955813)
              ·
                refine ⟨2321084700800823179215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12379118404271056955813 2321084700800823179215)
                ·
                  rfl

theorem cell19_7628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_7628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7628 prefixEnd_7628 := by exact prefixLift 7628
  have htrace : WordTrace (prefixWord ++ tailWord_7628) baseStart_7628 baseEnd_7628 := by
    simpa [prefixWord, tailWord_7628, baseEnd_7628] using wordTrace_append hprefix tailTrace_7628
  have hstable : (prefixWord ++ tailWord_7628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628).length < 2 ^ (prefixWord ++ tailWord_7628).sum := by decide
  have hdescent : baseEnd_7628 < baseStart_7628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645 : List Nat := [1, 4, 3, 1, 1, 3, 3, 3]
def baseStart_7645 : Nat := 118140960795 + 7645 * 2 ^ 59
def prefixEnd_7645 : Nat := 4983230072969 + 3 ^ 40 * 7645 * 2
def baseEnd_7645 : Nat := 2326257542949820801391

theorem tailTrace_7645 : CollatzResearch.WordTrace tailWord_7645 prefixEnd_7645 2326257542949820801391 := by
  unfold tailWord_7645
  simp only [CollatzResearch.WordTrace]
  refine ⟨278836057310945507160389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185890704873963671440259 278836057310945507160389)
  ·
    refine ⟨52281760745802282592573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278836057310945507160389 52281760745802282592573)
    ·
      refine ⟨19605660279675855972215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52281760745802282592573 19605660279675855972215)
      ·
        refine ⟨29408490419513783958323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19605660279675855972215 29408490419513783958323)
        ·
          refine ⟨44112735629270675937485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29408490419513783958323 44112735629270675937485)
          ·
            refine ⟨16542275860976503476557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44112735629270675937485 16542275860976503476557)
            ·
              refine ⟨6203353447866188803709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16542275860976503476557 6203353447866188803709)
              ·
                refine ⟨2326257542949820801391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6203353447866188803709 2326257542949820801391)
                ·
                  rfl

theorem cell19_7645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 3].length) (baseStart_7645 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7645 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7645 prefixEnd_7645 := by exact prefixLift 7645
  have htrace : WordTrace (prefixWord ++ tailWord_7645) baseStart_7645 baseEnd_7645 := by
    simpa [prefixWord, tailWord_7645, baseEnd_7645] using wordTrace_append hprefix tailTrace_7645
  have hstable : (prefixWord ++ tailWord_7645).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645).length < 2 ^ (prefixWord ++ tailWord_7645).sum := by decide
  have hdescent : baseEnd_7645 < baseStart_7645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647 : List Nat := [1, 1, 2, 3, 3, 1, 5, 3]
def baseStart_7647 : Nat := 118140960795 + 7647 * 2 ^ 59
def prefixEnd_7647 : Nat := 4983230072969 + 3 ^ 40 * 7647 * 2
def baseEnd_7647 : Nat := 2326866112614408756941

theorem tailTrace_7647 : CollatzResearch.WordTrace tailWord_7647 prefixEnd_7647 2326866112614408756941 := by
  unfold tailWord_7647
  simp only [CollatzResearch.WordTrace]
  refine ⟨278909003303699848733195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185939335535799899155463 278909003303699848733195)
  ·
    refine ⟨418363504955549773099793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278909003303699848733195 418363504955549773099793)
    ·
      refine ⟨313772628716662329824845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418363504955549773099793 313772628716662329824845)
      ·
        refine ⟨117664735768748373684317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313772628716662329824845 117664735768748373684317)
        ·
          refine ⟨44124275913280640131619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117664735768748373684317 44124275913280640131619)
          ·
            refine ⟨66186413869920960197429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44124275913280640131619 66186413869920960197429)
            ·
              refine ⟨6204976300305090018509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66186413869920960197429 6204976300305090018509)
              ·
                refine ⟨2326866112614408756941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6204976300305090018509 2326866112614408756941)
                ·
                  rfl

theorem cell19_7647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 3].length) (baseStart_7647 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7647 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7647 prefixEnd_7647 := by exact prefixLift 7647
  have htrace : WordTrace (prefixWord ++ tailWord_7647) baseStart_7647 baseEnd_7647 := by
    simpa [prefixWord, tailWord_7647, baseEnd_7647] using wordTrace_append hprefix tailTrace_7647
  have hstable : (prefixWord ++ tailWord_7647).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647).length < 2 ^ (prefixWord ++ tailWord_7647).sum := by decide
  have hdescent : baseEnd_7647 < baseStart_7647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7666 : List Nat := [3, 2, 1, 4, 1, 2, 6]
def baseStart_7666 : Nat := 118140960795 + 7666 * 2 ^ 59
def prefixEnd_7666 : Nat := 4983230072969 + 3 ^ 40 * 7666 * 2
def baseEnd_7666 : Nat := 777549174809331444889

theorem tailTrace_7666 : CollatzResearch.WordTrace tailWord_7666 prefixEnd_7666 777549174809331444889 := by
  unfold tailWord_7666
  simp only [CollatzResearch.WordTrace]
  refine ⟨69900497558716523418713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186401326823244062449901 69900497558716523418713)
  ·
    refine ⟨52425373169037392564035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69900497558716523418713 52425373169037392564035)
    ·
      refine ⟨78638059753556088846053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52425373169037392564035 78638059753556088846053)
      ·
        refine ⟨14744636203791766658635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78638059753556088846053 14744636203791766658635)
        ·
          refine ⟨22116954305687649987953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14744636203791766658635 22116954305687649987953)
          ·
            refine ⟨16587715729265737490965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22116954305687649987953 16587715729265737490965)
            ·
              refine ⟨777549174809331444889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16587715729265737490965 777549174809331444889)
              ·
                rfl

theorem cell19_7666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 6].length) (baseStart_7666 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7666 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7666 prefixEnd_7666 := by exact prefixLift 7666
  have htrace : WordTrace (prefixWord ++ tailWord_7666) baseStart_7666 baseEnd_7666 := by
    simpa [prefixWord, tailWord_7666, baseEnd_7666] using wordTrace_append hprefix tailTrace_7666
  have hstable : (prefixWord ++ tailWord_7666).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7666).length < 2 ^ (prefixWord ++ tailWord_7666).sum := by decide
  have hdescent : baseEnd_7666 < baseStart_7666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704 : List Nat := [2, 1, 2, 3, 4, 1, 1, 5]
def baseStart_7704 : Nat := 118140960795 + 7704 * 2 ^ 59
def prefixEnd_7704 : Nat := 4983230072969 + 3 ^ 40 * 7704 * 2
def baseEnd_7704 : Nat := 2344210348055165490119

theorem tailTrace_7704 : CollatzResearch.WordTrace tailWord_7704 prefixEnd_7704 2344210348055165490119 := by
  unfold tailWord_7704
  simp only [CollatzResearch.WordTrace]
  refine ⟨140493982048599291779083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187325309398132389038777 140493982048599291779083)
  ·
    refine ⟨210740973072898937668625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140493982048599291779083 210740973072898937668625)
    ·
      refine ⟨158055729804674203251469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210740973072898937668625 158055729804674203251469)
      ·
        refine ⟨59270898676752826219301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158055729804674203251469 59270898676752826219301)
        ·
          refine ⟨11113293501891154916119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59270898676752826219301 11113293501891154916119)
          ·
            refine ⟨16669940252836732374179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11113293501891154916119 16669940252836732374179)
            ·
              refine ⟨25004910379255098561269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16669940252836732374179 25004910379255098561269)
              ·
                refine ⟨2344210348055165490119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25004910379255098561269 2344210348055165490119)
                ·
                  rfl

theorem cell19_7704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_7704 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7704 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7704 prefixEnd_7704 := by exact prefixLift 7704
  have htrace : WordTrace (prefixWord ++ tailWord_7704) baseStart_7704 baseEnd_7704 := by
    simpa [prefixWord, tailWord_7704, baseEnd_7704] using wordTrace_append hprefix tailTrace_7704
  have hstable : (prefixWord ++ tailWord_7704).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704).length < 2 ^ (prefixWord ++ tailWord_7704).sum := by decide
  have hdescent : baseEnd_7704 < baseStart_7704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797 : List Nat := [1, 3, 4, 2, 1, 3, 1, 4]
def baseStart_7797 : Nat := 118140960795 + 7797 * 2 ^ 59
def prefixEnd_7797 : Nat := 4983230072969 + 3 ^ 40 * 7797 * 2
def baseEnd_7797 : Nat := 2372508837458505423199

theorem tailTrace_7797 : CollatzResearch.WordTrace tailWord_7797 prefixEnd_7797 2372508837458505423199 := by
  unfold tailWord_7797
  simp only [CollatzResearch.WordTrace]
  refine ⟨284379952760275466693645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189586635173516977795763 284379952760275466693645)
  ·
    refine ⟨106642482285103300010117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284379952760275466693645 106642482285103300010117)
    ·
      refine ⟨19995465428456868751897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106642482285103300010117 19995465428456868751897)
      ·
        refine ⟨14996599071342651563923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19995465428456868751897 14996599071342651563923)
        ·
          refine ⟨22494898607013977345885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14996599071342651563923 22494898607013977345885)
          ·
            refine ⟨8435586977630241504707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22494898607013977345885 8435586977630241504707)
            ·
              refine ⟨12653380466445362257061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8435586977630241504707 12653380466445362257061)
              ·
                refine ⟨2372508837458505423199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12653380466445362257061 2372508837458505423199)
                ·
                  rfl

theorem cell19_7797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_7797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7797 prefixEnd_7797 := by exact prefixLift 7797
  have htrace : WordTrace (prefixWord ++ tailWord_7797) baseStart_7797 baseEnd_7797 := by
    simpa [prefixWord, tailWord_7797, baseEnd_7797] using wordTrace_append hprefix tailTrace_7797
  have hstable : (prefixWord ++ tailWord_7797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797).length < 2 ^ (prefixWord ++ tailWord_7797).sum := by decide
  have hdescent : baseEnd_7797 < baseStart_7797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911 : List Nat := [1, 1, 5, 4, 1, 1, 2, 4]
def baseStart_7911 : Nat := 118140960795 + 7911 * 2 ^ 59
def prefixEnd_7911 : Nat := 4983230072969 + 3 ^ 40 * 7911 * 2
def baseEnd_7911 : Nat := 2407197308340018889555

theorem tailTrace_7911 : CollatzResearch.WordTrace tailWord_7911 prefixEnd_7911 2407197308340018889555 := by
  unfold tailWord_7911
  simp only [CollatzResearch.WordTrace]
  refine ⟨288537874347272936343587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192358582898181957562391 288537874347272936343587)
  ·
    refine ⟨432806811520909404515381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288537874347272936343587 432806811520909404515381)
    ·
      refine ⟨40575638580085256673317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 432806811520909404515381 40575638580085256673317)
      ·
        refine ⟨7607932233765985626247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40575638580085256673317 7607932233765985626247)
        ·
          refine ⟨11411898350648978439371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7607932233765985626247 11411898350648978439371)
          ·
            refine ⟨17117847525973467659057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11411898350648978439371 17117847525973467659057)
            ·
              refine ⟨12838385644480100744293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17117847525973467659057 12838385644480100744293)
              ·
                refine ⟨2407197308340018889555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12838385644480100744293 2407197308340018889555)
                ·
                  rfl

theorem cell19_7911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 4].length) (baseStart_7911 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_7911 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_7911 prefixEnd_7911 := by exact prefixLift 7911
  have htrace : WordTrace (prefixWord ++ tailWord_7911) baseStart_7911 baseEnd_7911 := by
    simpa [prefixWord, tailWord_7911, baseEnd_7911] using wordTrace_append hprefix tailTrace_7911
  have hstable : (prefixWord ++ tailWord_7911).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911).length < 2 ^ (prefixWord ++ tailWord_7911).sum := by decide
  have hdescent : baseEnd_7911 < baseStart_7911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006 : List Nat := [6, 1, 1, 2, 1, 2, 6]
def baseStart_8006 : Nat := 118140960795 + 8006 * 2 ^ 59
def prefixEnd_8006 : Nat := 4983230072969 + 3 ^ 40 * 8006 * 2
def baseEnd_8006 : Nat := 812034789135982259395

theorem tailTrace_8006 : CollatzResearch.WordTrace tailWord_8006 prefixEnd_8006 812034789135982259395 := by
  unfold tailWord_8006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9125087781347005032871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194668539335402774034581 9125087781347005032871)
  ·
    refine ⟨13687631672020507549307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9125087781347005032871 13687631672020507549307)
    ·
      refine ⟨20531447508030761323961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13687631672020507549307 20531447508030761323961)
      ·
        refine ⟨15398585631023070992971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20531447508030761323961 15398585631023070992971)
        ·
          refine ⟨23097878446534606489457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15398585631023070992971 23097878446534606489457)
          ·
            refine ⟨17323408834900954867093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23097878446534606489457 17323408834900954867093)
            ·
              refine ⟨812034789135982259395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17323408834900954867093 812034789135982259395)
              ·
                rfl

theorem cell19_8006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 6].length) (baseStart_8006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8006 prefixEnd_8006 := by exact prefixLift 8006
  have htrace : WordTrace (prefixWord ++ tailWord_8006) baseStart_8006 baseEnd_8006 := by
    simpa [prefixWord, tailWord_8006, baseEnd_8006] using wordTrace_append hprefix tailTrace_8006
  have hstable : (prefixWord ++ tailWord_8006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006).length < 2 ^ (prefixWord ++ tailWord_8006).sum := by decide
  have hdescent : baseEnd_8006 < baseStart_8006 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042 : List Nat := [3, 1, 3, 4, 1, 2, 2, 3]
def baseStart_8042 : Nat := 118140960795 + 8042 * 2 ^ 59
def prefixEnd_8042 : Nat := 4983230072969 + 3 ^ 40 * 8042 * 2
def baseEnd_8042 : Nat := 2447058621370529978087

theorem tailTrace_8042 : CollatzResearch.WordTrace tailWord_8042 prefixEnd_8042 2447058621370529978087 := by
  unfold tailWord_8042
  simp only [CollatzResearch.WordTrace]
  refine ⟨73328959218170577340595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195543891248454872908253 73328959218170577340595)
  ·
    refine ⟨109993438827255866010893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73328959218170577340595 109993438827255866010893)
    ·
      refine ⟨41247539560220949754085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109993438827255866010893 41247539560220949754085)
      ·
        refine ⟨7733913667541428078891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41247539560220949754085 7733913667541428078891)
        ·
          refine ⟨11600870501312142118337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7733913667541428078891 11600870501312142118337)
          ·
            refine ⟨8700652875984106588753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11600870501312142118337 8700652875984106588753)
            ·
              refine ⟨6525489656988079941565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8700652875984106588753 6525489656988079941565)
              ·
                refine ⟨2447058621370529978087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6525489656988079941565 2447058621370529978087)
                ·
                  rfl

theorem cell19_8042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_8042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8042 prefixEnd_8042 := by exact prefixLift 8042
  have htrace : WordTrace (prefixWord ++ tailWord_8042) baseStart_8042 baseEnd_8042 := by
    simpa [prefixWord, tailWord_8042, baseEnd_8042] using wordTrace_append hprefix tailTrace_8042
  have hstable : (prefixWord ++ tailWord_8042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042).length < 2 ^ (prefixWord ++ tailWord_8042).sum := by decide
  have hdescent : baseEnd_8042 < baseStart_8042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046 : List Nat := [4, 1, 2, 3, 1, 2, 1, 5]
def baseStart_8046 : Nat := 118140960795 + 8046 * 2 ^ 59
def prefixEnd_8046 : Nat := 4983230072969 + 3 ^ 40 * 8046 * 2
def baseEnd_8046 : Nat := 2448275760699705889187

theorem tailTrace_8046 : CollatzResearch.WordTrace tailWord_8046 prefixEnd_8046 2448275760699705889187 := by
  unfold tailWord_8046
  simp only [CollatzResearch.WordTrace]
  refine ⟨36682716107273874063499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195641152572127328338661 36682716107273874063499)
  ·
    refine ⟨55024074160910811095249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36682716107273874063499 55024074160910811095249)
    ·
      refine ⟨41268055620683108321437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55024074160910811095249 41268055620683108321437)
      ·
        refine ⟨15475520857756165620539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41268055620683108321437 15475520857756165620539)
        ·
          refine ⟨23213281286634248430809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15475520857756165620539 23213281286634248430809)
          ·
            refine ⟨17409960964975686323107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23213281286634248430809 17409960964975686323107)
            ·
              refine ⟨26114941447463529484661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17409960964975686323107 26114941447463529484661)
              ·
                refine ⟨2448275760699705889187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26114941447463529484661 2448275760699705889187)
                ·
                  rfl

theorem cell19_8046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_8046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8046 prefixEnd_8046 := by exact prefixLift 8046
  have htrace : WordTrace (prefixWord ++ tailWord_8046) baseStart_8046 baseEnd_8046 := by
    simpa [prefixWord, tailWord_8046, baseEnd_8046] using wordTrace_append hprefix tailTrace_8046
  have hstable : (prefixWord ++ tailWord_8046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046).length < 2 ^ (prefixWord ++ tailWord_8046).sum := by decide
  have hdescent : baseEnd_8046 < baseStart_8046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067 : List Nat := [1, 1, 1, 3, 4, 4, 5]
def baseStart_8067 : Nat := 118140960795 + 8067 * 2 ^ 59
def prefixEnd_8067 : Nat := 4983230072969 + 3 ^ 40 * 8067 * 2
def baseEnd_8067 : Nat := 818221914059293140821

theorem tailTrace_8067 : CollatzResearch.WordTrace tailWord_8067 prefixEnd_8067 818221914059293140821 := by
  unfold tailWord_8067
  simp only [CollatzResearch.WordTrace]
  refine ⟨294227661782111579022455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196151774521407719348303 294227661782111579022455)
  ·
    refine ⟨441341492673167368533683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294227661782111579022455 441341492673167368533683)
    ·
      refine ⟨662012239009751052800525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441341492673167368533683 662012239009751052800525)
      ·
        refine ⟨248254589628656644800197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 662012239009751052800525 248254589628656644800197)
        ·
          refine ⟨46547735555373120900037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248254589628656644800197 46547735555373120900037)
          ·
            refine ⟨8727700416632460168757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46547735555373120900037 8727700416632460168757)
            ·
              refine ⟨818221914059293140821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8727700416632460168757 818221914059293140821)
              ·
                rfl

theorem cell19_8067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 5].length) (baseStart_8067 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8067 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8067 prefixEnd_8067 := by exact prefixLift 8067
  have htrace : WordTrace (prefixWord ++ tailWord_8067) baseStart_8067 baseEnd_8067 := by
    simpa [prefixWord, tailWord_8067, baseEnd_8067] using wordTrace_append hprefix tailTrace_8067
  have hstable : (prefixWord ++ tailWord_8067).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067).length < 2 ^ (prefixWord ++ tailWord_8067).sum := by decide
  have hdescent : baseEnd_8067 < baseStart_8067 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084 : List Nat := [2, 4, 2, 1, 1, 3, 2, 4]
def baseStart_8084 : Nat := 118140960795 + 8084 * 2 ^ 59
def prefixEnd_8084 : Nat := 4983230072969 + 3 ^ 40 * 8084 * 2
def baseEnd_8084 : Nat := 2459838584326877044639

theorem tailTrace_8084 : CollatzResearch.WordTrace tailWord_8084 prefixEnd_8084 2459838584326877044639 := by
  unfold tailWord_8084
  simp only [CollatzResearch.WordTrace]
  refine ⟨147423851360261741195653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196565135147015654927537 147423851360261741195653)
  ·
    refine ⟨27641972130049076474185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147423851360261741195653 27641972130049076474185)
    ·
      refine ⟨20731479097536807355639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27641972130049076474185 20731479097536807355639)
      ·
        refine ⟨31097218646305211033459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20731479097536807355639 31097218646305211033459)
        ·
          refine ⟨46645827969457816550189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31097218646305211033459 46645827969457816550189)
          ·
            refine ⟨17492185488546681206321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46645827969457816550189 17492185488546681206321)
            ·
              refine ⟨13119139116410010904741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17492185488546681206321 13119139116410010904741)
              ·
                refine ⟨2459838584326877044639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13119139116410010904741 2459838584326877044639)
                ·
                  rfl

theorem cell19_8084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_8084 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8084 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8084 prefixEnd_8084 := by exact prefixLift 8084
  have htrace : WordTrace (prefixWord ++ tailWord_8084) baseStart_8084 baseEnd_8084 := by
    simpa [prefixWord, tailWord_8084, baseEnd_8084] using wordTrace_append hprefix tailTrace_8084
  have hstable : (prefixWord ++ tailWord_8084).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084).length < 2 ^ (prefixWord ++ tailWord_8084).sum := by decide
  have hdescent : baseEnd_8084 < baseStart_8084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124 : List Nat := [2, 2, 2, 5, 8]
def baseStart_8124 : Nat := 118140960795 + 8124 * 2 ^ 59
def prefixEnd_8124 : Nat := 4983230072969 + 3 ^ 40 * 8124 * 2
def baseEnd_8124 : Nat := 91555925096986524283

theorem tailTrace_8124 : CollatzResearch.WordTrace tailWord_8124 prefixEnd_8124 91555925096986524283 := by
  unfold tailWord_8124
  simp only [CollatzResearch.WordTrace]
  refine ⟨148153311287805156923713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197537748383740209231617 148153311287805156923713)
  ·
    refine ⟨111114983465853867692785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148153311287805156923713 111114983465853867692785)
    ·
      refine ⟨83336237599390400769589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111114983465853867692785 83336237599390400769589)
      ·
        refine ⟨7812772274942850072149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83336237599390400769589 7812772274942850072149)
        ·
          refine ⟨91555925096986524283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 7812772274942850072149 91555925096986524283)
          ·
            rfl

theorem cell19_8124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 8].length) (baseStart_8124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8124 prefixEnd_8124 := by exact prefixLift 8124
  have htrace : WordTrace (prefixWord ++ tailWord_8124) baseStart_8124 baseEnd_8124 := by
    simpa [prefixWord, tailWord_8124, baseEnd_8124] using wordTrace_append hprefix tailTrace_8124
  have hstable : (prefixWord ++ tailWord_8124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124).length < 2 ^ (prefixWord ++ tailWord_8124).sum := by decide
  have hdescent : baseEnd_8124 < baseStart_8124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145 : List Nat := [1, 2, 2, 1, 2, 1, 2, 8]
def baseStart_8145 : Nat := 118140960795 + 8145 * 2 ^ 59
def prefixEnd_8145 : Nat := 4983230072969 + 3 ^ 40 * 8145 * 2
def baseEnd_8145 : Nat := 2478399959096809688917

theorem tailTrace_8145 : CollatzResearch.WordTrace tailWord_8145 prefixEnd_8145 2478399959096809688917 := by
  unfold tailWord_8145
  simp only [CollatzResearch.WordTrace]
  refine ⟨297072555499530900361889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198048370333020600241259 297072555499530900361889)
  ·
    refine ⟨222804416624648175271417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297072555499530900361889 222804416624648175271417)
    ·
      refine ⟨167103312468486131453563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222804416624648175271417 167103312468486131453563)
      ·
        refine ⟨250654968702729197180345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167103312468486131453563 250654968702729197180345)
        ·
          refine ⟨187991226527046897885259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250654968702729197180345 187991226527046897885259)
          ·
            refine ⟨281986839790570346827889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187991226527046897885259 281986839790570346827889)
            ·
              refine ⟨211490129842927760120917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281986839790570346827889 211490129842927760120917)
              ·
                refine ⟨2478399959096809688917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 211490129842927760120917 2478399959096809688917)
                ·
                  rfl

theorem cell19_8145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_8145 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8145 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8145 prefixEnd_8145 := by exact prefixLift 8145
  have htrace : WordTrace (prefixWord ++ tailWord_8145) baseStart_8145 baseEnd_8145 := by
    simpa [prefixWord, tailWord_8145, baseEnd_8145] using wordTrace_append hprefix tailTrace_8145
  have hstable : (prefixWord ++ tailWord_8145).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145).length < 2 ^ (prefixWord ++ tailWord_8145).sum := by decide
  have hdescent : baseEnd_8145 < baseStart_8145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215 : List Nat := [1, 1, 3, 5, 2, 2, 2, 3]
def baseStart_8215 : Nat := 118140960795 + 8215 * 2 ^ 59
def prefixEnd_8215 : Nat := 4983230072969 + 3 ^ 40 * 8215 * 2
def baseEnd_8215 : Nat := 2499699897357388133171

theorem tailTrace_8215 : CollatzResearch.WordTrace tailWord_8215 prefixEnd_8215 2499699897357388133171 := by
  unfold tailWord_8215
  simp only [CollatzResearch.WordTrace]
  refine ⟨299625665245932855410099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199750443497288570273399 299625665245932855410099)
  ·
    refine ⟨449438497868899283115149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299625665245932855410099 449438497868899283115149)
    ·
      refine ⟨168539436700837231168181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449438497868899283115149 168539436700837231168181)
      ·
        refine ⟨15800572190703490422017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168539436700837231168181 15800572190703490422017)
        ·
          refine ⟨11850429143027617816513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15800572190703490422017 11850429143027617816513)
          ·
            refine ⟨8887821857270713362385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11850429143027617816513 8887821857270713362385)
            ·
              refine ⟨6665866392953035021789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8887821857270713362385 6665866392953035021789)
              ·
                refine ⟨2499699897357388133171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6665866392953035021789 2499699897357388133171)
                ·
                  rfl

theorem cell19_8215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 3].length) (baseStart_8215 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8215 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8215 prefixEnd_8215 := by exact prefixLift 8215
  have htrace : WordTrace (prefixWord ++ tailWord_8215) baseStart_8215 baseEnd_8215 := by
    simpa [prefixWord, tailWord_8215, baseEnd_8215] using wordTrace_append hprefix tailTrace_8215
  have hstable : (prefixWord ++ tailWord_8215).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215).length < 2 ^ (prefixWord ++ tailWord_8215).sum := by decide
  have hdescent : baseEnd_8215 < baseStart_8215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8238 : List Nat := [4, 1, 3, 1, 1, 2, 7]
def baseStart_8238 : Nat := 118140960795 + 8238 * 2 ^ 59
def prefixEnd_8238 : Nat := 4983230072969 + 3 ^ 40 * 8238 * 2
def baseEnd_8238 : Nat := 835566149500049873999

theorem tailTrace_8238 : CollatzResearch.WordTrace tailWord_8238 prefixEnd_8238 835566149500049873999 := by
  unfold tailWord_8238
  simp only [CollatzResearch.WordTrace]
  refine ⟨37558068020325972937171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200309696108405188998245 37558068020325972937171)
  ·
    refine ⟨56337102030488959405757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37558068020325972937171 56337102030488959405757)
    ·
      refine ⟨21126413261433359777159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56337102030488959405757 21126413261433359777159)
      ·
        refine ⟨31689619892150039665739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21126413261433359777159 31689619892150039665739)
        ·
          refine ⟨47534429838225059498609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31689619892150039665739 47534429838225059498609)
          ·
            refine ⟨35650822378668794623957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47534429838225059498609 35650822378668794623957)
            ·
              refine ⟨835566149500049873999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35650822378668794623957 835566149500049873999)
              ·
                rfl

theorem cell19_8238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 7].length) (baseStart_8238 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8238 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8238 prefixEnd_8238 := by exact prefixLift 8238
  have htrace : WordTrace (prefixWord ++ tailWord_8238) baseStart_8238 baseEnd_8238 := by
    simpa [prefixWord, tailWord_8238, baseEnd_8238] using wordTrace_append hprefix tailTrace_8238
  have hstable : (prefixWord ++ tailWord_8238).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8238).length < 2 ^ (prefixWord ++ tailWord_8238).sum := by decide
  have hdescent : baseEnd_8238 < baseStart_8238 := by decide
  rcases family_descends (prefixWord ++ tailWord_8238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8240 : List Nat := [2, 1, 1, 1, 2, 5, 7]
def baseStart_8240 : Nat := 118140960795 + 8240 * 2 ^ 59
def prefixEnd_8240 : Nat := 4983230072969 + 3 ^ 40 * 8240 * 2
def baseEnd_8240 : Nat := 835769006054912525849

theorem tailTrace_8240 : CollatzResearch.WordTrace tailWord_8240 prefixEnd_8240 835769006054912525849 := by
  unfold tailWord_8240
  simp only [CollatzResearch.WordTrace]
  refine ⟨150268745077681062535087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200358326770241416713449 150268745077681062535087)
  ·
    refine ⟨225403117616521593802631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150268745077681062535087 225403117616521593802631)
    ·
      refine ⟨338104676424782390703947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225403117616521593802631 338104676424782390703947)
      ·
        refine ⟨507157014637173586055921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338104676424782390703947 507157014637173586055921)
        ·
          refine ⟨380367760977880189541941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507157014637173586055921 380367760977880189541941)
          ·
            refine ⟨35659477591676267769557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 380367760977880189541941 35659477591676267769557)
            ·
              refine ⟨835769006054912525849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35659477591676267769557 835769006054912525849)
              ·
                rfl

theorem cell19_8240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_8240 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8240 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8240 prefixEnd_8240 := by exact prefixLift 8240
  have htrace : WordTrace (prefixWord ++ tailWord_8240) baseStart_8240 baseEnd_8240 := by
    simpa [prefixWord, tailWord_8240, baseEnd_8240] using wordTrace_append hprefix tailTrace_8240
  have hstable : (prefixWord ++ tailWord_8240).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8240).length < 2 ^ (prefixWord ++ tailWord_8240).sum := by decide
  have hdescent : baseEnd_8240 < baseStart_8240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8257 : List Nat := [1, 2, 5, 1, 2, 1, 1, 6]
def baseStart_8257 : Nat := 118140960795 + 8257 * 2 ^ 59
def prefixEnd_8257 : Nat := 4983230072969 + 3 ^ 40 * 8257 * 2
def baseEnd_8257 : Nat := 2512479860313735199723

theorem tailTrace_8257 : CollatzResearch.WordTrace tailWord_8257 prefixEnd_8257 2512479860313735199723 := by
  unfold tailWord_8257
  simp only [CollatzResearch.WordTrace]
  refine ⟨301157531093774028439025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200771687395849352292683 301157531093774028439025)
  ·
    refine ⟨225868148320330521329269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301157531093774028439025 225868148320330521329269)
    ·
      refine ⟨21175138905030986374619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225868148320330521329269 21175138905030986374619)
      ·
        refine ⟨31762708357546479561929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21175138905030986374619 31762708357546479561929)
        ·
          refine ⟨23822031268159859671447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31762708357546479561929 23822031268159859671447)
          ·
            refine ⟨35733046902239789507171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23822031268159859671447 35733046902239789507171)
            ·
              refine ⟨53599570353359684260757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35733046902239789507171 53599570353359684260757)
              ·
                refine ⟨2512479860313735199723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53599570353359684260757 2512479860313735199723)
                ·
                  rfl

theorem cell19_8257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_8257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8257 prefixEnd_8257 := by exact prefixLift 8257
  have htrace : WordTrace (prefixWord ++ tailWord_8257) baseStart_8257 baseEnd_8257 := by
    simpa [prefixWord, tailWord_8257, baseEnd_8257] using wordTrace_append hprefix tailTrace_8257
  have hstable : (prefixWord ++ tailWord_8257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8257).length < 2 ^ (prefixWord ++ tailWord_8257).sum := by decide
  have hdescent : baseEnd_8257 < baseStart_8257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350 : List Nat := [4, 3, 1, 1, 3, 1, 6]
def baseStart_8350 : Nat := 118140960795 + 8350 * 2 ^ 59
def prefixEnd_8350 : Nat := 4983230072969 + 3 ^ 40 * 8350 * 2
def baseEnd_8350 : Nat := 846926116572358377601

theorem tailTrace_8350 : CollatzResearch.WordTrace tailWord_8350 prefixEnd_8350 846926116572358377601 := by
  unfold tailWord_8350
  simp only [CollatzResearch.WordTrace]
  refine ⟨38068689969606363946813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203033013171233941049669 38068689969606363946813)
  ·
    refine ⟨14275758738602386480055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38068689969606363946813 14275758738602386480055)
    ·
      refine ⟨21413638107903579720083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14275758738602386480055 21413638107903579720083)
      ·
        refine ⟨32120457161855369580125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21413638107903579720083 32120457161855369580125)
        ·
          refine ⟨12045171435695763592547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32120457161855369580125 12045171435695763592547)
          ·
            refine ⟨18067757153543645388821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12045171435695763592547 18067757153543645388821)
            ·
              refine ⟨846926116572358377601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18067757153543645388821 846926116572358377601)
              ·
                rfl

theorem cell19_8350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 6].length) (baseStart_8350 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8350 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8350 prefixEnd_8350 := by exact prefixLift 8350
  have htrace : WordTrace (prefixWord ++ tailWord_8350) baseStart_8350 baseEnd_8350 := by
    simpa [prefixWord, tailWord_8350, baseEnd_8350] using wordTrace_append hprefix tailTrace_8350
  have hstable : (prefixWord ++ tailWord_8350).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350).length < 2 ^ (prefixWord ++ tailWord_8350).sum := by decide
  have hdescent : baseEnd_8350 < baseStart_8350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386 : List Nat := [3, 5, 1, 1, 1, 2, 1, 5]
def baseStart_8386 : Nat := 118140960795 + 8386 * 2 ^ 59
def prefixEnd_8386 : Nat := 4983230072969 + 3 ^ 40 * 8386 * 2
def baseEnd_8386 : Nat := 2551732603679658332705

theorem tailTrace_8386 : CollatzResearch.WordTrace tailWord_8386 prefixEnd_8386 2551732603679658332705 := by
  unfold tailWord_8386
  simp only [CollatzResearch.WordTrace]
  refine ⟨76465636906607264971253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203908365084286039923341 76465636906607264971253)
  ·
    refine ⟨7168653459994431091055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76465636906607264971253 7168653459994431091055)
    ·
      refine ⟨10752980189991646636583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7168653459994431091055 10752980189991646636583)
      ·
        refine ⟨16129470284987469954875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10752980189991646636583 16129470284987469954875)
        ·
          refine ⟨24194205427481204932313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16129470284987469954875 24194205427481204932313)
          ·
            refine ⟨18145654070610903699235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24194205427481204932313 18145654070610903699235)
            ·
              refine ⟨27218481105916355548853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18145654070610903699235 27218481105916355548853)
              ·
                refine ⟨2551732603679658332705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27218481105916355548853 2551732603679658332705)
                ·
                  rfl

theorem cell19_8386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_8386 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8386 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8386 prefixEnd_8386 := by exact prefixLift 8386
  have htrace : WordTrace (prefixWord ++ tailWord_8386) baseStart_8386 baseEnd_8386 := by
    simpa [prefixWord, tailWord_8386, baseEnd_8386] using wordTrace_append hprefix tailTrace_8386
  have hstable : (prefixWord ++ tailWord_8386).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386).length < 2 ^ (prefixWord ++ tailWord_8386).sum := by decide
  have hdescent : baseEnd_8386 < baseStart_8386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388 : List Nat := [2, 3, 3, 1, 2, 1, 4, 3]
def baseStart_8388 : Nat := 118140960795 + 8388 * 2 ^ 59
def prefixEnd_8388 : Nat := 4983230072969 + 3 ^ 40 * 8388 * 2
def baseEnd_8388 : Nat := 2552341173344246288255

theorem tailTrace_8388 : CollatzResearch.WordTrace tailWord_8388 prefixEnd_8388 2552341173344246288255 := by
  unfold tailWord_8388
  simp only [CollatzResearch.WordTrace]
  refine ⟨152967746809591700728909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203956995746122267638545 152967746809591700728909)
  ·
    refine ⟨57362905053596887773341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152967746809591700728909 57362905053596887773341)
    ·
      refine ⟨21511089395098832915003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57362905053596887773341 21511089395098832915003)
      ·
        refine ⟨32266634092648249372505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21511089395098832915003 32266634092648249372505)
        ·
          refine ⟨24199975569486187029379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32266634092648249372505 24199975569486187029379)
          ·
            refine ⟨36299963354229280544069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24199975569486187029379 36299963354229280544069)
            ·
              refine ⟨6806243128917990102013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36299963354229280544069 6806243128917990102013)
              ·
                refine ⟨2552341173344246288255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6806243128917990102013 2552341173344246288255)
                ·
                  rfl

theorem cell19_8388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_8388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8388 prefixEnd_8388 := by exact prefixLift 8388
  have htrace : WordTrace (prefixWord ++ tailWord_8388) baseStart_8388 baseEnd_8388 := by
    simpa [prefixWord, tailWord_8388, baseEnd_8388] using wordTrace_append hprefix tailTrace_8388
  have hstable : (prefixWord ++ tailWord_8388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388).length < 2 ^ (prefixWord ++ tailWord_8388).sum := by decide
  have hdescent : baseEnd_8388 < baseStart_8388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8449 : List Nat := [1, 2, 4, 1, 1, 2, 1, 7]
def baseStart_8449 : Nat := 118140960795 + 8449 * 2 ^ 59
def prefixEnd_8449 : Nat := 4983230072969 + 3 ^ 40 * 8449 * 2
def baseEnd_8449 : Nat := 2570902548114178932533

theorem tailTrace_8449 : CollatzResearch.WordTrace tailWord_8449 prefixEnd_8449 2570902548114178932533 := by
  unfold tailWord_8449
  simp only [CollatzResearch.WordTrace]
  refine ⟨308160346398190819428401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 205440230932127212952267 308160346398190819428401)
  ·
    refine ⟨231120259798643114571301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 308160346398190819428401 231120259798643114571301)
    ·
      refine ⟨43335048712245583982119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231120259798643114571301 43335048712245583982119)
      ·
        refine ⟨65002573068368375973179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43335048712245583982119 65002573068368375973179)
        ·
          refine ⟨97503859602552563959769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65002573068368375973179 97503859602552563959769)
          ·
            refine ⟨73127894701914422969827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97503859602552563959769 73127894701914422969827)
            ·
              refine ⟨109691842052871634454741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73127894701914422969827 109691842052871634454741)
              ·
                refine ⟨2570902548114178932533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 109691842052871634454741 2570902548114178932533)
                ·
                  rfl

theorem cell19_8449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_8449 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8449 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8449 prefixEnd_8449 := by exact prefixLift 8449
  have htrace : WordTrace (prefixWord ++ tailWord_8449) baseStart_8449 baseEnd_8449 := by
    simpa [prefixWord, tailWord_8449, baseEnd_8449] using wordTrace_append hprefix tailTrace_8449
  have hstable : (prefixWord ++ tailWord_8449).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8449).length < 2 ^ (prefixWord ++ tailWord_8449).sum := by decide
  have hdescent : baseEnd_8449 < baseStart_8449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8601 : List Nat := [1, 2, 1, 2, 1, 4, 4, 4]
def baseStart_8601 : Nat := 118140960795 + 8601 * 2 ^ 59
def prefixEnd_8601 : Nat := 4983230072969 + 3 ^ 40 * 8601 * 2
def baseEnd_8601 : Nat := 2617153842622863554341

theorem tailTrace_8601 : CollatzResearch.WordTrace tailWord_8601 prefixEnd_8601 2617153842622863554341 := by
  unfold tailWord_8601
  simp only [CollatzResearch.WordTrace]
  refine ⟨313704241847520778961657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 209136161231680519307771 313704241847520778961657)
  ·
    refine ⟨235278181385640584221243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 313704241847520778961657 235278181385640584221243)
    ·
      refine ⟨352917272078460876331865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235278181385640584221243 352917272078460876331865)
      ·
        refine ⟨264687954058845657248899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352917272078460876331865 264687954058845657248899)
        ·
          refine ⟨397031931088268485873349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264687954058845657248899 397031931088268485873349)
          ·
            refine ⟨74443487079050341101253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 397031931088268485873349 74443487079050341101253)
            ·
              refine ⟨13958153827321938956485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74443487079050341101253 13958153827321938956485)
              ·
                refine ⟨2617153842622863554341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13958153827321938956485 2617153842622863554341)
                ·
                  rfl

theorem cell19_8601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_8601 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8601 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8601 prefixEnd_8601 := by exact prefixLift 8601
  have htrace : WordTrace (prefixWord ++ tailWord_8601) baseStart_8601 baseEnd_8601 := by
    simpa [prefixWord, tailWord_8601, baseEnd_8601] using wordTrace_append hprefix tailTrace_8601
  have hstable : (prefixWord ++ tailWord_8601).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8601).length < 2 ^ (prefixWord ++ tailWord_8601).sum := by decide
  have hdescent : baseEnd_8601 < baseStart_8601 := by decide
  rcases family_descends (prefixWord ++ tailWord_8601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8732 : List Nat := [2, 2, 3, 1, 2, 2, 4, 3]
def baseStart_8732 : Nat := 118140960795 + 8732 * 2 ^ 59
def prefixEnd_8732 : Nat := 4983230072969 + 3 ^ 40 * 8732 * 2
def baseEnd_8732 : Nat := 2657015155653374642873

theorem tailTrace_8732 : CollatzResearch.WordTrace tailWord_8732 prefixEnd_8732 2657015155653374642873 := by
  unfold tailWord_8732
  simp only [CollatzResearch.WordTrace]
  refine ⟨159241102186465075990225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 212321469581953434653633 159241102186465075990225)
  ·
    refine ⟨119430826639848806992669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159241102186465075990225 119430826639848806992669)
    ·
      refine ⟨44786559989943302622251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119430826639848806992669 44786559989943302622251)
      ·
        refine ⟨67179839984914953933377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44786559989943302622251 67179839984914953933377)
        ·
          refine ⟨50384879988686215450033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67179839984914953933377 50384879988686215450033)
          ·
            refine ⟨37788659991514661587525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50384879988686215450033 37788659991514661587525)
            ·
              refine ⟨7085373748408999047661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37788659991514661587525 7085373748408999047661)
              ·
                refine ⟨2657015155653374642873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7085373748408999047661 2657015155653374642873)
                ·
                  rfl

theorem cell19_8732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_8732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8732 prefixEnd_8732 := by exact prefixLift 8732
  have htrace : WordTrace (prefixWord ++ tailWord_8732) baseStart_8732 baseEnd_8732 := by
    simpa [prefixWord, tailWord_8732, baseEnd_8732] using wordTrace_append hprefix tailTrace_8732
  have hstable : (prefixWord ++ tailWord_8732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8732).length < 2 ^ (prefixWord ++ tailWord_8732).sum := by decide
  have hdescent : baseEnd_8732 < baseStart_8732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8808 : List Nat := [2, 1, 4, 3, 3, 6]
def baseStart_8808 : Nat := 118140960795 + 8808 * 2 ^ 59
def prefixEnd_8808 : Nat := 4983230072969 + 3 ^ 40 * 8808 * 2
def baseEnd_8808 : Nat := 297793422545301883753

theorem tailTrace_8808 : CollatzResearch.WordTrace tailWord_8808 prefixEnd_8808 297793422545301883753 := by
  unfold tailWord_8808
  simp only [CollatzResearch.WordTrace]
  refine ⟨160627076048797565873539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 214169434731730087831385 160627076048797565873539)
  ·
    refine ⟨240940614073196348810309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160627076048797565873539 240940614073196348810309)
    ·
      refine ⟨45176365138724315401933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240940614073196348810309 45176365138724315401933)
      ·
        refine ⟨16941136927021618275725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45176365138724315401933 16941136927021618275725)
        ·
          refine ⟨6352926347633106853397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16941136927021618275725 6352926347633106853397)
          ·
            refine ⟨297793422545301883753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6352926347633106853397 297793422545301883753)
            ·
              rfl

theorem cell19_8808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 6].length) (baseStart_8808 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8808 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8808 prefixEnd_8808 := by exact prefixLift 8808
  have htrace : WordTrace (prefixWord ++ tailWord_8808) baseStart_8808 baseEnd_8808 := by
    simpa [prefixWord, tailWord_8808, baseEnd_8808] using wordTrace_append hprefix tailTrace_8808
  have hstable : (prefixWord ++ tailWord_8808).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8808).length < 2 ^ (prefixWord ++ tailWord_8808).sum := by decide
  have hdescent : baseEnd_8808 < baseStart_8808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8831 : List Nat := [1, 1, 2, 2, 1, 1, 1, 10]
def baseStart_8831 : Nat := 118140960795 + 8831 * 2 ^ 59
def prefixEnd_8831 : Nat := 4983230072969 + 3 ^ 40 * 8831 * 2
def baseEnd_8831 : Nat := 2687139354050478442603

theorem tailTrace_8831 : CollatzResearch.WordTrace tailWord_8831 prefixEnd_8831 2687139354050478442603 := by
  unfold tailWord_8831
  simp only [CollatzResearch.WordTrace]
  refine ⟨322093031014270059834347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 214728687342846706556231 322093031014270059834347)
  ·
    refine ⟨483139546521405089751521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 322093031014270059834347 483139546521405089751521)
    ·
      refine ⟨362354659891053817313641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 483139546521405089751521 362354659891053817313641)
      ·
        refine ⟨271765994918290362985231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362354659891053817313641 271765994918290362985231)
        ·
          refine ⟨407648992377435544477847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271765994918290362985231 407648992377435544477847)
          ·
            refine ⟨611473488566153316716771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407648992377435544477847 611473488566153316716771)
            ·
              refine ⟨917210232849229975075157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611473488566153316716771 917210232849229975075157)
              ·
                refine ⟨2687139354050478442603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 917210232849229975075157 2687139354050478442603)
                ·
                  rfl

theorem cell19_8831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_8831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8831 prefixEnd_8831 := by exact prefixLift 8831
  have htrace : WordTrace (prefixWord ++ tailWord_8831) baseStart_8831 baseEnd_8831 := by
    simpa [prefixWord, tailWord_8831, baseEnd_8831] using wordTrace_append hprefix tailTrace_8831
  have hstable : (prefixWord ++ tailWord_8831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8831).length < 2 ^ (prefixWord ++ tailWord_8831).sum := by decide
  have hdescent : baseEnd_8831 < baseStart_8831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8846 : List Nat := [4, 1, 1, 3, 1, 1, 5, 3]
def baseStart_8846 : Nat := 118140960795 + 8846 * 2 ^ 59
def prefixEnd_8846 : Nat := 4983230072969 + 3 ^ 40 * 8846 * 2
def baseEnd_8846 : Nat := 2691703626534888109229

theorem tailTrace_8846 : CollatzResearch.WordTrace tailWord_8846 prefixEnd_8846 2691703626534888109229 := by
  unfold tailWord_8846
  simp only [CollatzResearch.WordTrace]
  refine ⟨40330015744990952703799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 215093417306618414420261 40330015744990952703799)
  ·
    refine ⟨60495023617486429055699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40330015744990952703799 60495023617486429055699)
    ·
      refine ⟨90742535426229643583549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60495023617486429055699 90742535426229643583549)
      ·
        refine ⟨34028450784836116343831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90742535426229643583549 34028450784836116343831)
        ·
          refine ⟨51042676177254174515747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34028450784836116343831 51042676177254174515747)
          ·
            refine ⟨76564014265881261773621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51042676177254174515747 76564014265881261773621)
            ·
              refine ⟨7177876337426368291277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76564014265881261773621 7177876337426368291277)
              ·
                refine ⟨2691703626534888109229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7177876337426368291277 2691703626534888109229)
                ·
                  rfl

theorem cell19_8846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_8846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8846 prefixEnd_8846 := by exact prefixLift 8846
  have htrace : WordTrace (prefixWord ++ tailWord_8846) baseStart_8846 baseEnd_8846 := by
    simpa [prefixWord, tailWord_8846, baseEnd_8846] using wordTrace_append hprefix tailTrace_8846
  have hstable : (prefixWord ++ tailWord_8846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8846).length < 2 ^ (prefixWord ++ tailWord_8846).sum := by decide
  have hdescent : baseEnd_8846 < baseStart_8846 := by decide
  rcases family_descends (prefixWord ++ tailWord_8846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8897 : List Nat := [1, 2, 6, 2, 2, 1, 2, 3]
def baseStart_8897 : Nat := 118140960795 + 8897 * 2 ^ 59
def prefixEnd_8897 : Nat := 4983230072969 + 3 ^ 40 * 8897 * 2
def baseEnd_8897 : Nat := 2707222152981880975757

theorem tailTrace_8897 : CollatzResearch.WordTrace tailWord_8897 prefixEnd_8897 2707222152981880975757 := by
  unfold tailWord_8897
  simp only [CollatzResearch.WordTrace]
  refine ⟨324500248775163331736945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 216333499183442221157963 324500248775163331736945)
  ·
    refine ⟨243375186581372498802709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 324500248775163331736945 243375186581372498802709)
    ·
      refine ⟨11408211871001835881377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 243375186581372498802709 11408211871001835881377)
      ·
        refine ⟨8556158903251376911033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11408211871001835881377 8556158903251376911033)
        ·
          refine ⟨6417119177438532683275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8556158903251376911033 6417119177438532683275)
          ·
            refine ⟨9625678766157799024913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6417119177438532683275 9625678766157799024913)
            ·
              refine ⟨7219259074618349268685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9625678766157799024913 7219259074618349268685)
              ·
                refine ⟨2707222152981880975757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7219259074618349268685 2707222152981880975757)
                ·
                  rfl

theorem cell19_8897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 3].length) (baseStart_8897 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8897 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8897 prefixEnd_8897 := by exact prefixLift 8897
  have htrace : WordTrace (prefixWord ++ tailWord_8897) baseStart_8897 baseEnd_8897 := by
    simpa [prefixWord, tailWord_8897, baseEnd_8897] using wordTrace_append hprefix tailTrace_8897
  have hstable : (prefixWord ++ tailWord_8897).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8897).length < 2 ^ (prefixWord ++ tailWord_8897).sum := by decide
  have hdescent : baseEnd_8897 < baseStart_8897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8943 : List Nat := [1, 1, 2, 1, 5, 3, 2, 4]
def baseStart_8943 : Nat := 118140960795 + 8943 * 2 ^ 59
def prefixEnd_8943 : Nat := 4983230072969 + 3 ^ 40 * 8943 * 2
def baseEnd_8943 : Nat := 2721219255267403953409

theorem tailTrace_8943 : CollatzResearch.WordTrace tailWord_8943 prefixEnd_8943 2721219255267403953409 := by
  unfold tailWord_8943
  simp only [CollatzResearch.WordTrace]
  refine ⟨326178006608513187911483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 217452004405675458607655 326178006608513187911483)
  ·
    refine ⟨489267009912769781867225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 326178006608513187911483 489267009912769781867225)
    ·
      refine ⟨366950257434577336400419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 489267009912769781867225 366950257434577336400419)
      ·
        refine ⟨550425386151866004600629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366950257434577336400419 550425386151866004600629)
        ·
          refine ⟨51602379951737437931309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 550425386151866004600629 51602379951737437931309)
          ·
            refine ⟨19350892481901539224241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51602379951737437931309 19350892481901539224241)
            ·
              refine ⟨14513169361426154418181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19350892481901539224241 14513169361426154418181)
              ·
                refine ⟨2721219255267403953409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14513169361426154418181 2721219255267403953409)
                ·
                  rfl

theorem cell19_8943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_8943 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8943 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8943 prefixEnd_8943 := by exact prefixLift 8943
  have htrace : WordTrace (prefixWord ++ tailWord_8943) baseStart_8943 baseEnd_8943 := by
    simpa [prefixWord, tailWord_8943, baseEnd_8943] using wordTrace_append hprefix tailTrace_8943
  have hstable : (prefixWord ++ tailWord_8943).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8943).length < 2 ^ (prefixWord ++ tailWord_8943).sum := by decide
  have hdescent : baseEnd_8943 < baseStart_8943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8983 : List Nat := [1, 1, 3, 4, 10]
def baseStart_8983 : Nat := 118140960795 + 8983 * 2 ^ 59
def prefixEnd_8983 : Nat := 4983230072969 + 3 ^ 40 * 8983 * 2
def baseEnd_8983 : Nat := 101236690687376409793

theorem tailTrace_8983 : CollatzResearch.WordTrace tailWord_8983 prefixEnd_8983 101236690687376409793 := by
  unfold tailWord_8983
  simp only [CollatzResearch.WordTrace]
  refine ⟨327636926463600019367603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 218424617642400012911735 327636926463600019367603)
  ·
    refine ⟨491455389695400029051405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 327636926463600019367603 491455389695400029051405)
    ·
      refine ⟨184295771135775010894277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 491455389695400029051405 184295771135775010894277)
      ·
        refine ⟨34555457087957814542677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184295771135775010894277 34555457087957814542677)
        ·
          refine ⟨101236690687376409793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 34555457087957814542677 101236690687376409793)
          ·
            rfl

theorem cell19_8983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 10].length) (baseStart_8983 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8983 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8983 prefixEnd_8983 := by exact prefixLift 8983
  have htrace : WordTrace (prefixWord ++ tailWord_8983) baseStart_8983 baseEnd_8983 := by
    simpa [prefixWord, tailWord_8983, baseEnd_8983] using wordTrace_append hprefix tailTrace_8983
  have hstable : (prefixWord ++ tailWord_8983).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8983).length < 2 ^ (prefixWord ++ tailWord_8983).sum := by decide
  have hdescent : baseEnd_8983 < baseStart_8983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8996 : List Nat := [2, 3, 1, 3, 4, 1, 1, 4]
def baseStart_8996 : Nat := 118140960795 + 8996 * 2 ^ 59
def prefixEnd_8996 : Nat := 4983230072969 + 3 ^ 40 * 8996 * 2
def baseEnd_8996 : Nat := 2737346351378984775487

theorem tailTrace_8996 : CollatzResearch.WordTrace tailWord_8996 prefixEnd_8996 2737346351378984775487 := by
  unfold tailWord_8996
  simp only [CollatzResearch.WordTrace]
  refine ⟨164055537708251619795421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 218740716944335493060561 164055537708251619795421)
  ·
    refine ⟨61520826640594357423283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164055537708251619795421 61520826640594357423283)
    ·
      refine ⟨92281239960891536134925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61520826640594357423283 92281239960891536134925)
      ·
        refine ⟨34605464985334326050597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92281239960891536134925 34605464985334326050597)
        ·
          refine ⟨6488524684750186134487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34605464985334326050597 6488524684750186134487)
          ·
            refine ⟨9732787027125279201731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6488524684750186134487 9732787027125279201731)
            ·
              refine ⟨14599180540687918802597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9732787027125279201731 14599180540687918802597)
              ·
                refine ⟨2737346351378984775487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14599180540687918802597 2737346351378984775487)
                ·
                  rfl

theorem cell19_8996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_8996 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_8996 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_8996 prefixEnd_8996 := by exact prefixLift 8996
  have htrace : WordTrace (prefixWord ++ tailWord_8996) baseStart_8996 baseEnd_8996 := by
    simpa [prefixWord, tailWord_8996, baseEnd_8996] using wordTrace_append hprefix tailTrace_8996
  have hstable : (prefixWord ++ tailWord_8996).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8996).length < 2 ^ (prefixWord ++ tailWord_8996).sum := by decide
  have hdescent : baseEnd_8996 < baseStart_8996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9070 : List Nat := [4, 1, 2, 3, 3, 1, 2, 3]
def baseStart_9070 : Nat := 118140960795 + 9070 * 2 ^ 59
def prefixEnd_9070 : Nat := 4983230072969 + 3 ^ 40 * 9070 * 2
def baseEnd_9070 : Nat := 2759863428968739130841

theorem tailTrace_9070 : CollatzResearch.WordTrace tailWord_9070 prefixEnd_9070 2759863428968739130841 := by
  unfold tailWord_9070
  simp only [CollatzResearch.WordTrace]
  refine ⟨41351259643551734723083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 220540051432275918523109 41351259643551734723083)
  ·
    refine ⟨62026889465327602084625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41351259643551734723083 62026889465327602084625)
    ·
      refine ⟨46520167098995701563469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62026889465327602084625 46520167098995701563469)
      ·
        refine ⟨17445062662123388086301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46520167098995701563469 17445062662123388086301)
        ·
          refine ⟨6541898498296270532363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17445062662123388086301 6541898498296270532363)
          ·
            refine ⟨9812847747444405798545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6541898498296270532363 9812847747444405798545)
            ·
              refine ⟨7359635810583304348909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9812847747444405798545 7359635810583304348909)
              ·
                refine ⟨2759863428968739130841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7359635810583304348909 2759863428968739130841)
                ·
                  rfl

theorem cell19_9070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_9070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9070 prefixEnd_9070 := by exact prefixLift 9070
  have htrace : WordTrace (prefixWord ++ tailWord_9070) baseStart_9070 baseEnd_9070 := by
    simpa [prefixWord, tailWord_9070, baseEnd_9070] using wordTrace_append hprefix tailTrace_9070
  have hstable : (prefixWord ++ tailWord_9070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9070).length < 2 ^ (prefixWord ++ tailWord_9070).sum := by decide
  have hdescent : baseEnd_9070 < baseStart_9070 := by decide
  rcases family_descends (prefixWord ++ tailWord_9070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9095 : List Nat := [1, 1, 4, 2, 3, 3, 5]
def baseStart_9095 : Nat := 118140960795 + 9095 * 2 ^ 59
def prefixEnd_9095 : Nat := 4983230072969 + 3 ^ 40 * 9095 * 2
def baseEnd_9095 : Nat := 922490183258696191739

theorem tailTrace_9095 : CollatzResearch.WordTrace tailWord_9095 prefixEnd_9095 922490183258696191739 := by
  unfold tailWord_9095
  simp only [CollatzResearch.WordTrace]
  refine ⟨331721902057843147444739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 221147934705228764963159 331721902057843147444739)
  ·
    refine ⟨497582853086764721167109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 331721902057843147444739 497582853086764721167109)
    ·
      refine ⟨93296784953768385218833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 497582853086764721167109 93296784953768385218833)
      ·
        refine ⟨69972588715326288914125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93296784953768385218833 69972588715326288914125)
        ·
          refine ⟨26239720768247358342797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69972588715326288914125 26239720768247358342797)
          ·
            refine ⟨9839895288092759378549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26239720768247358342797 9839895288092759378549)
            ·
              refine ⟨922490183258696191739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9839895288092759378549 922490183258696191739)
              ·
                rfl

theorem cell19_9095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 5].length) (baseStart_9095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9095 prefixEnd_9095 := by exact prefixLift 9095
  have htrace : WordTrace (prefixWord ++ tailWord_9095) baseStart_9095 baseEnd_9095 := by
    simpa [prefixWord, tailWord_9095, baseEnd_9095] using wordTrace_append hprefix tailTrace_9095
  have hstable : (prefixWord ++ tailWord_9095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9095).length < 2 ^ (prefixWord ++ tailWord_9095).sum := by decide
  have hdescent : baseEnd_9095 < baseStart_9095 := by decide
  rcases family_descends (prefixWord ++ tailWord_9095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9097 : List Nat := [1, 2, 1, 1, 5, 2, 7]
def baseStart_9097 : Nat := 118140960795 + 9097 * 2 ^ 59
def prefixEnd_9097 : Nat := 4983230072969 + 3 ^ 40 * 9097 * 2
def baseEnd_9097 : Nat := 922693039813558843589

theorem tailTrace_9097 : CollatzResearch.WordTrace tailWord_9097 prefixEnd_9097 922693039813558843589 := by
  unfold tailWord_9097
  simp only [CollatzResearch.WordTrace]
  refine ⟨331794848050597489017545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 221196565367064992678363 331794848050597489017545)
  ·
    refine ⟨248846136037948116763159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 331794848050597489017545 248846136037948116763159)
    ·
      refine ⟨373269204056922175144739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248846136037948116763159 373269204056922175144739)
      ·
        refine ⟨559903806085383262717109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373269204056922175144739 559903806085383262717109)
        ·
          refine ⟨52490981820504680879729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 559903806085383262717109 52490981820504680879729)
          ·
            refine ⟨39368236365378510659797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52490981820504680879729 39368236365378510659797)
            ·
              refine ⟨922693039813558843589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 39368236365378510659797 922693039813558843589)
              ·
                rfl

theorem cell19_9097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_9097 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9097 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9097 prefixEnd_9097 := by exact prefixLift 9097
  have htrace : WordTrace (prefixWord ++ tailWord_9097) baseStart_9097 baseEnd_9097 := by
    simpa [prefixWord, tailWord_9097, baseEnd_9097] using wordTrace_append hprefix tailTrace_9097
  have hstable : (prefixWord ++ tailWord_9097).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9097).length < 2 ^ (prefixWord ++ tailWord_9097).sum := by decide
  have hdescent : baseEnd_9097 < baseStart_9097 := by decide
  rcases family_descends (prefixWord ++ tailWord_9097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9110 : List Nat := [5, 3, 1, 1, 1, 1, 1, 6]
def baseStart_9110 : Nat := 118140960795 + 9110 * 2 ^ 59
def prefixEnd_9110 : Nat := 4983230072969 + 3 ^ 40 * 9110 * 2
def baseEnd_9110 : Nat := 2772034822260498241843

theorem tailTrace_9110 : CollatzResearch.WordTrace tailWord_9110 prefixEnd_9110 2772034822260498241843 := by
  unfold tailWord_9110
  simp only [CollatzResearch.WordTrace]
  refine ⟨20766812312718794327549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 221512664669000472827189 20766812312718794327549)
  ·
    refine ⟨7787554617269547872831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20766812312718794327549 7787554617269547872831)
    ·
      refine ⟨11681331925904321809247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7787554617269547872831 11681331925904321809247)
      ·
        refine ⟨17521997888856482713871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11681331925904321809247 17521997888856482713871)
        ·
          refine ⟨26282996833284724070807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17521997888856482713871 26282996833284724070807)
          ·
            refine ⟨39424495249927086106211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26282996833284724070807 39424495249927086106211)
            ·
              refine ⟨59136742874890629159317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39424495249927086106211 59136742874890629159317)
              ·
                refine ⟨2772034822260498241843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59136742874890629159317 2772034822260498241843)
                ·
                  rfl

theorem cell19_9110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_9110 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9110 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9110 prefixEnd_9110 := by exact prefixLift 9110
  have htrace : WordTrace (prefixWord ++ tailWord_9110) baseStart_9110 baseEnd_9110 := by
    simpa [prefixWord, tailWord_9110, baseEnd_9110] using wordTrace_append hprefix tailTrace_9110
  have hstable : (prefixWord ++ tailWord_9110).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9110).length < 2 ^ (prefixWord ++ tailWord_9110).sum := by decide
  have hdescent : baseEnd_9110 < baseStart_9110 := by decide
  rcases family_descends (prefixWord ++ tailWord_9110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9186 : List Nat := [3, 3, 3, 1, 1, 2, 3, 3]
def baseStart_9186 : Nat := 118140960795 + 9186 * 2 ^ 59
def prefixEnd_9186 : Nat := 4983230072969 + 3 ^ 40 * 9186 * 2
def baseEnd_9186 : Nat := 2795160469514840552747

theorem tailTrace_9186 : CollatzResearch.WordTrace tailWord_9186 prefixEnd_9186 2795160469514840552747 := by
  unfold tailWord_9186
  simp only [CollatzResearch.WordTrace]
  refine ⟨83760236182041422251853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 223360629818777126004941 83760236182041422251853)
  ·
    refine ⟨31410088568265533344445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83760236182041422251853 31410088568265533344445)
    ·
      refine ⟨11778783213099575004167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31410088568265533344445 11778783213099575004167)
      ·
        refine ⟨17668174819649362506251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11778783213099575004167 17668174819649362506251)
        ·
          refine ⟨26502262229474043759377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17668174819649362506251 26502262229474043759377)
          ·
            refine ⟨19876696672105532819533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26502262229474043759377 19876696672105532819533)
            ·
              refine ⟨7453761252039574807325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19876696672105532819533 7453761252039574807325)
              ·
                refine ⟨2795160469514840552747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7453761252039574807325 2795160469514840552747)
                ·
                  rfl

theorem cell19_9186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_9186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9186 prefixEnd_9186 := by exact prefixLift 9186
  have htrace : WordTrace (prefixWord ++ tailWord_9186) baseStart_9186 baseEnd_9186 := by
    simpa [prefixWord, tailWord_9186, baseEnd_9186] using wordTrace_append hprefix tailTrace_9186
  have hstable : (prefixWord ++ tailWord_9186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9186).length < 2 ^ (prefixWord ++ tailWord_9186).sum := by decide
  have hdescent : baseEnd_9186 < baseStart_9186 := by decide
  rcases family_descends (prefixWord ++ tailWord_9186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9192 : List Nat := [2, 1, 4, 1, 1, 1, 2, 7]
def baseStart_9192 : Nat := 118140960795 + 9192 * 2 ^ 59
def prefixEnd_9192 : Nat := 4983230072969 + 3 ^ 40 * 9192 * 2
def baseEnd_9192 : Nat := 2796986178508604419397

theorem tailTrace_9192 : CollatzResearch.WordTrace tailWord_9192 prefixEnd_9192 2796986178508604419397 := by
  unfold tailWord_9192
  simp only [CollatzResearch.WordTrace]
  refine ⟨167629891353214356862915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 223506521804285809150553 167629891353214356862915)
  ·
    refine ⟨251444837029821535294373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167629891353214356862915 251444837029821535294373)
    ·
      refine ⟨47145906943091537867695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251444837029821535294373 47145906943091537867695)
      ·
        refine ⟨70718860414637306801543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47145906943091537867695 70718860414637306801543)
        ·
          refine ⟨106078290621955960202315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70718860414637306801543 106078290621955960202315)
          ·
            refine ⟨159117435932933940303473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106078290621955960202315 159117435932933940303473)
            ·
              refine ⟨119338076949700455227605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159117435932933940303473 119338076949700455227605)
              ·
                refine ⟨2796986178508604419397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 119338076949700455227605 2796986178508604419397)
                ·
                  rfl

theorem cell19_9192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_9192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9192 prefixEnd_9192 := by exact prefixLift 9192
  have htrace : WordTrace (prefixWord ++ tailWord_9192) baseStart_9192 baseEnd_9192 := by
    simpa [prefixWord, tailWord_9192, baseEnd_9192] using wordTrace_append hprefix tailTrace_9192
  have hstable : (prefixWord ++ tailWord_9192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9192).length < 2 ^ (prefixWord ++ tailWord_9192).sum := by decide
  have hdescent : baseEnd_9192 < baseStart_9192 := by decide
  rcases family_descends (prefixWord ++ tailWord_9192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9247 : List Nat := [1, 1, 2, 4, 1, 3, 4, 3]
def baseStart_9247 : Nat := 118140960795 + 9247 * 2 ^ 59
def prefixEnd_9247 : Nat := 4983230072969 + 3 ^ 40 * 9247 * 2
def baseEnd_9247 : Nat := 2813721844284773197025

theorem tailTrace_9247 : CollatzResearch.WordTrace tailWord_9247 prefixEnd_9247 2813721844284773197025 := by
  unfold tailWord_9247
  simp only [CollatzResearch.WordTrace]
  refine ⟨337265797507173106977995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 224843865004782071318663 337265797507173106977995)
  ·
    refine ⟨505898696260759660466993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 337265797507173106977995 505898696260759660466993)
    ·
      refine ⟨379424022195569745350245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 505898696260759660466993 379424022195569745350245)
      ·
        refine ⟨71142004161669327253171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 379424022195569745350245 71142004161669327253171)
        ·
          refine ⟨106713006242503990879757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71142004161669327253171 106713006242503990879757)
          ·
            refine ⟨40017377340938996579909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106713006242503990879757 40017377340938996579909)
            ·
              refine ⟨7503258251426061858733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40017377340938996579909 7503258251426061858733)
              ·
                refine ⟨2813721844284773197025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7503258251426061858733 2813721844284773197025)
                ·
                  rfl

theorem cell19_9247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 3].length) (baseStart_9247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9247 prefixEnd_9247 := by exact prefixLift 9247
  have htrace : WordTrace (prefixWord ++ tailWord_9247) baseStart_9247 baseEnd_9247 := by
    simpa [prefixWord, tailWord_9247, baseEnd_9247] using wordTrace_append hprefix tailTrace_9247
  have hstable : (prefixWord ++ tailWord_9247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9247).length < 2 ^ (prefixWord ++ tailWord_9247).sum := by decide
  have hdescent : baseEnd_9247 < baseStart_9247 := by decide
  rcases family_descends (prefixWord ++ tailWord_9247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9287 : List Nat := [1, 1, 4, 1, 3, 2, 1, 6]
def baseStart_9287 : Nat := 118140960795 + 9287 * 2 ^ 59
def prefixEnd_9287 : Nat := 4983230072969 + 3 ^ 40 * 9287 * 2
def baseEnd_9287 : Nat := 2825893237576532308027

theorem tailTrace_9287 : CollatzResearch.WordTrace tailWord_9287 prefixEnd_9287 2825893237576532308027 := by
  unfold tailWord_9287
  simp only [CollatzResearch.WordTrace]
  refine ⟨338724717362259938434115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 225816478241506625622743 338724717362259938434115)
  ·
    refine ⟨508087076043389907651173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 338724717362259938434115 508087076043389907651173)
    ·
      refine ⟨95266326758135607684595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 508087076043389907651173 95266326758135607684595)
      ·
        refine ⟨142899490137203411526893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95266326758135607684595 142899490137203411526893)
        ·
          refine ⟨53587308801451279322585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142899490137203411526893 53587308801451279322585)
          ·
            refine ⟨40190481601088459491939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53587308801451279322585 40190481601088459491939)
            ·
              refine ⟨60285722401632689237909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40190481601088459491939 60285722401632689237909)
              ·
                refine ⟨2825893237576532308027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60285722401632689237909 2825893237576532308027)
                ·
                  rfl

theorem cell19_9287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_9287 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9287 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9287 prefixEnd_9287 := by exact prefixLift 9287
  have htrace : WordTrace (prefixWord ++ tailWord_9287) baseStart_9287 baseEnd_9287 := by
    simpa [prefixWord, tailWord_9287, baseEnd_9287] using wordTrace_append hprefix tailTrace_9287
  have hstable : (prefixWord ++ tailWord_9287).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9287).length < 2 ^ (prefixWord ++ tailWord_9287).sum := by decide
  have hdescent : baseEnd_9287 < baseStart_9287 := by decide
  rcases family_descends (prefixWord ++ tailWord_9287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9325 : List Nat := [1, 5, 1, 1, 2, 9]
def baseStart_9325 : Nat := 118140960795 + 9325 * 2 ^ 59
def prefixEnd_9325 : Nat := 4983230072969 + 3 ^ 40 * 9325 * 2
def baseEnd_9325 : Nat := 315272895689300384831

theorem tailTrace_9325 : CollatzResearch.WordTrace tailWord_9325 prefixEnd_9325 315272895689300384831 := by
  unfold tailWord_9325
  simp only [CollatzResearch.WordTrace]
  refine ⟨340110691224592428317429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 226740460816394952211619 340110691224592428317429)
  ·
    refine ⟨31885377302305540154759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 340110691224592428317429 31885377302305540154759)
    ·
      refine ⟨47828065953458310232139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31885377302305540154759 47828065953458310232139)
      ·
        refine ⟨71742098930187465348209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47828065953458310232139 71742098930187465348209)
        ·
          refine ⟨53806574197640599011157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71742098930187465348209 53806574197640599011157)
          ·
            refine ⟨315272895689300384831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 53806574197640599011157 315272895689300384831)
            ·
              rfl

theorem cell19_9325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 9].length) (baseStart_9325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9325 prefixEnd_9325 := by exact prefixLift 9325
  have htrace : WordTrace (prefixWord ++ tailWord_9325) baseStart_9325 baseEnd_9325 := by
    simpa [prefixWord, tailWord_9325, baseEnd_9325] using wordTrace_append hprefix tailTrace_9325
  have hstable : (prefixWord ++ tailWord_9325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9325).length < 2 ^ (prefixWord ++ tailWord_9325).sum := by decide
  have hdescent : baseEnd_9325 < baseStart_9325 := by decide
  rcases family_descends (prefixWord ++ tailWord_9325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9344 : List Nat := [2, 1, 1, 2, 1, 3, 5, 4]
def baseStart_9344 : Nat := 118140960795 + 9344 * 2 ^ 59
def prefixEnd_9344 : Nat := 4983230072969 + 3 ^ 40 * 9344 * 2
def baseEnd_9344 : Nat := 2843237473017289041205

theorem tailTrace_9344 : CollatzResearch.WordTrace tailWord_9344 prefixEnd_9344 2843237473017289041205 := by
  unfold tailWord_9344
  simp only [CollatzResearch.WordTrace]
  refine ⟨170401839077879336629543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 227202452103839115506057 170401839077879336629543)
  ·
    refine ⟨255602758616819004944315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170401839077879336629543 255602758616819004944315)
    ·
      refine ⟨383404137925228507416473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255602758616819004944315 383404137925228507416473)
      ·
        refine ⟨287553103443921380562355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383404137925228507416473 287553103443921380562355)
        ·
          refine ⟨431329655165882070843533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287553103443921380562355 431329655165882070843533)
          ·
            refine ⟨161748620687205776566325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 431329655165882070843533 161748620687205776566325)
            ·
              refine ⟨15163933189425541553093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 161748620687205776566325 15163933189425541553093)
              ·
                refine ⟨2843237473017289041205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15163933189425541553093 2843237473017289041205)
                ·
                  rfl

theorem cell19_9344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_9344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9344 prefixEnd_9344 := by exact prefixLift 9344
  have htrace : WordTrace (prefixWord ++ tailWord_9344) baseStart_9344 baseEnd_9344 := by
    simpa [prefixWord, tailWord_9344, baseEnd_9344] using wordTrace_append hprefix tailTrace_9344
  have hstable : (prefixWord ++ tailWord_9344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9344).length < 2 ^ (prefixWord ++ tailWord_9344).sum := by decide
  have hdescent : baseEnd_9344 < baseStart_9344 := by decide
  rcases family_descends (prefixWord ++ tailWord_9344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9410 : List Nat := [3, 5, 1, 1, 3, 1, 2, 3]
def baseStart_9410 : Nat := 118140960795 + 9410 * 2 ^ 59
def prefixEnd_9410 : Nat := 4983230072969 + 3 ^ 40 * 9410 * 2
def baseEnd_9410 : Nat := 2863320271948691574359

theorem tailTrace_9410 : CollatzResearch.WordTrace tailWord_9410 prefixEnd_9410 2863320271948691574359 := by
  unfold tailWord_9410
  simp only [CollatzResearch.WordTrace]
  refine ⟨85802723979162986290421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 228807263944434630107789 85802723979162986290421)
  ·
    refine ⟨8044005373046529964727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85802723979162986290421 8044005373046529964727)
    ·
      refine ⟨12066008059569794947091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8044005373046529964727 12066008059569794947091)
      ·
        refine ⟨18099012089354692420637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12066008059569794947091 18099012089354692420637)
        ·
          refine ⟨6787129533508009657739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18099012089354692420637 6787129533508009657739)
          ·
            refine ⟨10180694300262014486609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6787129533508009657739 10180694300262014486609)
            ·
              refine ⟨7635520725196510864957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10180694300262014486609 7635520725196510864957)
              ·
                refine ⟨2863320271948691574359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7635520725196510864957 2863320271948691574359)
                ·
                  rfl

theorem cell19_9410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_9410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9410 prefixEnd_9410 := by exact prefixLift 9410
  have htrace : WordTrace (prefixWord ++ tailWord_9410) baseStart_9410 baseEnd_9410 := by
    simpa [prefixWord, tailWord_9410, baseEnd_9410] using wordTrace_append hprefix tailTrace_9410
  have hstable : (prefixWord ++ tailWord_9410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9410).length < 2 ^ (prefixWord ++ tailWord_9410).sum := by decide
  have hdescent : baseEnd_9410 < baseStart_9410 := by decide
  rcases family_descends (prefixWord ++ tailWord_9410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9418 : List Nat := [3, 1, 2, 1, 3, 2, 4, 3]
def baseStart_9418 : Nat := 118140960795 + 9418 * 2 ^ 59
def prefixEnd_9418 : Nat := 4983230072969 + 3 ^ 40 * 9418 * 2
def baseEnd_9418 : Nat := 2865754550607043396559

theorem tailTrace_9418 : CollatzResearch.WordTrace tailWord_9418 prefixEnd_9418 2865754550607043396559 := by
  unfold tailWord_9418
  simp only [CollatzResearch.WordTrace]
  refine ⟨85875669971917327863227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 229001786591779540968605 85875669971917327863227)
  ·
    refine ⟨128813504957875991794841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85875669971917327863227 128813504957875991794841)
    ·
      refine ⟨96610128718406993846131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128813504957875991794841 96610128718406993846131)
      ·
        refine ⟨144915193077610490769197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96610128718406993846131 144915193077610490769197)
        ·
          refine ⟨54343197404103934038449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144915193077610490769197 54343197404103934038449)
          ·
            refine ⟨40757398053077950528837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54343197404103934038449 40757398053077950528837)
            ·
              refine ⟨7642012134952115724157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40757398053077950528837 7642012134952115724157)
              ·
                refine ⟨2865754550607043396559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7642012134952115724157 2865754550607043396559)
                ·
                  rfl

theorem cell19_9418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_9418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9418 prefixEnd_9418 := by exact prefixLift 9418
  have htrace : WordTrace (prefixWord ++ tailWord_9418) baseStart_9418 baseEnd_9418 := by
    simpa [prefixWord, tailWord_9418, baseEnd_9418] using wordTrace_append hprefix tailTrace_9418
  have hstable : (prefixWord ++ tailWord_9418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9418).length < 2 ^ (prefixWord ++ tailWord_9418).sum := by decide
  have hdescent : baseEnd_9418 < baseStart_9418 := by decide
  rcases family_descends (prefixWord ++ tailWord_9418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9532 : List Nat := [2, 2, 2, 2, 1, 4, 3, 3]
def baseStart_9532 : Nat := 118140960795 + 9532 * 2 ^ 59
def prefixEnd_9532 : Nat := 4983230072969 + 3 ^ 40 * 9532 * 2
def baseEnd_9532 : Nat := 2900443021488556862915

theorem tailTrace_9532 : CollatzResearch.WordTrace tailWord_9532 prefixEnd_9532 2900443021488556862915 := by
  unfold tailWord_9532
  simp only [CollatzResearch.WordTrace]
  refine ⟨173830300737333390551425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 231773734316444520735233 173830300737333390551425)
  ·
    refine ⟨130372725553000042913569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173830300737333390551425 130372725553000042913569)
    ·
      refine ⟨97779544164750032185177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130372725553000042913569 97779544164750032185177)
      ·
        refine ⟨73334658123562524138883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97779544164750032185177 73334658123562524138883)
        ·
          refine ⟨110001987185343786208325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73334658123562524138883 110001987185343786208325)
          ·
            refine ⟨20625372597251959914061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110001987185343786208325 20625372597251959914061)
            ·
              refine ⟨7734514723969484967773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20625372597251959914061 7734514723969484967773)
              ·
                refine ⟨2900443021488556862915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7734514723969484967773 2900443021488556862915)
                ·
                  rfl

theorem cell19_9532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_9532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9532 prefixEnd_9532 := by exact prefixLift 9532
  have htrace : WordTrace (prefixWord ++ tailWord_9532) baseStart_9532 baseEnd_9532 := by
    simpa [prefixWord, tailWord_9532, baseEnd_9532] using wordTrace_append hprefix tailTrace_9532
  have hstable : (prefixWord ++ tailWord_9532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9532).length < 2 ^ (prefixWord ++ tailWord_9532).sum := by decide
  have hdescent : baseEnd_9532 < baseStart_9532 := by decide
  rcases family_descends (prefixWord ++ tailWord_9532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9549 : List Nat := [1, 6, 1, 3, 1, 1, 6]
def baseStart_9549 : Nat := 118140960795 + 9549 * 2 ^ 59
def prefixEnd_9549 : Nat := 4983230072969 + 3 ^ 40 * 9549 * 2
def baseEnd_9549 : Nat := 968538621212518161697

theorem tailTrace_9549 : CollatzResearch.WordTrace tailWord_9549 prefixEnd_9549 968538621212518161697 := by
  unfold tailWord_9549
  simp only [CollatzResearch.WordTrace]
  refine ⟨348280642413078684471701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 232187094942052456314467 348280642413078684471701)
  ·
    refine ⟨16325655113113063334611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 348280642413078684471701 16325655113113063334611)
    ·
      refine ⟨24488482669669595001917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16325655113113063334611 24488482669669595001917)
      ·
        refine ⟨9183181001126098125719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24488482669669595001917 9183181001126098125719)
        ·
          refine ⟨13774771501689147188579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9183181001126098125719 13774771501689147188579)
          ·
            refine ⟨20662157252533720782869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13774771501689147188579 20662157252533720782869)
            ·
              refine ⟨968538621212518161697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20662157252533720782869 968538621212518161697)
              ·
                rfl

theorem cell19_9549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 6].length) (baseStart_9549 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9549 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9549 prefixEnd_9549 := by exact prefixLift 9549
  have htrace : WordTrace (prefixWord ++ tailWord_9549) baseStart_9549 baseEnd_9549 := by
    simpa [prefixWord, tailWord_9549, baseEnd_9549] using wordTrace_append hprefix tailTrace_9549
  have hstable : (prefixWord ++ tailWord_9549).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9549).length < 2 ^ (prefixWord ++ tailWord_9549).sum := by decide
  have hdescent : baseEnd_9549 < baseStart_9549 := by decide
  rcases family_descends (prefixWord ++ tailWord_9549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9555 : List Nat := [1, 1, 1, 2, 1, 1, 12]
def baseStart_9555 : Nat := 118140960795 + 9555 * 2 ^ 59
def prefixEnd_9555 : Nat := 4983230072969 + 3 ^ 40 * 9555 * 2
def baseEnd_9555 : Nat := 969147190877106117247

theorem tailTrace_9555 : CollatzResearch.WordTrace tailWord_9555 prefixEnd_9555 969147190877106117247 := by
  unfold tailWord_9555
  simp only [CollatzResearch.WordTrace]
  refine ⟨348499480391341709190119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 232332986927561139460079 348499480391341709190119)
  ·
    refine ⟨522749220587012563785179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 348499480391341709190119 522749220587012563785179)
    ·
      refine ⟨784123830880518845677769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 522749220587012563785179 784123830880518845677769)
      ·
        refine ⟨588092873160389134258327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 784123830880518845677769 588092873160389134258327)
        ·
          refine ⟨882139309740583701387491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 588092873160389134258327 882139309740583701387491)
          ·
            refine ⟨1323208964610875552081237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882139309740583701387491 1323208964610875552081237)
            ·
              refine ⟨969147190877106117247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 1323208964610875552081237 969147190877106117247)
              ·
                rfl

theorem cell19_9555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_9555 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9555 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9555 prefixEnd_9555 := by exact prefixLift 9555
  have htrace : WordTrace (prefixWord ++ tailWord_9555) baseStart_9555 baseEnd_9555 := by
    simpa [prefixWord, tailWord_9555, baseEnd_9555] using wordTrace_append hprefix tailTrace_9555
  have hstable : (prefixWord ++ tailWord_9555).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9555).length < 2 ^ (prefixWord ++ tailWord_9555).sum := by decide
  have hdescent : baseEnd_9555 < baseStart_9555 := by decide
  rcases family_descends (prefixWord ++ tailWord_9555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9589 : List Nat := [1, 3, 4, 1, 3, 1, 1, 5]
def baseStart_9589 : Nat := 118140960795 + 9589 * 2 ^ 59
def prefixEnd_9589 : Nat := 4983230072969 + 3 ^ 40 * 9589 * 2
def baseEnd_9589 : Nat := 2917787256929313596093

theorem tailTrace_9589 : CollatzResearch.WordTrace tailWord_9589 prefixEnd_9589 2917787256929313596093 := by
  unfold tailWord_9589
  simp only [CollatzResearch.WordTrace]
  refine ⟨349739562268165515927821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 233159708178777010618547 349739562268165515927821)
  ·
    refine ⟨131152335850562068472933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 349739562268165515927821 131152335850562068472933)
    ·
      refine ⟨24591062971980387838675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131152335850562068472933 24591062971980387838675)
      ·
        refine ⟨36886594457970581758013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24591062971980387838675 36886594457970581758013)
        ·
          refine ⟨13832472921738968159255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36886594457970581758013 13832472921738968159255)
          ·
            refine ⟨20748709382608452238883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13832472921738968159255 20748709382608452238883)
            ·
              refine ⟨31123064073912678358325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20748709382608452238883 31123064073912678358325)
              ·
                refine ⟨2917787256929313596093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31123064073912678358325 2917787256929313596093)
                ·
                  rfl

theorem cell19_9589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_9589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9589 prefixEnd_9589 := by exact prefixLift 9589
  have htrace : WordTrace (prefixWord ++ tailWord_9589) baseStart_9589 baseEnd_9589 := by
    simpa [prefixWord, tailWord_9589, baseEnd_9589] using wordTrace_append hprefix tailTrace_9589
  have hstable : (prefixWord ++ tailWord_9589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9589).length < 2 ^ (prefixWord ++ tailWord_9589).sum := by decide
  have hdescent : baseEnd_9589 < baseStart_9589 := by decide
  rcases family_descends (prefixWord ++ tailWord_9589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
