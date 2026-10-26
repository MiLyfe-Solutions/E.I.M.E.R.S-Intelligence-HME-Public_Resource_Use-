import FamilyDescent
import OrdinaryBridge

open CollatzResearch

namespace V185TrunkScan12

def prefixWord : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1]

theorem prefixTrace : CollatzResearch.WordTrace prefixWord 118140960795 4983230072969 := by
  unfold prefixWord
  simp only [CollatzResearch.WordTrace]
  refine ⟨177211441193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118140960795 177211441193)
  ·
    refine ⟨132908580895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177211441193 132908580895)
    ·
      refine ⟨199362871343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132908580895 199362871343)
      ·
        refine ⟨299044307015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199362871343 299044307015)
        ·
          refine ⟨448566460523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299044307015 448566460523)
          ·
            refine ⟨672849690785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448566460523 672849690785)
            ·
              refine ⟨504637268089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 672849690785 504637268089)
              ·
                refine ⟨378477951067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504637268089 378477951067)
                ·
                  refine ⟨567716926601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378477951067 567716926601)
                  ·
                    refine ⟨425787694951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 567716926601 425787694951)
                    ·
                      refine ⟨638681542427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 1 425787694951 638681542427)
                      ·
                        refine ⟨958022313641, ?_, ?_⟩
                        · exact (by decide : CollatzResearch.ExactOddStep 1 638681542427 958022313641)
                        ·
                          refine ⟨718516735231, ?_, ?_⟩
                          · exact (by decide : CollatzResearch.ExactOddStep 2 958022313641 718516735231)
                          ·
                            refine ⟨1077775102847, ?_, ?_⟩
                            · exact (by decide : CollatzResearch.ExactOddStep 1 718516735231 1077775102847)
                            ·
                              refine ⟨1616662654271, ?_, ?_⟩
                              · exact (by decide : CollatzResearch.ExactOddStep 1 1077775102847 1616662654271)
                              ·
                                refine ⟨2424993981407, ?_, ?_⟩
                                · exact (by decide : CollatzResearch.ExactOddStep 1 1616662654271 2424993981407)
                                ·
                                  refine ⟨3637490972111, ?_, ?_⟩
                                  · exact (by decide : CollatzResearch.ExactOddStep 1 2424993981407 3637490972111)
                                  ·
                                    refine ⟨5456236458167, ?_, ?_⟩
                                    · exact (by decide : CollatzResearch.ExactOddStep 1 3637490972111 5456236458167)
                                    ·
                                      refine ⟨8184354687251, ?_, ?_⟩
                                      · exact (by decide : CollatzResearch.ExactOddStep 1 5456236458167 8184354687251)
                                      ·
                                        refine ⟨12276532030877, ?_, ?_⟩
                                        · exact (by decide : CollatzResearch.ExactOddStep 1 8184354687251 12276532030877)
                                        ·
                                          refine ⟨4603699511579, ?_, ?_⟩
                                          · exact (by decide : CollatzResearch.ExactOddStep 3 12276532030877 4603699511579)
                                          ·
                                            refine ⟨6905549267369, ?_, ?_⟩
                                            · exact (by decide : CollatzResearch.ExactOddStep 1 4603699511579 6905549267369)
                                            ·
                                              refine ⟨5179161950527, ?_, ?_⟩
                                              · exact (by decide : CollatzResearch.ExactOddStep 2 6905549267369 5179161950527)
                                              ·
                                                refine ⟨7768742925791, ?_, ?_⟩
                                                · exact (by decide : CollatzResearch.ExactOddStep 1 5179161950527 7768742925791)
                                                ·
                                                  refine ⟨11653114388687, ?_, ?_⟩
                                                  · exact (by decide : CollatzResearch.ExactOddStep 1 7768742925791 11653114388687)
                                                  ·
                                                    refine ⟨17479671583031, ?_, ?_⟩
                                                    · exact (by decide : CollatzResearch.ExactOddStep 1 11653114388687 17479671583031)
                                                    ·
                                                      refine ⟨26219507374547, ?_, ?_⟩
                                                      · exact (by decide : CollatzResearch.ExactOddStep 1 17479671583031 26219507374547)
                                                      ·
                                                        refine ⟨39329261061821, ?_, ?_⟩
                                                        · exact (by decide : CollatzResearch.ExactOddStep 1 26219507374547 39329261061821)
                                                        ·
                                                          refine ⟨14748472898183, ?_, ?_⟩
                                                          · exact (by decide : CollatzResearch.ExactOddStep 3 39329261061821 14748472898183)
                                                          ·
                                                            refine ⟨22122709347275, ?_, ?_⟩
                                                            · exact (by decide : CollatzResearch.ExactOddStep 1 14748472898183 22122709347275)
                                                            ·
                                                              refine ⟨33184064020913, ?_, ?_⟩
                                                              · exact (by decide : CollatzResearch.ExactOddStep 1 22122709347275 33184064020913)
                                                              ·
                                                                refine ⟨24888048015685, ?_, ?_⟩
                                                                · exact (by decide : CollatzResearch.ExactOddStep 2 33184064020913 24888048015685)
                                                                ·
                                                                  refine ⟨4666509002941, ?_, ?_⟩
                                                                  · exact (by decide : CollatzResearch.ExactOddStep 4 24888048015685 4666509002941)
                                                                  ·
                                                                    refine ⟨1749940876103, ?_, ?_⟩
                                                                    · exact (by decide : CollatzResearch.ExactOddStep 3 4666509002941 1749940876103)
                                                                    ·
                                                                      refine ⟨2624911314155, ?_, ?_⟩
                                                                      · exact (by decide : CollatzResearch.ExactOddStep 1 1749940876103 2624911314155)
                                                                      ·
                                                                        refine ⟨3937366971233, ?_, ?_⟩
                                                                        · exact (by decide : CollatzResearch.ExactOddStep 1 2624911314155 3937366971233)
                                                                        ·
                                                                          refine ⟨2953025228425, ?_, ?_⟩
                                                                          · exact (by decide : CollatzResearch.ExactOddStep 2 3937366971233 2953025228425)
                                                                          ·
                                                                            refine ⟨2214768921319, ?_, ?_⟩
                                                                            · exact (by decide : CollatzResearch.ExactOddStep 2 2953025228425 2214768921319)
                                                                            ·
                                                                              refine ⟨3322153381979, ?_, ?_⟩
                                                                              · exact (by decide : CollatzResearch.ExactOddStep 1 2214768921319 3322153381979)
                                                                              ·
                                                                                refine ⟨4983230072969, ?_, ?_⟩
                                                                                · exact (by decide : CollatzResearch.ExactOddStep 1 3322153381979 4983230072969)
                                                                                ·
                                                                                  rfl

theorem wordTrace_append {u v : List Nat} {x y z : Nat}
    (h₁ : WordTrace u x y) (h₂ : WordTrace v y z) :
    WordTrace (u ++ v) x z := by
  induction u generalizing x with
  | nil =>
      simp only [WordTrace] at h₁
      subst y
      simpa using h₂
  | cons a u ih =>
      simp only [List.cons_append, WordTrace] at h₁ ⊢
      rcases h₁ with ⟨w, hs, ht⟩
      exact ⟨w, hs, ih ht⟩

theorem prefixLift (q : Nat) :
    WordTrace prefixWord (118140960795 + q * 2 ^ 59) (4983230072969 + 3 ^ 40 * q * 2) := by
  have h := word_trace_lift prefixWord prefixTrace (b := 59) (q := q) (by decide)
  simpa [prefixWord] using h

def tailWord_18 : List Nat := [3, 2, 5, 2]
def baseStart_18 : Nat := 118140960795 + 18 * 2 ^ 59
def prefixEnd_18 : Nat := 4983230072969 + 3 ^ 40 * 18 * 2
def baseEnd_18 : Nat := 8655213106018466869

theorem tailTrace_18 : CollatzResearch.WordTrace tailWord_18 prefixEnd_18 8655213106018466869 := by
  unfold tailWord_18
  simp only [CollatzResearch.WordTrace]
  refine ⟨164128485565979816177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 437675961509279509805 164128485565979816177)
  ·
    refine ⟨123096364174484862133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164128485565979816177 123096364174484862133)
    ·
      refine ⟨11540284141357955825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123096364174484862133 11540284141357955825)
      ·
        refine ⟨8655213106018466869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11540284141357955825 8655213106018466869)
        ·
          rfl

theorem cell_18_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_18 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_18 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_18 prefixEnd_18 := by
    exact prefixLift 18
  have htrace : WordTrace (prefixWord ++ tailWord_18) baseStart_18 baseEnd_18 := by
    simpa [prefixWord, tailWord_18, baseEnd_18] using wordTrace_append hprefix tailTrace_18
  have hstable : (prefixWord ++ tailWord_18).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18).length < 2 ^ (prefixWord ++ tailWord_18).sum := by decide
  have hdescent : baseEnd_18 < baseStart_18 := by decide
  rcases family_descends (prefixWord ++ tailWord_18) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30 : List Nat := [4, 3, 4]
def baseStart_30 : Nat := 118140960795 + 30 * 2 ^ 59
def prefixEnd_30 : Nat := 4983230072969 + 3 ^ 40 * 30 * 2
def baseEnd_30 : Nat := 9616903407333709291

theorem tailTrace_30 : CollatzResearch.WordTrace tailWord_30 prefixEnd_30 9616903407333709291 := by
  unfold tailWord_30
  simp only [CollatzResearch.WordTrace]
  refine ⟨136773737348746087693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 729459932526645801029 136773737348746087693)
  ·
    refine ⟨51290151505779782885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136773737348746087693 51290151505779782885)
    ·
      refine ⟨9616903407333709291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51290151505779782885 9616903407333709291)
      ·
        rfl

theorem cell_30_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_30 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_30 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_30 prefixEnd_30 := by
    exact prefixLift 30
  have htrace : WordTrace (prefixWord ++ tailWord_30) baseStart_30 baseEnd_30 := by
    simpa [prefixWord, tailWord_30, baseEnd_30] using wordTrace_append hprefix tailTrace_30
  have hstable : (prefixWord ++ tailWord_30).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30).length < 2 ^ (prefixWord ++ tailWord_30).sum := by decide
  have hdescent : baseEnd_30 < baseStart_30 := by decide
  rcases family_descends (prefixWord ++ tailWord_30) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32 : List Nat := [2, 1, 1, 8]
def baseStart_32 : Nat := 118140960795 + 32 * 2 ^ 59
def prefixEnd_32 : Nat := 4983230072969 + 3 ^ 40 * 32 * 2
def baseEnd_32 : Nat := 15387045445164246781

theorem tailTrace_32 : CollatzResearch.WordTrace tailWord_32 prefixEnd_32 15387045445164246781 := by
  unfold tailWord_32
  simp only [CollatzResearch.WordTrace]
  refine ⟨583567945772155137175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 778090594362873516233 583567945772155137175)
  ·
    refine ⟨875351918658232705763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 583567945772155137175 875351918658232705763)
    ·
      refine ⟨1313027877987349058645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 875351918658232705763 1313027877987349058645)
      ·
        refine ⟨15387045445164246781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 1313027877987349058645 15387045445164246781)
        ·
          rfl

theorem cell_32_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_32 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_32 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_32 prefixEnd_32 := by
    exact prefixLift 32
  have htrace : WordTrace (prefixWord ++ tailWord_32) baseStart_32 baseEnd_32 := by
    simpa [prefixWord, tailWord_32, baseEnd_32] using wordTrace_append hprefix tailTrace_32
  have hstable : (prefixWord ++ tailWord_32).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32).length < 2 ^ (prefixWord ++ tailWord_32).sum := by decide
  have hdescent : baseEnd_32 < baseStart_32 := by decide
  rcases family_descends (prefixWord ++ tailWord_32) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38 : List Nat := [8]
def baseStart_38 : Nat := 118140960795 + 38 * 2 ^ 59
def prefixEnd_38 : Nat := 4983230072969 + 3 ^ 40 * 38 * 2
def baseEnd_38 : Nat := 10827920857869804631

theorem tailTrace_38 : CollatzResearch.WordTrace tailWord_38 prefixEnd_38 10827920857869804631 := by
  unfold tailWord_38
  simp only [CollatzResearch.WordTrace]
  refine ⟨10827920857869804631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 923982579871556661845 10827920857869804631)
  ·
    rfl

theorem cell_38_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_38 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_38 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_38 prefixEnd_38 := by
    exact prefixLift 38
  have htrace : WordTrace (prefixWord ++ tailWord_38) baseStart_38 baseEnd_38 := by
    simpa [prefixWord, tailWord_38, baseEnd_38] using wordTrace_append hprefix tailTrace_38
  have hstable : (prefixWord ++ tailWord_38).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38).length < 2 ^ (prefixWord ++ tailWord_38).sum := by decide
  have hdescent : baseEnd_38 < baseStart_38 := by decide
  rcases family_descends (prefixWord ++ tailWord_38) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45 : List Nat := [1, 5, 6]
def baseStart_45 : Nat := 118140960795 + 45 * 2 ^ 59
def prefixEnd_45 : Nat := 4983230072969 + 3 ^ 40 * 45 * 2
def baseEnd_45 : Nat := 7212677539076061757

theorem tailTrace_45 : CollatzResearch.WordTrace tailWord_45 prefixEnd_45 7212677539076061757 := by
  unfold tailWord_45
  simp only [CollatzResearch.WordTrace]
  refine ⟨1641284844447530497589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1094189896298353665059 1641284844447530497589)
  ·
    refine ⟨153870454166955984149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1641284844447530497589 153870454166955984149)
    ·
      refine ⟨7212677539076061757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 153870454166955984149 7212677539076061757)
      ·
        rfl

theorem cell_45_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_45 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_45 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_45 prefixEnd_45 := by
    exact prefixLift 45
  have htrace : WordTrace (prefixWord ++ tailWord_45) baseStart_45 baseEnd_45 := by
    simpa [prefixWord, tailWord_45, baseEnd_45] using wordTrace_append hprefix tailTrace_45
  have hstable : (prefixWord ++ tailWord_45).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45).length < 2 ^ (prefixWord ++ tailWord_45).sum := by decide
  have hdescent : baseEnd_45 < baseStart_45 := by decide
  rcases family_descends (prefixWord ++ tailWord_45) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66 : List Nat := [3, 6]
def baseStart_66 : Nat := 118140960795 + 66 * 2 ^ 59
def prefixEnd_66 : Nat := 4983230072969 + 3 ^ 40 * 66 * 2
def baseEnd_66 : Nat := 28209583223063871235

theorem tailTrace_66 : CollatzResearch.WordTrace tailWord_66 prefixEnd_66 28209583223063871235 := by
  unfold tailWord_66
  simp only [CollatzResearch.WordTrace]
  refine ⟨601804442092029253013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1604811845578744674701 601804442092029253013)
  ·
    refine ⟨28209583223063871235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 601804442092029253013 28209583223063871235)
    ·
      rfl

theorem cell_66_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_66 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_66 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_66 prefixEnd_66 := by
    exact prefixLift 66
  have htrace : WordTrace (prefixWord ++ tailWord_66) baseStart_66 baseEnd_66 := by
    simpa [prefixWord, tailWord_66, baseEnd_66] using wordTrace_append hprefix tailTrace_66
  have hstable : (prefixWord ++ tailWord_66).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66).length < 2 ^ (prefixWord ++ tailWord_66).sum := by decide
  have hdescent : baseEnd_66 < baseStart_66 := by decide
  rcases family_descends (prefixWord ++ tailWord_66) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102 : List Nat := [7]
def baseStart_102 : Nat := 118140960795 + 102 * 2 ^ 59
def prefixEnd_102 : Nat := 4983230072969 + 3 ^ 40 * 102 * 2
def baseEnd_102 : Nat := 58128838092910395665

theorem tailTrace_102 : CollatzResearch.WordTrace tailWord_102 prefixEnd_102 58128838092910395665 := by
  unfold tailWord_102
  simp only [CollatzResearch.WordTrace]
  refine ⟨58128838092910395665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 2480163758630843548373 58128838092910395665)
  ·
    rfl

theorem cell_102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_102 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_102 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_102 prefixEnd_102 := by
    exact prefixLift 102
  have htrace : WordTrace (prefixWord ++ tailWord_102) baseStart_102 baseEnd_102 := by
    simpa [prefixWord, tailWord_102, baseEnd_102] using wordTrace_append hprefix tailTrace_102
  have hstable : (prefixWord ++ tailWord_102).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102).length < 2 ^ (prefixWord ++ tailWord_102).sum := by decide
  have hdescent : baseEnd_102 < baseStart_102 := by decide
  rcases family_descends (prefixWord ++ tailWord_102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104 : List Nat := [2, 1, 4, 5]
def baseStart_104 : Nat := 118140960795 + 104 * 2 ^ 59
def prefixEnd_104 : Nat := 4983230072969 + 3 ^ 40 * 104 * 2
def baseEnd_104 : Nat := 50007897475056829187

theorem tailTrace_104 : CollatzResearch.WordTrace tailWord_104 prefixEnd_104 50007897475056829187 := by
  unfold tailWord_104
  simp only [CollatzResearch.WordTrace]
  refine ⟨1896595815350303447683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2528794420467071263577 1896595815350303447683)
  ·
    refine ⟨2844893723025455171525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1896595815350303447683 2844893723025455171525)
    ·
      refine ⟨533417573067272844661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2844893723025455171525 533417573067272844661)
      ·
        refine ⟨50007897475056829187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 533417573067272844661 50007897475056829187)
        ·
          rfl

theorem cell_104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_104 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_104 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_104 prefixEnd_104 := by
    exact prefixLift 104
  have htrace : WordTrace (prefixWord ++ tailWord_104) baseStart_104 baseEnd_104 := by
    simpa [prefixWord, tailWord_104, baseEnd_104] using wordTrace_append hprefix tailTrace_104
  have hstable : (prefixWord ++ tailWord_104).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104).length < 2 ^ (prefixWord ++ tailWord_104).sum := by decide
  have hdescent : baseEnd_104 < baseStart_104 := by decide
  rcases family_descends (prefixWord ++ tailWord_104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116 : List Nat := [2, 7]
def baseStart_116 : Nat := 118140960795 + 116 * 2 ^ 59
def prefixEnd_116 : Nat := 4983230072969 + 3 ^ 40 * 116 * 2
def baseEnd_116 : Nat := 49580479537812378893

theorem tailTrace_116 : CollatzResearch.WordTrace tailWord_116 prefixEnd_116 49580479537812378893 := by
  unfold tailWord_116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2115433793613328166101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2820578391484437554801 2115433793613328166101)
  ·
    refine ⟨49580479537812378893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 2115433793613328166101 49580479537812378893)
    ·
      rfl

theorem cell_116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_116 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_116 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_116 prefixEnd_116 := by
    exact prefixLift 116
  have htrace : WordTrace (prefixWord ++ tailWord_116) baseStart_116 baseEnd_116 := by
    simpa [prefixWord, tailWord_116, baseEnd_116] using wordTrace_append hprefix tailTrace_116
  have hstable : (prefixWord ++ tailWord_116).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116).length < 2 ^ (prefixWord ++ tailWord_116).sum := by decide
  have hdescent : baseEnd_116 < baseStart_116 := by decide
  rcases family_descends (prefixWord ++ tailWord_116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117 : List Nat := [1, 3, 4, 4]
def baseStart_117 : Nat := 118140960795 + 117 * 2 ^ 59
def prefixEnd_117 : Nat := 4983230072969 + 3 ^ 40 * 117 * 2
def baseEnd_117 : Nat := 56258884647120767677

theorem tailTrace_117 : CollatzResearch.WordTrace tailWord_117 prefixEnd_117 56258884647120767677 := by
  unfold tailWord_117
  simp only [CollatzResearch.WordTrace]
  refine ⟨4267340583603827118605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2844893722402551412403 4267340583603827118605)
  ·
    refine ⟨1600252718851435169477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4267340583603827118605 1600252718851435169477)
    ·
      refine ⟨300047384784644094277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1600252718851435169477 300047384784644094277)
      ·
        refine ⟨56258884647120767677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300047384784644094277 56258884647120767677)
        ·
          rfl

theorem cell_117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_117 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_117 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_117 prefixEnd_117 := by
    exact prefixLift 117
  have htrace : WordTrace (prefixWord ++ tailWord_117) baseStart_117 baseEnd_117 := by
    simpa [prefixWord, tailWord_117, baseEnd_117] using wordTrace_append hprefix tailTrace_117
  have hstable : (prefixWord ++ tailWord_117).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117).length < 2 ^ (prefixWord ++ tailWord_117).sum := by decide
  have hdescent : baseEnd_117 < baseStart_117 := by decide
  rcases family_descends (prefixWord ++ tailWord_117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130 : List Nat := [3, 4, 5]
def baseStart_130 : Nat := 118140960795 + 130 * 2 ^ 59
def prefixEnd_130 : Nat := 4983230072969 + 3 ^ 40 * 130 * 2
def baseEnd_130 : Nat := 20836623939728235389

theorem tailTrace_130 : CollatzResearch.WordTrace tailWord_130 prefixEnd_130 20836623939728235389 := by
  unfold tailWord_130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1185372384126761835461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3160993024338031561229 1185372384126761835461)
  ·
    refine ⟨222257322023767844149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1185372384126761835461 222257322023767844149)
    ·
      refine ⟨20836623939728235389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222257322023767844149 20836623939728235389)
      ·
        rfl

theorem cell_130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_130 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_130 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_130 prefixEnd_130 := by
    exact prefixLift 130
  have htrace : WordTrace (prefixWord ++ tailWord_130) baseStart_130 baseEnd_130 := by
    simpa [prefixWord, tailWord_130, baseEnd_130] using wordTrace_append hprefix tailTrace_130
  have hstable : (prefixWord ++ tailWord_130).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130).length < 2 ^ (prefixWord ++ tailWord_130).sum := by decide
  have hdescent : baseEnd_130 < baseStart_130 := by decide
  rcases family_descends (prefixWord ++ tailWord_130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134 : List Nat := [6, 4]
def baseStart_134 : Nat := 118140960795 + 134 * 2 ^ 59
def prefixEnd_134 : Nat := 4983230072969 + 3 ^ 40 * 134 * 2
def baseEnd_134 : Nat := 28637001105560920825

theorem tailTrace_134 : CollatzResearch.WordTrace tailWord_134 prefixEnd_134 28637001105560920825 := by
  unfold tailWord_134
  simp only [CollatzResearch.WordTrace]
  refine ⟨152730672562991577733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3258254348010486991637 152730672562991577733)
  ·
    refine ⟨28637001105560920825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152730672562991577733 28637001105560920825)
    ·
      rfl

theorem cell_134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_134 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_134 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_134 prefixEnd_134 := by
    exact prefixLift 134
  have htrace : WordTrace (prefixWord ++ tailWord_134) baseStart_134 baseEnd_134 := by
    simpa [prefixWord, tailWord_134, baseEnd_134] using wordTrace_append hprefix tailTrace_134
  have hstable : (prefixWord ++ tailWord_134).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134).length < 2 ^ (prefixWord ++ tailWord_134).sum := by decide
  have hdescent : baseEnd_134 < baseStart_134 := by decide
  rcases family_descends (prefixWord ++ tailWord_134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141 : List Nat := [1, 9]
def baseStart_141 : Nat := 118140960795 + 141 * 2 ^ 59
def prefixEnd_141 : Nat := 4983230072969 + 3 ^ 40 * 141 * 2
def baseEnd_141 : Nat := 30132963847593316361

theorem tailTrace_141 : CollatzResearch.WordTrace tailWord_141 prefixEnd_141 30132963847593316361 := by
  unfold tailWord_141
  simp only [CollatzResearch.WordTrace]
  refine ⟨5142692496655925992277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3428461664437283994851 5142692496655925992277)
  ·
    refine ⟨30132963847593316361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 9 5142692496655925992277 30132963847593316361)
    ·
      rfl

theorem cell_141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_141 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_141 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_141 prefixEnd_141 := by
    exact prefixLift 141
  have htrace : WordTrace (prefixWord ++ tailWord_141) baseStart_141 baseEnd_141 := by
    simpa [prefixWord, tailWord_141, baseEnd_141] using wordTrace_append hprefix tailTrace_141
  have hstable : (prefixWord ++ tailWord_141).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141).length < 2 ^ (prefixWord ++ tailWord_141).sum := by decide
  have hdescent : baseEnd_141 < baseStart_141 := by decide
  rcases family_descends (prefixWord ++ tailWord_141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166 : List Nat := [9]
def baseStart_166 : Nat := 118140960795 + 166 * 2 ^ 59
def prefixEnd_166 : Nat := 4983230072969 + 3 ^ 40 * 166 * 2
def baseEnd_166 : Nat := 23650458617520295517

theorem tailTrace_166 : CollatzResearch.WordTrace tailWord_166 prefixEnd_166 23650458617520295517 := by
  unfold tailWord_166
  simp only [CollatzResearch.WordTrace]
  refine ⟨23650458617520295517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 9 4036344937390130434901 23650458617520295517)
  ·
    rfl

theorem cell_166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_166 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_166 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_166 prefixEnd_166 := by
    exact prefixLift 166
  have htrace : WordTrace (prefixWord ++ tailWord_166) baseStart_166 baseEnd_166 := by
    simpa [prefixWord, tailWord_166, baseEnd_166] using wordTrace_append hprefix tailTrace_166
  have hstable : (prefixWord ++ tailWord_166).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166).length < 2 ^ (prefixWord ++ tailWord_166).sum := by decide
  have hdescent : baseEnd_166 < baseStart_166 := by decide
  rcases family_descends (prefixWord ++ tailWord_166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168 : List Nat := [2, 1, 8]
def baseStart_168 : Nat := 118140960795 + 168 * 2 ^ 59
def prefixEnd_168 : Nat := 4983230072969 + 3 ^ 40 * 168 * 2
def baseEnd_168 : Nat := 53854658778863120143

theorem tailTrace_168 : CollatzResearch.WordTrace tailWord_168 prefixEnd_168 53854658778863120143 := by
  unfold tailWord_168
  simp only [CollatzResearch.WordTrace]
  refine ⟨3063731699419768612579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4084975599226358150105 3063731699419768612579)
  ·
    refine ⟨4595597549129652918869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3063731699419768612579 4595597549129652918869)
    ·
      refine ⟨53854658778863120143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 4595597549129652918869 53854658778863120143)
      ·
        rfl

theorem cell_168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_168 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_168 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_168 prefixEnd_168 := by
    exact prefixLift 168
  have htrace : WordTrace (prefixWord ++ tailWord_168) baseStart_168 baseEnd_168 := by
    simpa [prefixWord, tailWord_168, baseEnd_168] using wordTrace_append hprefix tailTrace_168
  have hstable : (prefixWord ++ tailWord_168).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168).length < 2 ^ (prefixWord ++ tailWord_168).sum := by decide
  have hdescent : baseEnd_168 < baseStart_168 := by decide
  rcases family_descends (prefixWord ++ tailWord_168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182 : List Nat := [5, 1, 3, 3]
def baseStart_182 : Nat := 118140960795 + 182 * 2 ^ 59
def prefixEnd_182 : Nat := 4983230072969 + 3 ^ 40 * 182 * 2
def baseEnd_182 : Nat := 87513820507440460127

theorem tailTrace_182 : CollatzResearch.WordTrace tailWord_182 prefixEnd_182 87513820507440460127 := by
  unfold tailWord_182
  simp only [CollatzResearch.WordTrace]
  refine ⟨414880334257495514675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4425390232079952156533 414880334257495514675)
  ·
    refine ⟨622320501386243272013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 414880334257495514675 622320501386243272013)
    ·
      refine ⟨233370188019841227005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 622320501386243272013 233370188019841227005)
      ·
        refine ⟨87513820507440460127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233370188019841227005 87513820507440460127)
        ·
          rfl

theorem cell_182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_182 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_182 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_182 prefixEnd_182 := by
    exact prefixLift 182
  have htrace : WordTrace (prefixWord ++ tailWord_182) baseStart_182 baseEnd_182 := by
    simpa [prefixWord, tailWord_182, baseEnd_182] using wordTrace_append hprefix tailTrace_182
  have hstable : (prefixWord ++ tailWord_182).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182).length < 2 ^ (prefixWord ++ tailWord_182).sum := by decide
  have hdescent : baseEnd_182 < baseStart_182 := by decide
  rcases family_descends (prefixWord ++ tailWord_182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222 : List Nat := [4, 8]
def baseStart_222 : Nat := 118140960795 + 222 * 2 ^ 59
def prefixEnd_222 : Nat := 4983230072969 + 3 ^ 40 * 222 * 2
def baseEnd_222 : Nat := 11860847465634901891

theorem tailTrace_222 : CollatzResearch.WordTrace tailWord_222 prefixEnd_222 11860847465634901891 := by
  unfold tailWord_222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012125650400844961365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5398003468804506460613 1012125650400844961365)
  ·
    refine ⟨11860847465634901891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 1012125650400844961365 11860847465634901891)
    ·
      rfl

theorem cell_222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_222 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_222 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_222 prefixEnd_222 := by
    exact prefixLift 222
  have htrace : WordTrace (prefixWord ++ tailWord_222) baseStart_222 baseEnd_222 := by
    simpa [prefixWord, tailWord_222, baseEnd_222] using wordTrace_append hprefix tailTrace_222
  have hstable : (prefixWord ++ tailWord_222).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222).length < 2 ^ (prefixWord ++ tailWord_222).sum := by decide
  have hdescent : baseEnd_222 < baseStart_222 := by decide
  rcases family_descends (prefixWord ++ tailWord_222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230 : List Nat := [7]
def baseStart_230 : Nat := 118140960795 + 230 * 2 ^ 59
def prefixEnd_230 : Nat := 4983230072969 + 3 ^ 40 * 230 * 2
def baseEnd_230 : Nat := 131074830847251968471

theorem tailTrace_230 : CollatzResearch.WordTrace tailWord_230 prefixEnd_230 131074830847251968471 := by
  unfold tailWord_230
  simp only [CollatzResearch.WordTrace]
  refine ⟨131074830847251968471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 5592526116149417321429 131074830847251968471)
  ·
    rfl

theorem cell_230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_230 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_230 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_230 prefixEnd_230 := by
    exact prefixLift 230
  have htrace : WordTrace (prefixWord ++ tailWord_230) baseStart_230 baseEnd_230 := by
    simpa [prefixWord, tailWord_230, baseEnd_230] using wordTrace_append hprefix tailTrace_230
  have hstable : (prefixWord ++ tailWord_230).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230).length < 2 ^ (prefixWord ++ tailWord_230).sum := by decide
  have hdescent : baseEnd_230 < baseStart_230 := by decide
  rcases family_descends (prefixWord ++ tailWord_230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262 : List Nat := [6, 2, 3]
def baseStart_262 : Nat := 118140960795 + 262 * 2 ^ 59
def prefixEnd_262 : Nat := 4983230072969 + 3 ^ 40 * 262 * 2
def baseEnd_262 : Nat := 83987622582658515941

theorem tailTrace_262 : CollatzResearch.WordTrace tailWord_262 prefixEnd_262 83987622582658515941 := by
  unfold tailWord_262
  simp only [CollatzResearch.WordTrace]
  refine ⟨298622658071674723345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6370616705529060764693 298622658071674723345)
  ·
    refine ⟨223966993553756042509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298622658071674723345 223966993553756042509)
    ·
      refine ⟨83987622582658515941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223966993553756042509 83987622582658515941)
      ·
        rfl

theorem cell_262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_262 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_262 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_262 prefixEnd_262 := by
    exact prefixLift 262
  have htrace : WordTrace (prefixWord ++ tailWord_262) baseStart_262 baseEnd_262 := by
    simpa [prefixWord, tailWord_262, baseEnd_262] using wordTrace_append hprefix tailTrace_262
  have hstable : (prefixWord ++ tailWord_262).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262).length < 2 ^ (prefixWord ++ tailWord_262).sum := by decide
  have hdescent : baseEnd_262 < baseStart_262 := by decide
  rcases family_descends (prefixWord ++ tailWord_262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269 : List Nat := [1, 7, 3]
def baseStart_269 : Nat := 118140960795 + 269 * 2 ^ 59
def prefixEnd_269 : Nat := 4983230072969 + 3 ^ 40 * 269 * 2
def baseEnd_269 : Nat := 86231566695707109245

theorem tailTrace_269 : CollatzResearch.WordTrace tailWord_269 prefixEnd_269 86231566695707109245 := by
  unfold tailWord_269
  simp only [CollatzResearch.WordTrace]
  refine ⟨9811236032933786651861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6540824021955857767907 9811236032933786651861)
  ·
    refine ⟨229950844521885624653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 9811236032933786651861 229950844521885624653)
    ·
      refine ⟨86231566695707109245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229950844521885624653 86231566695707109245)
      ·
        rfl

theorem cell_269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_269 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_269 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_269 prefixEnd_269 := by
    exact prefixLift 269
  have htrace : WordTrace (prefixWord ++ tailWord_269) baseStart_269 baseEnd_269 := by
    simpa [prefixWord, tailWord_269, baseEnd_269] using wordTrace_append hprefix tailTrace_269
  have hstable : (prefixWord ++ tailWord_269).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269).length < 2 ^ (prefixWord ++ tailWord_269).sum := by decide
  have hdescent : baseEnd_269 < baseStart_269 := by decide
  rcases family_descends (prefixWord ++ tailWord_269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274 : List Nat := [3, 2, 4, 3]
def baseStart_274 : Nat := 118140960795 + 274 * 2 ^ 59
def prefixEnd_274 : Nat := 4983230072969 + 3 ^ 40 * 274 * 2
def baseEnd_274 : Nat := 131751575878969870979

theorem tailTrace_274 : CollatzResearch.WordTrace tailWord_274 prefixEnd_274 131751575878969870979 := by
  unfold tailWord_274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2498400253704910145969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6662400676546427055917 2498400253704910145969)
  ·
    refine ⟨1873800190278682609477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2498400253704910145969 1873800190278682609477)
    ·
      refine ⟨351337535677252989277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1873800190278682609477 351337535677252989277)
      ·
        refine ⟨131751575878969870979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 351337535677252989277 131751575878969870979)
        ·
          rfl

theorem cell_274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_274 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_274 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_274 prefixEnd_274 := by
    exact prefixLift 274
  have htrace : WordTrace (prefixWord ++ tailWord_274) baseStart_274 baseEnd_274 := by
    simpa [prefixWord, tailWord_274, baseEnd_274] using wordTrace_append hprefix tailTrace_274
  have hstable : (prefixWord ++ tailWord_274).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274).length < 2 ^ (prefixWord ++ tailWord_274).sum := by decide
  have hdescent : baseEnd_274 < baseStart_274 := by decide
  rcases family_descends (prefixWord ++ tailWord_274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276 : List Nat := [2, 4, 5]
def baseStart_276 : Nat := 118140960795 + 276 * 2 ^ 59
def prefixEnd_276 : Nat := 4983230072969 + 3 ^ 40 * 276 * 2
def baseEnd_276 : Nat := 88475510808755702549

theorem tailTrace_276 : CollatzResearch.WordTrace tailWord_276 prefixEnd_276 88475510808755702549 := by
  unfold tailWord_276
  simp only [CollatzResearch.WordTrace]
  refine ⟨5033273503786991078341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6711031338382654771121 5033273503786991078341)
  ·
    refine ⟨943738781960060827189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5033273503786991078341 943738781960060827189)
    ·
      refine ⟨88475510808755702549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 943738781960060827189 88475510808755702549)
      ·
        rfl

theorem cell_276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_276 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_276 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_276 prefixEnd_276 := by
    exact prefixLift 276
  have htrace : WordTrace (prefixWord ++ tailWord_276) baseStart_276 baseEnd_276 := by
    simpa [prefixWord, tailWord_276, baseEnd_276] using wordTrace_append hprefix tailTrace_276
  have hstable : (prefixWord ++ tailWord_276).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276).length < 2 ^ (prefixWord ++ tailWord_276).sum := by decide
  have hdescent : baseEnd_276 < baseStart_276 := by decide
  rcases family_descends (prefixWord ++ tailWord_276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278 : List Nat := [5, 4]
def baseStart_278 : Nat := 118140960795 + 278 * 2 ^ 59
def prefixEnd_278 : Nat := 4983230072969 + 3 ^ 40 * 278 * 2
def baseEnd_278 : Nat := 118822183597597543705

theorem tailTrace_278 : CollatzResearch.WordTrace tailWord_278 prefixEnd_278 118822183597597543705 := by
  unfold tailWord_278
  simp only [CollatzResearch.WordTrace]
  refine ⟨633718312520520233093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6759662000218882486325 633718312520520233093)
  ·
    refine ⟨118822183597597543705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 633718312520520233093 118822183597597543705)
    ·
      rfl

theorem cell_278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_278 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_278 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_278 prefixEnd_278 := by
    exact prefixLift 278
  have htrace : WordTrace (prefixWord ++ tailWord_278) baseStart_278 baseEnd_278 := by
    simpa [prefixWord, tailWord_278, baseEnd_278] using wordTrace_append hprefix tailTrace_278
  have hstable : (prefixWord ++ tailWord_278).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278).length < 2 ^ (prefixWord ++ tailWord_278).sum := by decide
  have hdescent : baseEnd_278 < baseStart_278 := by decide
  rcases family_descends (prefixWord ++ tailWord_278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294 : List Nat := [8]
def baseStart_294 : Nat := 118140960795 + 294 * 2 ^ 59
def prefixEnd_294 : Nat := 4983230072969 + 3 ^ 40 * 294 * 2
def baseEnd_294 : Nat := 83773913612211377437

theorem tailTrace_294 : CollatzResearch.WordTrace tailWord_294 prefixEnd_294 83773913612211377437 := by
  unfold tailWord_294
  simp only [CollatzResearch.WordTrace]
  refine ⟨83773913612211377437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 7148707294908704207957 83773913612211377437)
  ·
    rfl

theorem cell_294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_294 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_294 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_294 prefixEnd_294 := by
    exact prefixLift 294
  have htrace : WordTrace (prefixWord ++ tailWord_294) baseStart_294 baseEnd_294 := by
    simpa [prefixWord, tailWord_294, baseEnd_294] using wordTrace_append hprefix tailTrace_294
  have hstable : (prefixWord ++ tailWord_294).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294).length < 2 ^ (prefixWord ++ tailWord_294).sum := by decide
  have hdescent : baseEnd_294 < baseStart_294 := by decide
  rcases family_descends (prefixWord ++ tailWord_294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322 : List Nat := [3, 8]
def baseStart_322 : Nat := 118140960795 + 322 * 2 ^ 59
def prefixEnd_322 : Nat := 4983230072969 + 3 ^ 40 * 322 * 2
def baseEnd_322 : Nat := 34407143088644057611

theorem tailTrace_322 : CollatzResearch.WordTrace tailWord_322 prefixEnd_322 34407143088644057611 := by
  unfold tailWord_322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2936076210230959582805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7829536560615892220813 2936076210230959582805)
  ·
    refine ⟨34407143088644057611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 2936076210230959582805 34407143088644057611)
    ·
      rfl

theorem cell_322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_322 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_322 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_322 prefixEnd_322 := by
    exact prefixLift 322
  have htrace : WordTrace (prefixWord ++ tailWord_322) baseStart_322 baseEnd_322 := by
    simpa [prefixWord, tailWord_322, baseEnd_322] using wordTrace_append hprefix tailTrace_322
  have hstable : (prefixWord ++ tailWord_322).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322).length < 2 ^ (prefixWord ++ tailWord_322).sum := by decide
  have hdescent : baseEnd_322 < baseStart_322 := by decide
  rcases family_descends (prefixWord ++ tailWord_322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326 : List Nat := [6, 1, 1, 4]
def baseStart_326 : Nat := 118140960795 + 326 * 2 ^ 59
def prefixEnd_326 : Nat := 4983230072969 + 3 ^ 40 * 326 * 2
def baseEnd_326 : Nat := 156755524567225624939

theorem tailTrace_326 : CollatzResearch.WordTrace tailWord_326 prefixEnd_326 156755524567225624939 := by
  unfold tailWord_326
  simp only [CollatzResearch.WordTrace]
  refine ⟨371568650826016296151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7926797884288347651221 371568650826016296151)
  ·
    refine ⟨557352976239024444227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 371568650826016296151 557352976239024444227)
    ·
      refine ⟨836029464358536666341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 557352976239024444227 836029464358536666341)
      ·
        refine ⟨156755524567225624939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 836029464358536666341 156755524567225624939)
        ·
          rfl

theorem cell_326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_326 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_326 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_326 prefixEnd_326 := by
    exact prefixLift 326
  have htrace : WordTrace (prefixWord ++ tailWord_326) baseStart_326 baseEnd_326 := by
    simpa [prefixWord, tailWord_326, baseEnd_326] using wordTrace_append hprefix tailTrace_326
  have hstable : (prefixWord ++ tailWord_326).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326).length < 2 ^ (prefixWord ++ tailWord_326).sum := by decide
  have hdescent : baseEnd_326 < baseStart_326 := by decide
  rcases family_descends (prefixWord ++ tailWord_326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333 : List Nat := [1, 6, 1, 4]
def baseStart_333 : Nat := 118140960795 + 333 * 2 ^ 59
def prefixEnd_333 : Nat := 4983230072969 + 3 ^ 40 * 333 * 2
def baseEnd_333 : Nat := 160121440736798514895

theorem tailTrace_333 : CollatzResearch.WordTrace tailWord_333 prefixEnd_333 160121440736798514895 := by
  unfold tailWord_333
  simp only [CollatzResearch.WordTrace]
  refine ⟨12145507801072716981653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8097005200715144654435 12145507801072716981653)
  ·
    refine ⟨569320678175283608515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12145507801072716981653 569320678175283608515)
    ·
      refine ⟨853981017262925412773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 569320678175283608515 853981017262925412773)
      ·
        refine ⟨160121440736798514895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 853981017262925412773 160121440736798514895)
        ·
          rfl

theorem cell_333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_333 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_333 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_333 prefixEnd_333 := by
    exact prefixLift 333
  have htrace : WordTrace (prefixWord ++ tailWord_333) baseStart_333 baseEnd_333 := by
    simpa [prefixWord, tailWord_333, baseEnd_333] using wordTrace_append hprefix tailTrace_333
  have hstable : (prefixWord ++ tailWord_333).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333).length < 2 ^ (prefixWord ++ tailWord_333).sum := by decide
  have hdescent : baseEnd_333 < baseStart_333 := by decide
  rcases family_descends (prefixWord ++ tailWord_333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358 : List Nat := [7]
def baseStart_358 : Nat := 118140960795 + 358 * 2 ^ 59
def prefixEnd_358 : Nat := 4983230072969 + 3 ^ 40 * 358 * 2
def baseEnd_358 : Nat := 204020823601593541277

theorem tailTrace_358 : CollatzResearch.WordTrace tailWord_358 prefixEnd_358 204020823601593541277 := by
  unfold tailWord_358
  simp only [CollatzResearch.WordTrace]
  refine ⟨204020823601593541277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 8704888473667991094485 204020823601593541277)
  ·
    rfl

theorem cell_358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_358 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_358 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_358 prefixEnd_358 := by
    exact prefixLift 358
  have htrace : WordTrace (prefixWord ++ tailWord_358) baseStart_358 baseEnd_358 := by
    simpa [prefixWord, tailWord_358, baseEnd_358] using wordTrace_append hprefix tailTrace_358
  have hstable : (prefixWord ++ tailWord_358).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358).length < 2 ^ (prefixWord ++ tailWord_358).sum := by decide
  have hdescent : baseEnd_358 < baseStart_358 := by decide
  rcases family_descends (prefixWord ++ tailWord_358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366 : List Nat := [4, 1, 2, 5]
def baseStart_366 : Nat := 118140960795 + 366 * 2 ^ 59
def prefixEnd_366 : Nat := 4983230072969 + 3 ^ 40 * 366 * 2
def baseEnd_366 : Nat := 175989331250499281831

theorem tailTrace_366 : CollatzResearch.WordTrace tailWord_366 prefixEnd_366 175989331250499281831 := by
  unfold tailWord_366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668639585189919116619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8899411121012901955301 1668639585189919116619)
  ·
    refine ⟨2502959377784878674929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1668639585189919116619 2502959377784878674929)
    ·
      refine ⟨1877219533338659006197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2502959377784878674929 1877219533338659006197)
      ·
        refine ⟨175989331250499281831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1877219533338659006197 175989331250499281831)
        ·
          rfl

theorem cell_366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_366 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_366 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_366 prefixEnd_366 := by
    exact prefixLift 366
  have htrace : WordTrace (prefixWord ++ tailWord_366) baseStart_366 baseEnd_366 := by
    simpa [prefixWord, tailWord_366, baseEnd_366] using wordTrace_append hprefix tailTrace_366
  have hstable : (prefixWord ++ tailWord_366).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366).length < 2 ^ (prefixWord ++ tailWord_366).sum := by decide
  have hdescent : baseEnd_366 < baseStart_366 := by decide
  rcases family_descends (prefixWord ++ tailWord_366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372 : List Nat := [2, 8]
def baseStart_372 : Nat := 118140960795 + 372 * 2 ^ 59
def prefixEnd_372 : Nat := 4983230072969 + 3 ^ 40 * 372 * 2
def baseEnd_372 : Nat := 79499734334662369051

theorem tailTrace_372 : CollatzResearch.WordTrace tailWord_372 prefixEnd_372 79499734334662369051 := by
  unfold tailWord_372
  simp only [CollatzResearch.WordTrace]
  refine ⟨6783977329891188825685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9045303106521585100913 6783977329891188825685)
  ·
    refine ⟨79499734334662369051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 6783977329891188825685 79499734334662369051)
    ·
      rfl

theorem cell_372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_372 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_372 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_372 prefixEnd_372 := by
    exact prefixLift 372
  have htrace : WordTrace (prefixWord ++ tailWord_372) baseStart_372 baseEnd_372 := by
    simpa [prefixWord, tailWord_372, baseEnd_372] using wordTrace_append hprefix tailTrace_372
  have hstable : (prefixWord ++ tailWord_372).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372).length < 2 ^ (prefixWord ++ tailWord_372).sum := by decide
  have hdescent : baseEnd_372 < baseStart_372 := by decide
  rcases family_descends (prefixWord ++ tailWord_372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390 : List Nat := [6, 3]
def baseStart_390 : Nat := 118140960795 + 390 * 2 ^ 59
def prefixEnd_390 : Nat := 4983230072969 + 3 ^ 40 * 390 * 2
def baseEnd_390 : Nat := 166692991342634200859

theorem tailTrace_390 : CollatzResearch.WordTrace tailWord_390 prefixEnd_390 166692991342634200859 := by
  unfold tailWord_390
  simp only [CollatzResearch.WordTrace]
  refine ⟨444514643580357868957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9482979063047634537749 444514643580357868957)
  ·
    refine ⟨166692991342634200859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 444514643580357868957 166692991342634200859)
    ·
      rfl

theorem cell_390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_390 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_390 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_390 prefixEnd_390 := by
    exact prefixLift 390
  have htrace : WordTrace (prefixWord ++ tailWord_390) baseStart_390 baseEnd_390 := by
    simpa [prefixWord, tailWord_390, baseEnd_390] using wordTrace_append hprefix tailTrace_390
  have hstable : (prefixWord ++ tailWord_390).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390).length < 2 ^ (prefixWord ++ tailWord_390).sum := by decide
  have hdescent : baseEnd_390 < baseStart_390 := by decide
  rcases family_descends (prefixWord ++ tailWord_390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397 : List Nat := [1, 8]
def baseStart_397 : Nat := 118140960795 + 397 * 2 ^ 59
def prefixEnd_397 : Nat := 4983230072969 + 3 ^ 40 * 397 * 2
def baseEnd_397 : Nat := 169684916826698991931

theorem tailTrace_397 : CollatzResearch.WordTrace tailWord_397 prefixEnd_397 169684916826698991931 := by
  unfold tailWord_397
  simp only [CollatzResearch.WordTrace]
  refine ⟨14479779569211647311445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9653186379474431540963 14479779569211647311445)
  ·
    refine ⟨169684916826698991931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 14479779569211647311445 169684916826698991931)
    ·
      rfl

theorem cell_397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_397 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_397 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_397 prefixEnd_397 := by
    exact prefixLift 397
  have htrace : WordTrace (prefixWord ++ tailWord_397) baseStart_397 baseEnd_397 := by
    simpa [prefixWord, tailWord_397, baseEnd_397] using wordTrace_append hprefix tailTrace_397
  have hstable : (prefixWord ++ tailWord_397).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397).length < 2 ^ (prefixWord ++ tailWord_397).sum := by decide
  have hdescent : baseEnd_397 < baseStart_397 := by decide
  rcases family_descends (prefixWord ++ tailWord_397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412 : List Nat := [2, 2, 3, 5]
def baseStart_412 : Nat := 118140960795 + 412 * 2 ^ 59
def prefixEnd_412 : Nat := 4983230072969 + 3 ^ 40 * 412 * 2
def baseEnd_412 : Nat := 198108208936263987257

theorem tailTrace_412 : CollatzResearch.WordTrace tailWord_412 prefixEnd_412 198108208936263987257 := by
  unfold tailWord_412
  simp only [CollatzResearch.WordTrace]
  refine ⟨7513437257434604553745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10017916343246139404993 7513437257434604553745)
  ·
    refine ⟨5635077943075953415309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7513437257434604553745 5635077943075953415309)
    ·
      refine ⟨2113154228653482530741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5635077943075953415309 2113154228653482530741)
      ·
        refine ⟨198108208936263987257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2113154228653482530741 198108208936263987257)
        ·
          rfl

theorem cell_412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_412 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_412 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_412 prefixEnd_412 := by
    exact prefixLift 412
  have htrace : WordTrace (prefixWord ++ tailWord_412) baseStart_412 baseEnd_412 := by
    simpa [prefixWord, tailWord_412, baseEnd_412] using wordTrace_append hprefix tailTrace_412
  have hstable : (prefixWord ++ tailWord_412).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412).length < 2 ^ (prefixWord ++ tailWord_412).sum := by decide
  have hdescent : baseEnd_412 < baseStart_412 := by decide
  rcases family_descends (prefixWord ++ tailWord_412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430 : List Nat := [4, 1, 6]
def baseStart_430 : Nat := 118140960795 + 430 * 2 ^ 59
def prefixEnd_430 : Nat := 4983230072969 + 3 ^ 40 * 430 * 2
def baseEnd_430 : Nat := 137842281295824755239

theorem tailTrace_430 : CollatzResearch.WordTrace tailWord_430 prefixEnd_430 137842281295824755239 := by
  unfold tailWord_430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1960423556207285407843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10455592299772188841829 1960423556207285407843)
  ·
    refine ⟨2940635334310928111765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1960423556207285407843 2940635334310928111765)
    ·
      refine ⟨137842281295824755239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2940635334310928111765 137842281295824755239)
      ·
        rfl

theorem cell_430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_430 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_430 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_430 prefixEnd_430 := by
    exact prefixLift 430
  have htrace : WordTrace (prefixWord ++ tailWord_430) baseStart_430 baseEnd_430 := by
    simpa [prefixWord, tailWord_430, baseEnd_430] using wordTrace_append hprefix tailTrace_430
  have hstable : (prefixWord ++ tailWord_430).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430).length < 2 ^ (prefixWord ++ tailWord_430).sum := by decide
  have hdescent : baseEnd_430 < baseStart_430 := by decide
  rcases family_descends (prefixWord ++ tailWord_430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438 : List Nat := [5, 1, 6]
def baseStart_438 : Nat := 118140960795 + 438 * 2 ^ 59
def prefixEnd_438 : Nat := 4983230072969 + 3 ^ 40 * 438 * 2
def baseEnd_438 : Nat := 70203394426797288079

theorem tailTrace_438 : CollatzResearch.WordTrace tailWord_438 prefixEnd_438 70203394426797288079 := by
  unfold tailWord_438
  simp only [CollatzResearch.WordTrace]
  refine ⟨998448276292228097123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10650114947117099702645 998448276292228097123)
  ·
    refine ⟨1497672414438342145685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 998448276292228097123 1497672414438342145685)
    ·
      refine ⟨70203394426797288079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1497672414438342145685 70203394426797288079)
      ·
        rfl

theorem cell_438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_438 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_438 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_438 prefixEnd_438 := by
    exact prefixLift 438
  have htrace : WordTrace (prefixWord ++ tailWord_438) baseStart_438 baseEnd_438 := by
    simpa [prefixWord, tailWord_438, baseEnd_438] using wordTrace_append hprefix tailTrace_438
  have hstable : (prefixWord ++ tailWord_438).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438).length < 2 ^ (prefixWord ++ tailWord_438).sum := by decide
  have hdescent : baseEnd_438 < baseStart_438 := by decide
  rcases family_descends (prefixWord ++ tailWord_438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450 : List Nat := [3, 5, 2, 2]
def baseStart_450 : Nat := 118140960795 + 450 * 2 ^ 59
def prefixEnd_450 : Nat := 4983230072969 + 3 ^ 40 * 450 * 2
def baseEnd_450 : Nat := 216380325285373961305

theorem tailTrace_450 : CollatzResearch.WordTrace tailWord_450 prefixEnd_450 216380325285373961305 := by
  unfold tailWord_450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4103212094300424747701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10941898918134465993869 4103212094300424747701)
  ·
    refine ⟨384676133840664820097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4103212094300424747701 384676133840664820097)
    ·
      refine ⟨288507100380498615073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384676133840664820097 288507100380498615073)
      ·
        refine ⟨216380325285373961305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288507100380498615073 216380325285373961305)
        ·
          rfl

theorem cell_450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_450 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_450 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_450 prefixEnd_450 := by
    exact prefixLift 450
  have htrace : WordTrace (prefixWord ++ tailWord_450) baseStart_450 baseEnd_450 := by
    simpa [prefixWord, tailWord_450, baseEnd_450] using wordTrace_append hprefix tailTrace_450
  have hstable : (prefixWord ++ tailWord_450).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450).length < 2 ^ (prefixWord ++ tailWord_450).sum := by decide
  have hdescent : baseEnd_450 < baseStart_450 := by decide
  rcases family_descends (prefixWord ++ tailWord_450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476 : List Nat := [2, 2, 7]
def baseStart_476 : Nat := 118140960795 + 476 * 2 ^ 59
def prefixEnd_476 : Nat := 4983230072969 + 3 ^ 40 * 476 * 2
def baseEnd_476 : Nat := 152588199753001225523

theorem tailTrace_476 : CollatzResearch.WordTrace tailWord_476 prefixEnd_476 152588199753001225523 := by
  unfold tailWord_476
  simp only [CollatzResearch.WordTrace]
  refine ⟨8680573141504069718641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11574097522005426291521 8680573141504069718641)
  ·
    refine ⟨6510429856128052288981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8680573141504069718641 6510429856128052288981)
    ·
      refine ⟨152588199753001225523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 6510429856128052288981 152588199753001225523)
      ·
        rfl

theorem cell_476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_476 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_476 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_476 prefixEnd_476 := by
    exact prefixLift 476
  have htrace : WordTrace (prefixWord ++ tailWord_476) baseStart_476 baseEnd_476 := by
    simpa [prefixWord, tailWord_476, baseEnd_476] using wordTrace_append hprefix tailTrace_476
  have hstable : (prefixWord ++ tailWord_476).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476).length < 2 ^ (prefixWord ++ tailWord_476).sum := by decide
  have hdescent : baseEnd_476 < baseStart_476 := by decide
  rcases family_descends (prefixWord ++ tailWord_476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478 : List Nat := [4, 5]
def baseStart_478 : Nat := 118140960795 + 478 * 2 ^ 59
def prefixEnd_478 : Nat := 4983230072969 + 3 ^ 40 * 478 * 2
def baseEnd_478 : Nat := 204305768856591574337

theorem tailTrace_478 : CollatzResearch.WordTrace tailWord_478 prefixEnd_478 204305768856591574337 := by
  unfold tailWord_478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2179261534470310126261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11622728183841654006725 2179261534470310126261)
  ·
    refine ⟨204305768856591574337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2179261534470310126261 204305768856591574337)
    ·
      rfl

theorem cell_478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_478 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_478 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_478 prefixEnd_478 := by
    exact prefixLift 478
  have htrace : WordTrace (prefixWord ++ tailWord_478) baseStart_478 baseEnd_478 := by
    simpa [prefixWord, tailWord_478, baseEnd_478] using wordTrace_append hprefix tailTrace_478
  have hstable : (prefixWord ++ tailWord_478).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478).length < 2 ^ (prefixWord ++ tailWord_478).sum := by decide
  have hdescent : baseEnd_478 < baseStart_478 := by decide
  rcases family_descends (prefixWord ++ tailWord_478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486 : List Nat := [7]
def baseStart_486 : Nat := 118140960795 + 486 * 2 ^ 59
def prefixEnd_486 : Nat := 4983230072969 + 3 ^ 40 * 486 * 2
def baseEnd_486 : Nat := 276966816355935114083

theorem tailTrace_486 : CollatzResearch.WordTrace tailWord_486 prefixEnd_486 276966816355935114083 := by
  unfold tailWord_486
  simp only [CollatzResearch.WordTrace]
  refine ⟨276966816355935114083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 11817250831186564867541 276966816355935114083)
  ·
    rfl

theorem cell_486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_486 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_486 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_486 prefixEnd_486 := by
    exact prefixLift 486
  have htrace : WordTrace (prefixWord ++ tailWord_486) baseStart_486 baseEnd_486 := by
    simpa [prefixWord, tailWord_486, baseEnd_486] using wordTrace_append hprefix tailTrace_486
  have hstable : (prefixWord ++ tailWord_486).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486).length < 2 ^ (prefixWord ++ tailWord_486).sum := by decide
  have hdescent : baseEnd_486 < baseStart_486 := by decide
  rcases family_descends (prefixWord ++ tailWord_486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510 : List Nat := [4, 2, 2, 4]
def baseStart_510 : Nat := 118140960795 + 510 * 2 ^ 59
def prefixEnd_510 : Nat := 4983230072969 + 3 ^ 40 * 510 * 2
def baseEnd_510 : Nat := 245231035310284446643

theorem tailTrace_510 : CollatzResearch.WordTrace tailWord_510 prefixEnd_510 245231035310284446643 := by
  unfold tailWord_510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2325153519978993271873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12400818773221297449989 2325153519978993271873)
  ·
    refine ⟨1743865139984244953905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2325153519978993271873 1743865139984244953905)
    ·
      refine ⟨1307898854988183715429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1743865139984244953905 1307898854988183715429)
      ·
        refine ⟨245231035310284446643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1307898854988183715429 245231035310284446643)
        ·
          rfl

theorem cell_510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_510 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_510 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_510 prefixEnd_510 := by
    exact prefixLift 510
  have htrace : WordTrace (prefixWord ++ tailWord_510) baseStart_510 baseEnd_510 := by
    simpa [prefixWord, tailWord_510, baseEnd_510] using wordTrace_append hprefix tailTrace_510
  have hstable : (prefixWord ++ tailWord_510).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510).length < 2 ^ (prefixWord ++ tailWord_510).sum := by decide
  have hdescent : baseEnd_510 < baseStart_510 := by decide
  rcases family_descends (prefixWord ++ tailWord_510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530 : List Nat := [3, 2, 7]
def baseStart_530 : Nat := 118140960795 + 530 * 2 ^ 59
def prefixEnd_530 : Nat := 4983230072969 + 3 ^ 40 * 530 * 2
def baseEnd_530 : Nat := 84949312883973758363

theorem tailTrace_530 : CollatzResearch.WordTrace tailWord_530 prefixEnd_530 84949312883973758363 := by
  unfold tailWord_530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4832672021843840475761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12887125391583574602029 4832672021843840475761)
  ·
    refine ⟨3624504016382880356821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4832672021843840475761 3624504016382880356821)
    ·
      refine ⟨84949312883973758363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 3624504016382880356821 84949312883973758363)
      ·
        rfl

theorem cell_530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_530 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_530 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_530 prefixEnd_530 := by
    exact prefixLift 530
  have htrace : WordTrace (prefixWord ++ tailWord_530) baseStart_530 baseEnd_530 := by
    simpa [prefixWord, tailWord_530, baseEnd_530] using wordTrace_append hprefix tailTrace_530
  have hstable : (prefixWord ++ tailWord_530).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530).length < 2 ^ (prefixWord ++ tailWord_530).sum := by decide
  have hdescent : baseEnd_530 < baseStart_530 := by decide
  rcases family_descends (prefixWord ++ tailWord_530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534 : List Nat := [5, 5]
def baseStart_534 : Nat := 118140960795 + 534 * 2 ^ 59
def prefixEnd_534 : Nat := 4983230072969 + 3 ^ 40 * 534 * 2
def baseEnd_534 : Nat := 114120586364554951457

theorem tailTrace_534 : CollatzResearch.WordTrace tailWord_534 prefixEnd_534 114120586364554951457 := by
  unfold tailWord_534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1217286254555252815541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12984386715256030032437 1217286254555252815541)
  ·
    refine ⟨114120586364554951457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1217286254555252815541 114120586364554951457)
    ·
      rfl

theorem cell_534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_534 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_534 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_534 prefixEnd_534 := by
    exact prefixLift 534
  have htrace : WordTrace (prefixWord ++ tailWord_534) baseStart_534 baseEnd_534 := by
    simpa [prefixWord, tailWord_534, baseEnd_534] using wordTrace_append hprefix tailTrace_534
  have hstable : (prefixWord ++ tailWord_534).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534).length < 2 ^ (prefixWord ++ tailWord_534).sum := by decide
  have hdescent : baseEnd_534 < baseStart_534 := by decide
  rcases family_descends (prefixWord ++ tailWord_534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542 : List Nat := [4, 3, 3, 2]
def baseStart_542 : Nat := 118140960795 + 542 * 2 ^ 59
def prefixEnd_542 : Nat := 4983230072969 + 3 ^ 40 * 542 * 2
def baseEnd_542 : Nat := 260618080656903372157

theorem tailTrace_542 : CollatzResearch.WordTrace tailWord_542 prefixEnd_542 260618080656903372157 := by
  unfold tailWord_542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2471045505487676417485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13178909362600940893253 2471045505487676417485)
  ·
    refine ⟨926642064557878656557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2471045505487676417485 926642064557878656557)
    ·
      refine ⟨347490774209204496209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 926642064557878656557 347490774209204496209)
      ·
        refine ⟨260618080656903372157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347490774209204496209 260618080656903372157)
        ·
          rfl

theorem cell_542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_542 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_542 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_542 prefixEnd_542 := by
    exact prefixLift 542
  have htrace : WordTrace (prefixWord ++ tailWord_542) baseStart_542 baseEnd_542 := by
    simpa [prefixWord, tailWord_542, baseEnd_542] using wordTrace_append hprefix tailTrace_542
  have hstable : (prefixWord ++ tailWord_542).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542).length < 2 ^ (prefixWord ++ tailWord_542).sum := by decide
  have hdescent : baseEnd_542 < baseStart_542 := by decide
  rcases family_descends (prefixWord ++ tailWord_542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550 : List Nat := [8]
def baseStart_550 : Nat := 118140960795 + 550 * 2 ^ 59
def prefixEnd_550 : Nat := 4983230072969 + 3 ^ 40 * 550 * 2
def baseEnd_550 : Nat := 156719906366552950243

theorem tailTrace_550 : CollatzResearch.WordTrace tailWord_550 prefixEnd_550 156719906366552950243 := by
  unfold tailWord_550
  simp only [CollatzResearch.WordTrace]
  refine ⟨156719906366552950243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 13373432009945851754069 156719906366552950243)
  ·
    rfl

theorem cell_550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_550 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_550 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_550 prefixEnd_550 := by
    exact prefixLift 550
  have htrace : WordTrace (prefixWord ++ tailWord_550) baseStart_550 baseEnd_550 := by
    simpa [prefixWord, tailWord_550, baseEnd_550] using wordTrace_append hprefix tailTrace_550
  have hstable : (prefixWord ++ tailWord_550).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550).length < 2 ^ (prefixWord ++ tailWord_550).sum := by decide
  have hdescent : baseEnd_550 < baseStart_550 := by decide
  rcases family_descends (prefixWord ++ tailWord_550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578 : List Nat := [3, 6]
def baseStart_578 : Nat := 118140960795 + 578 * 2 ^ 59
def prefixEnd_578 : Nat := 4983230072969 + 3 ^ 40 * 578 * 2
def baseEnd_578 : Nat := 247047561486088589653

theorem tailTrace_578 : CollatzResearch.WordTrace tailWord_578 prefixEnd_578 247047561486088589653 := by
  unfold tailWord_578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5270347978369889912597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14054261275653039766925 5270347978369889912597)
  ·
    refine ⟨247047561486088589653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5270347978369889912597 247047561486088589653)
    ·
      rfl

theorem cell_578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_578 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_578 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_578 prefixEnd_578 := by
    exact prefixLift 578
  have htrace : WordTrace (prefixWord ++ tailWord_578) baseStart_578 baseEnd_578 := by
    simpa [prefixWord, tailWord_578, baseEnd_578] using wordTrace_append hprefix tailTrace_578
  have hstable : (prefixWord ++ tailWord_578).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578).length < 2 ^ (prefixWord ++ tailWord_578).sum := by decide
  have hdescent : baseEnd_578 < baseStart_578 := by decide
  rcases family_descends (prefixWord ++ tailWord_578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614 : List Nat := [7]
def baseStart_614 : Nat := 118140960795 + 614 * 2 ^ 59
def prefixEnd_614 : Nat := 4983230072969 + 3 ^ 40 * 614 * 2
def baseEnd_614 : Nat := 349912809110276686889

theorem tailTrace_614 : CollatzResearch.WordTrace tailWord_614 prefixEnd_614 349912809110276686889 := by
  unfold tailWord_614
  simp only [CollatzResearch.WordTrace]
  refine ⟨349912809110276686889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 14929613188705138640597 349912809110276686889)
  ·
    rfl

theorem cell_614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_614 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_614 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_614 prefixEnd_614 := by
    exact prefixLift 614
  have htrace : WordTrace (prefixWord ++ tailWord_614) baseStart_614 baseEnd_614 := by
    simpa [prefixWord, tailWord_614, baseEnd_614] using wordTrace_append hprefix tailTrace_614
  have hstable : (prefixWord ++ tailWord_614).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614).length < 2 ^ (prefixWord ++ tailWord_614).sum := by decide
  have hdescent : baseEnd_614 < baseStart_614 := by decide
  rcases family_descends (prefixWord ++ tailWord_614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628 : List Nat := [2, 7]
def baseStart_628 : Nat := 118140960795 + 628 * 2 ^ 59
def prefixEnd_628 : Nat := 4983230072969 + 3 ^ 40 * 628 * 2
def baseEnd_628 : Nat := 268418457800837097311

theorem tailTrace_628 : CollatzResearch.WordTrace tailWord_628 prefixEnd_628 268418457800837097311 := by
  unfold tailWord_628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11452520866169049485269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15270027821558732647025 11452520866169049485269)
  ·
    refine ⟨268418457800837097311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11452520866169049485269 268418457800837097311)
    ·
      rfl

theorem cell_628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_628 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_628 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_628 prefixEnd_628 := by
    exact prefixLift 628
  have htrace : WordTrace (prefixWord ++ tailWord_628) baseStart_628 baseEnd_628 := by
    simpa [prefixWord, tailWord_628, baseEnd_628] using wordTrace_append hprefix tailTrace_628
  have hstable : (prefixWord ++ tailWord_628).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628).length < 2 ^ (prefixWord ++ tailWord_628).sum := by decide
  have hdescent : baseEnd_628 < baseStart_628 := by decide
  rcases family_descends (prefixWord ++ tailWord_628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_646 : List Nat := [6, 5]
def baseStart_646 : Nat := 118140960795 + 646 * 2 ^ 59
def prefixEnd_646 : Nat := 4983230072969 + 3 ^ 40 * 646 * 2
def baseEnd_646 : Nat := 69027995118536640017

theorem tailTrace_646 : CollatzResearch.WordTrace tailWord_646 prefixEnd_646 69027995118536640017 := by
  unfold tailWord_646
  simp only [CollatzResearch.WordTrace]
  refine ⟨736298614597724160181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15707703778084782083861 736298614597724160181)
  ·
    refine ⟨69027995118536640017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 736298614597724160181 69027995118536640017)
    ·
      rfl

theorem cell_646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_646 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_646 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_646 prefixEnd_646 := by
    exact prefixLift 646
  have htrace : WordTrace (prefixWord ++ tailWord_646) baseStart_646 baseEnd_646 := by
    simpa [prefixWord, tailWord_646, baseEnd_646] using wordTrace_append hprefix tailTrace_646
  have hstable : (prefixWord ++ tailWord_646).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_646).length < 2 ^ (prefixWord ++ tailWord_646).sum := by decide
  have hdescent : baseEnd_646 < baseStart_646 := by decide
  rcases family_descends (prefixWord ++ tailWord_646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_648 : List Nat := [2, 1, 3, 6]
def baseStart_648 : Nat := 118140960795 + 648 * 2 ^ 59
def prefixEnd_648 : Nat := 4983230072969 + 3 ^ 40 * 648 * 2
def baseEnd_648 : Nat := 311587668367578562921

theorem tailTrace_648 : CollatzResearch.WordTrace tailWord_648 prefixEnd_648 311587668367578562921 := by
  unfold tailWord_648
  simp only [CollatzResearch.WordTrace]
  refine ⟨11817250829940757349299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15756334439921009799065 11817250829940757349299)
  ·
    refine ⟨17725876244911136023949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11817250829940757349299 17725876244911136023949)
    ·
      refine ⟨6647203591841676008981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17725876244911136023949 6647203591841676008981)
      ·
        refine ⟨311587668367578562921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6647203591841676008981 311587668367578562921)
        ·
          rfl

theorem cell_648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_648 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_648 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_648 prefixEnd_648 := by
    exact prefixLift 648
  have htrace : WordTrace (prefixWord ++ tailWord_648) baseStart_648 baseEnd_648 := by
    simpa [prefixWord, tailWord_648, baseEnd_648] using wordTrace_append hprefix tailTrace_648
  have hstable : (prefixWord ++ tailWord_648).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_648).length < 2 ^ (prefixWord ++ tailWord_648).sum := by decide
  have hdescent : baseEnd_648 < baseStart_648 := by decide
  rcases family_descends (prefixWord ++ tailWord_648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_653 : List Nat := [1, 10]
def baseStart_653 : Nat := 118140960795 + 653 * 2 ^ 59
def prefixEnd_653 : Nat := 4983230072969 + 3 ^ 40 * 653 * 2
def baseEnd_653 : Nat := 69775976489552837785

theorem tailTrace_653 : CollatzResearch.WordTrace tailWord_653 prefixEnd_653 69775976489552837785 := by
  unfold tailWord_653
  simp only [CollatzResearch.WordTrace]
  refine ⟨23816866641767368630613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15877911094511579087075 23816866641767368630613)
  ·
    refine ⟨69775976489552837785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 10 23816866641767368630613 69775976489552837785)
    ·
      rfl

theorem cell_653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_653 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_653 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_653 prefixEnd_653 := by
    exact prefixLift 653
  have htrace : WordTrace (prefixWord ++ tailWord_653) baseStart_653 baseEnd_653 := by
    simpa [prefixWord, tailWord_653, baseEnd_653] using wordTrace_append hprefix tailTrace_653
  have hstable : (prefixWord ++ tailWord_653).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_653).length < 2 ^ (prefixWord ++ tailWord_653).sum := by decide
  have hdescent : baseEnd_653 < baseStart_653 := by decide
  rcases family_descends (prefixWord ++ tailWord_653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662 : List Nat := [5, 3, 3]
def baseStart_662 : Nat := 118140960795 + 662 * 2 ^ 59
def prefixEnd_662 : Nat := 4983230072969 + 3 ^ 40 * 662 * 2
def baseEnd_662 : Nat := 212213000471149561889

theorem tailTrace_662 : CollatzResearch.WordTrace tailWord_662 prefixEnd_662 212213000471149561889 := by
  unfold tailWord_662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1509070225572619106765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16096749072774603805493 1509070225572619106765)
  ·
    refine ⟨565901334589732165037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1509070225572619106765 565901334589732165037)
    ·
      refine ⟨212213000471149561889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 565901334589732165037 212213000471149561889)
      ·
        rfl

theorem cell_662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_662 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_662 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_662 prefixEnd_662 := by
    exact prefixLift 662
  have htrace : WordTrace (prefixWord ++ tailWord_662) baseStart_662 baseEnd_662 := by
    simpa [prefixWord, tailWord_662, baseEnd_662] using wordTrace_append hprefix tailTrace_662
  have hstable : (prefixWord ++ tailWord_662).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662).length < 2 ^ (prefixWord ++ tailWord_662).sum := by decide
  have hdescent : baseEnd_662 < baseStart_662 := by decide
  rcases family_descends (prefixWord ++ tailWord_662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674 : List Nat := [3, 3, 1, 5]
def baseStart_674 : Nat := 118140960795 + 674 * 2 ^ 59
def prefixEnd_674 : Nat := 4983230072969 + 3 ^ 40 * 674 * 2
def baseEnd_674 : Nat := 324089642711706439901

theorem tailTrace_674 : CollatzResearch.WordTrace tailWord_674 prefixEnd_674 324089642711706439901 := by
  unfold tailWord_674
  simp only [CollatzResearch.WordTrace]
  refine ⟨6145699891421988786269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16388533043791970096717 6145699891421988786269)
  ·
    refine ⟨2304637459283245794851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6145699891421988786269 2304637459283245794851)
    ·
      refine ⟨3456956188924868692277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2304637459283245794851 3456956188924868692277)
      ·
        refine ⟨324089642711706439901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3456956188924868692277 324089642711706439901)
        ·
          rfl

theorem cell_674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_674 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_674 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_674 prefixEnd_674 := by
    exact prefixLift 674
  have htrace : WordTrace (prefixWord ++ tailWord_674) baseStart_674 baseEnd_674 := by
    simpa [prefixWord, tailWord_674, baseEnd_674] using wordTrace_append hprefix tailTrace_674
  have hstable : (prefixWord ++ tailWord_674).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674).length < 2 ^ (prefixWord ++ tailWord_674).sum := by decide
  have hdescent : baseEnd_674 < baseStart_674 := by decide
  rcases family_descends (prefixWord ++ tailWord_674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678 : List Nat := [9]
def baseStart_678 : Nat := 118140960795 + 678 * 2 ^ 59
def prefixEnd_678 : Nat := 4983230072969 + 3 ^ 40 * 678 * 2
def baseEnd_678 : Nat := 96596451371861868323

theorem tailTrace_678 : CollatzResearch.WordTrace tailWord_678 prefixEnd_678 96596451371861868323 := by
  unfold tailWord_678
  simp only [CollatzResearch.WordTrace]
  refine ⟨96596451371861868323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 9 16485794367464425527125 96596451371861868323)
  ·
    rfl

theorem cell_678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_678 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_678 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_678 prefixEnd_678 := by
    exact prefixLift 678
  have htrace : WordTrace (prefixWord ++ tailWord_678) baseStart_678 baseEnd_678 := by
    simpa [prefixWord, tailWord_678, baseEnd_678] using wordTrace_append hprefix tailTrace_678
  have hstable : (prefixWord ++ tailWord_678).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678).length < 2 ^ (prefixWord ++ tailWord_678).sum := by decide
  have hdescent : baseEnd_678 < baseStart_678 := by decide
  rcases family_descends (prefixWord ++ tailWord_678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680 : List Nat := [2, 1, 7, 2]
def baseStart_680 : Nat := 118140960795 + 680 * 2 ^ 59
def prefixEnd_680 : Nat := 4983230072969 + 3 ^ 40 * 680 * 2
def baseEnd_680 : Nat := 326974713714197488435

theorem tailTrace_680 : CollatzResearch.WordTrace tailWord_680 prefixEnd_680 326974713714197488435 := by
  unfold tailWord_680
  simp only [CollatzResearch.WordTrace]
  refine ⟨12400818771975489931747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16534425029300653242329 12400818771975489931747)
  ·
    refine ⟨18601228157963234897621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12400818771975489931747 18601228157963234897621)
    ·
      refine ⟨435966284952263317913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 18601228157963234897621 435966284952263317913)
      ·
        refine ⟨326974713714197488435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435966284952263317913 326974713714197488435)
        ·
          rfl

theorem cell_680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_680 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_680 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_680 prefixEnd_680 := by
    exact prefixLift 680
  have htrace : WordTrace (prefixWord ++ tailWord_680) baseStart_680 baseEnd_680 := by
    simpa [prefixWord, tailWord_680, baseEnd_680] using wordTrace_append hprefix tailTrace_680
  have hstable : (prefixWord ++ tailWord_680).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680).length < 2 ^ (prefixWord ++ tailWord_680).sum := by decide
  have hdescent : baseEnd_680 < baseStart_680 := by decide
  rcases family_descends (prefixWord ++ tailWord_680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692 : List Nat := [2, 5, 4]
def baseStart_692 : Nat := 118140960795 + 692 * 2 ^ 59
def prefixEnd_692 : Nat := 4983230072969 + 3 ^ 40 * 692 * 2
def baseEnd_692 : Nat := 221829903812786390335

theorem tailTrace_692 : CollatzResearch.WordTrace tailWord_692 prefixEnd_692 221829903812786390335 := by
  unfold tailWord_692
  simp only [CollatzResearch.WordTrace]
  refine ⟨12619656750238514650165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16826209000318019533553 12619656750238514650165)
  ·
    refine ⟨1183092820334860748453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12619656750238514650165 1183092820334860748453)
    ·
      refine ⟨221829903812786390335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1183092820334860748453 221829903812786390335)
      ·
        rfl

theorem cell_692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_692 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_692 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_692 prefixEnd_692 := by
    exact prefixLift 692
  have htrace : WordTrace (prefixWord ++ tailWord_692) baseStart_692 baseEnd_692 := by
    simpa [prefixWord, tailWord_692, baseEnd_692] using wordTrace_append hprefix tailTrace_692
  have hstable : (prefixWord ++ tailWord_692).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692).length < 2 ^ (prefixWord ++ tailWord_692).sum := by decide
  have hdescent : baseEnd_692 < baseStart_692 := by decide
  rcases family_descends (prefixWord ++ tailWord_692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706 : List Nat := [3, 5, 1, 3]
def baseStart_706 : Nat := 118140960795 + 706 * 2 ^ 59
def prefixEnd_706 : Nat := 4983230072969 + 3 ^ 40 * 706 * 2
def baseEnd_706 : Nat := 339476688058325365415

theorem tailTrace_706 : CollatzResearch.WordTrace tailWord_706 prefixEnd_706 339476688058325365415 := by
  unfold tailWord_706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6437483862439355077493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17166623633171613539981 6437483862439355077493)
  ·
    refine ⟨603514112103689538515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6437483862439355077493 603514112103689538515)
    ·
      refine ⟨905271168155534307773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603514112103689538515 905271168155534307773)
      ·
        refine ⟨339476688058325365415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 905271168155534307773 339476688058325365415)
        ·
          rfl

theorem cell_706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_706 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_706 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_706 prefixEnd_706 := by
    exact prefixLift 706
  have htrace : WordTrace (prefixWord ++ tailWord_706) baseStart_706 baseEnd_706 := by
    simpa [prefixWord, tailWord_706, baseEnd_706] using wordTrace_append hprefix tailTrace_706
  have hstable : (prefixWord ++ tailWord_706).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706).length < 2 ^ (prefixWord ++ tailWord_706).sum := by decide
  have hdescent : baseEnd_706 < baseStart_706 := by decide
  rcases family_descends (prefixWord ++ tailWord_706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726 : List Nat := [5, 2, 1, 4]
def baseStart_726 : Nat := 118140960795 + 726 * 2 ^ 59
def prefixEnd_726 : Nat := 4983230072969 + 3 ^ 40 * 726 * 2
def baseEnd_726 : Nat := 349093591399962193861

theorem tailTrace_726 : CollatzResearch.WordTrace tailWord_726 prefixEnd_726 349093591399962193861 := by
  unfold tailWord_726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1654962211081302252377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17652930251533890692021 1654962211081302252377)
  ·
    refine ⟨1241221658310976689283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1654962211081302252377 1241221658310976689283)
    ·
      refine ⟨1861832487466465033925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1241221658310976689283 1861832487466465033925)
      ·
        refine ⟨349093591399962193861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1861832487466465033925 349093591399962193861)
        ·
          rfl

theorem cell_726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_726 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_726 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_726 prefixEnd_726 := by
    exact prefixLift 726
  have htrace : WordTrace (prefixWord ++ tailWord_726) baseStart_726 baseEnd_726 := by
    simpa [prefixWord, tailWord_726, baseEnd_726] using wordTrace_append hprefix tailTrace_726
  have hstable : (prefixWord ++ tailWord_726).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726).length < 2 ^ (prefixWord ++ tailWord_726).sum := by decide
  have hdescent : baseEnd_726 < baseStart_726 := by decide
  rcases family_descends (prefixWord ++ tailWord_726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733 : List Nat := [1, 4, 3, 4]
def baseStart_733 : Nat := 118140960795 + 733 * 2 ^ 59
def prefixEnd_733 : Nat := 4983230072969 + 3 ^ 40 * 733 * 2
def baseEnd_733 : Nat := 352459507569535083817

theorem tailTrace_733 : CollatzResearch.WordTrace tailWord_733 prefixEnd_733 352459507569535083817 := by
  unfold tailWord_733
  simp only [CollatzResearch.WordTrace]
  refine ⟨26734706351941031542853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17823137567960687695235 26734706351941031542853)
  ·
    refine ⟨5012757440988943414285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26734706351941031542853 5012757440988943414285)
    ·
      refine ⟨1879784040370853780357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5012757440988943414285 1879784040370853780357)
      ·
        refine ⟨352459507569535083817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1879784040370853780357 352459507569535083817)
        ·
          rfl

theorem cell_733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_733 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_733 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_733 prefixEnd_733 := by
    exact prefixLift 733
  have htrace : WordTrace (prefixWord ++ tailWord_733) baseStart_733 baseEnd_733 := by
    simpa [prefixWord, tailWord_733, baseEnd_733] using wordTrace_append hprefix tailTrace_733
  have hstable : (prefixWord ++ tailWord_733).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733).length < 2 ^ (prefixWord ++ tailWord_733).sum := by decide
  have hdescent : baseEnd_733 < baseStart_733 := by decide
  rcases family_descends (prefixWord ++ tailWord_733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734 : List Nat := [4, 6]
def baseStart_734 : Nat := 118140960795 + 734 * 2 ^ 59
def prefixEnd_734 : Nat := 4983230072969 + 3 ^ 40 * 734 * 2
def baseEnd_734 : Nat := 156862378994051966773

theorem tailTrace_734 : CollatzResearch.WordTrace tailWord_734 prefixEnd_734 156862378994051966773 := by
  unfold tailWord_734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3346397418539775291157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17847452898878801552837 3346397418539775291157)
  ·
    refine ⟨156862378994051966773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3346397418539775291157 156862378994051966773)
    ·
      rfl

theorem cell_734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_734 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_734 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_734 prefixEnd_734 := by
    exact prefixLift 734
  have htrace : WordTrace (prefixWord ++ tailWord_734) baseStart_734 baseEnd_734 := by
    simpa [prefixWord, tailWord_734, baseEnd_734] using wordTrace_append hprefix tailTrace_734
  have hstable : (prefixWord ++ tailWord_734).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734).length < 2 ^ (prefixWord ++ tailWord_734).sum := by decide
  have hdescent : baseEnd_734 < baseStart_734 := by decide
  rcases family_descends (prefixWord ++ tailWord_734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738 : List Nat := [3, 3, 5]
def baseStart_738 : Nat := 118140960795 + 738 * 2 ^ 59
def prefixEnd_738 : Nat := 4983230072969 + 3 ^ 40 * 738 * 2
def baseEnd_738 : Nat := 236575822269962860619

theorem tailTrace_738 : CollatzResearch.WordTrace tailWord_738 prefixEnd_738 236575822269962860619 := by
  unfold tailWord_738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6729267833456721368717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17944714222551256983245 6729267833456721368717)
  ·
    refine ⟨2523475437546270513269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6729267833456721368717 2523475437546270513269)
    ·
      refine ⟨236575822269962860619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2523475437546270513269 236575822269962860619)
      ·
        rfl

theorem cell_738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_738 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_738 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_738 prefixEnd_738 := by
    exact prefixLift 738
  have htrace : WordTrace (prefixWord ++ tailWord_738) baseStart_738 baseEnd_738 := by
    simpa [prefixWord, tailWord_738, baseEnd_738] using wordTrace_append hprefix tailTrace_738
  have hstable : (prefixWord ++ tailWord_738).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738).length < 2 ^ (prefixWord ++ tailWord_738).sum := by decide
  have hdescent : baseEnd_738 < baseStart_738 := by decide
  rcases family_descends (prefixWord ++ tailWord_738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742 : List Nat := [7]
def baseStart_742 : Nat := 118140960795 + 742 * 2 ^ 59
def prefixEnd_742 : Nat := 4983230072969 + 3 ^ 40 * 742 * 2
def baseEnd_742 : Nat := 422858801864618259695

theorem tailTrace_742 : CollatzResearch.WordTrace tailWord_742 prefixEnd_742 422858801864618259695 := by
  unfold tailWord_742
  simp only [CollatzResearch.WordTrace]
  refine ⟨422858801864618259695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 18041975546223712413653 422858801864618259695)
  ·
    rfl

theorem cell_742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_742 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_742 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_742 prefixEnd_742 := by
    exact prefixLift 742
  have htrace : WordTrace (prefixWord ++ tailWord_742) baseStart_742 baseEnd_742 := by
    simpa [prefixWord, tailWord_742, baseEnd_742] using wordTrace_append hprefix tailTrace_742
  have hstable : (prefixWord ++ tailWord_742).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742).length < 2 ^ (prefixWord ++ tailWord_742).sum := by decide
  have hdescent : baseEnd_742 < baseStart_742 := by decide
  rcases family_descends (prefixWord ++ tailWord_742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790 : List Nat := [5, 4]
def baseStart_790 : Nat := 118140960795 + 790 * 2 ^ 59
def prefixEnd_790 : Nat := 4983230072969 + 3 ^ 40 * 790 * 2
def baseEnd_790 : Nat := 337660161860622262123

theorem tailTrace_790 : CollatzResearch.WordTrace tailWord_790 prefixEnd_790 337660161860622262123 := by
  unfold tailWord_790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1800854196589985397989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19209111430293177578549 1800854196589985397989)
  ·
    refine ⟨337660161860622262123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1800854196589985397989 337660161860622262123)
    ·
      rfl

theorem cell_790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_790 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_790 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_790 prefixEnd_790 := by
    exact prefixLift 790
  have htrace : WordTrace (prefixWord ++ tailWord_790) baseStart_790 baseEnd_790 := by
    simpa [prefixWord, tailWord_790, baseEnd_790] using wordTrace_append hprefix tailTrace_790
  have hstable : (prefixWord ++ tailWord_790).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790).length < 2 ^ (prefixWord ++ tailWord_790).sum := by decide
  have hdescent : baseEnd_790 < baseStart_790 := by decide
  rcases family_descends (prefixWord ++ tailWord_790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798 : List Nat := [4, 3, 2, 3]
def baseStart_798 : Nat := 118140960795 + 798 * 2 ^ 59
def prefixEnd_798 : Nat := 4983230072969 + 3 ^ 40 * 798 * 2
def baseEnd_798 : Nat := 383714443429854776267

theorem tailTrace_798 : CollatzResearch.WordTrace tailWord_798 prefixEnd_798 383714443429854776267 := by
  unfold tailWord_798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3638181389557141582381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19403634077638088439365 3638181389557141582381)
  ·
    refine ⟨1364318021083928093393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3638181389557141582381 1364318021083928093393)
    ·
      refine ⟨1023238515812946070045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1364318021083928093393 1023238515812946070045)
      ·
        refine ⟨383714443429854776267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1023238515812946070045 383714443429854776267)
        ·
          rfl

theorem cell_798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_798 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_798 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_798 prefixEnd_798 := by
    exact prefixLift 798
  have htrace : WordTrace (prefixWord ++ tailWord_798) baseStart_798 baseEnd_798 := by
    simpa [prefixWord, tailWord_798, baseEnd_798] using wordTrace_append hprefix tailTrace_798
  have hstable : (prefixWord ++ tailWord_798).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798).length < 2 ^ (prefixWord ++ tailWord_798).sum := by decide
  have hdescent : baseEnd_798 < baseStart_798 := by decide
  rcases family_descends (prefixWord ++ tailWord_798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806 : List Nat := [8]
def baseStart_806 : Nat := 118140960795 + 806 * 2 ^ 59
def prefixEnd_806 : Nat := 4983230072969 + 3 ^ 40 * 806 * 2
def baseEnd_806 : Nat := 229665899120894523049

theorem tailTrace_806 : CollatzResearch.WordTrace tailWord_806 prefixEnd_806 229665899120894523049 := by
  unfold tailWord_806
  simp only [CollatzResearch.WordTrace]
  refine ⟨229665899120894523049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 19598156724982999300181 229665899120894523049)
  ·
    rfl

theorem cell_806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_806 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_806 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_806 prefixEnd_806 := by
    exact prefixLift 806
  have htrace : WordTrace (prefixWord ++ tailWord_806) baseStart_806 baseEnd_806 := by
    simpa [prefixWord, tailWord_806, baseEnd_806] using wordTrace_append hprefix tailTrace_806
  have hstable : (prefixWord ++ tailWord_806).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806).length < 2 ^ (prefixWord ++ tailWord_806).sum := by decide
  have hdescent : baseEnd_806 < baseStart_806 := by decide
  rcases family_descends (prefixWord ++ tailWord_806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807 : List Nat := [1, 1, 9]
def baseStart_807 : Nat := 118140960795 + 807 * 2 ^ 59
def prefixEnd_807 : Nat := 4983230072969 + 3 ^ 40 * 807 * 2
def baseEnd_807 : Nat := 258694699955727566045

theorem tailTrace_807 : CollatzResearch.WordTrace tailWord_807 prefixEnd_807 258694699955727566045 := by
  unfold tailWord_807
  simp only [CollatzResearch.WordTrace]
  refine ⟨29433708083851669736675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19622472055901113157783 29433708083851669736675)
  ·
    refine ⟨44150562125777504605013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29433708083851669736675 44150562125777504605013)
    ·
      refine ⟨258694699955727566045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 9 44150562125777504605013 258694699955727566045)
      ·
        rfl

theorem cell_807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_807 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_807 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_807 prefixEnd_807 := by
    exact prefixLift 807
  have htrace : WordTrace (prefixWord ++ tailWord_807) baseStart_807 baseEnd_807 := by
    simpa [prefixWord, tailWord_807, baseEnd_807] using wordTrace_append hprefix tailTrace_807
  have hstable : (prefixWord ++ tailWord_807).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807).length < 2 ^ (prefixWord ++ tailWord_807).sum := by decide
  have hdescent : baseEnd_807 < baseStart_807 := by decide
  rcases family_descends (prefixWord ++ tailWord_807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825 : List Nat := [1, 2, 1, 8]
def baseStart_825 : Nat := 118140960795 + 825 * 2 ^ 59
def prefixEnd_825 : Nat := 4983230072969 + 3 ^ 40 * 825 * 2
def baseEnd_825 : Nat := 396697262941064494669

theorem tailTrace_825 : CollatzResearch.WordTrace tailWord_825 prefixEnd_825 396697262941064494669 := by
  unfold tailWord_825
  simp only [CollatzResearch.WordTrace]
  refine ⟨30090222018640743891929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20060148012427162594619 30090222018640743891929)
  ·
    refine ⟨22567666513980557918947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30090222018640743891929 22567666513980557918947)
    ·
      refine ⟨33851499770970836878421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22567666513980557918947 33851499770970836878421)
      ·
        refine ⟨396697262941064494669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 33851499770970836878421 396697262941064494669)
        ·
          rfl

theorem cell_825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_825 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_825 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_825 prefixEnd_825 := by
    exact prefixLift 825
  have htrace : WordTrace (prefixWord ++ tailWord_825) baseStart_825 baseEnd_825 := by
    simpa [prefixWord, tailWord_825, baseEnd_825] using wordTrace_append hprefix tailTrace_825
  have hstable : (prefixWord ++ tailWord_825).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825).length < 2 ^ (prefixWord ++ tailWord_825).sum := by decide
  have hdescent : baseEnd_825 < baseStart_825 := by decide
  rcases family_descends (prefixWord ++ tailWord_825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834 : List Nat := [3, 7]
def baseStart_834 : Nat := 118140960795 + 834 * 2 ^ 59
def prefixEnd_834 : Nat := 4983230072969 + 3 ^ 40 * 834 * 2
def baseEnd_834 : Nat := 178233275308800474431

theorem tailTrace_834 : CollatzResearch.WordTrace tailWord_834 prefixEnd_834 178233275308800474431 := by
  unfold tailWord_834
  simp only [CollatzResearch.WordTrace]
  refine ⟨7604619746508820242389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20278985990690187313037 7604619746508820242389)
  ·
    refine ⟨178233275308800474431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 7604619746508820242389 178233275308800474431)
    ·
      rfl

theorem cell_834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_834 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_834 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_834 prefixEnd_834 := by
    exact prefixLift 834
  have htrace : WordTrace (prefixWord ++ tailWord_834) baseStart_834 baseEnd_834 := by
    simpa [prefixWord, tailWord_834, baseEnd_834] using wordTrace_append hprefix tailTrace_834
  have hstable : (prefixWord ++ tailWord_834).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834).length < 2 ^ (prefixWord ++ tailWord_834).sum := by decide
  have hdescent : baseEnd_834 < baseStart_834 := by decide
  rcases family_descends (prefixWord ++ tailWord_834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862 : List Nat := [4, 4, 3]
def baseStart_862 : Nat := 118140960795 + 862 * 2 ^ 59
def prefixEnd_862 : Nat := 4983230072969 + 3 ^ 40 * 862 * 2
def baseEnd_862 : Nat := 276325689415395084863

theorem tailTrace_862 : CollatzResearch.WordTrace tailWord_862 prefixEnd_862 276325689415395084863 := by
  unfold tailWord_862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3929965360574507873605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20959815256397375325893 3929965360574507873605)
  ·
    refine ⟨736868505107720226301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3929965360574507873605 736868505107720226301)
    ·
      refine ⟨276325689415395084863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 736868505107720226301 276325689415395084863)
      ·
        rfl

theorem cell_862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_862 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_862 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_862 prefixEnd_862 := by
    exact prefixLift 862
  have htrace : WordTrace (prefixWord ++ tailWord_862) baseStart_862 baseEnd_862 := by
    simpa [prefixWord, tailWord_862, baseEnd_862] using wordTrace_append hprefix tailTrace_862
  have hstable : (prefixWord ++ tailWord_862).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862).length < 2 ^ (prefixWord ++ tailWord_862).sum := by decide
  have hdescent : baseEnd_862 < baseStart_862 := by decide
  rcases family_descends (prefixWord ++ tailWord_862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870 : List Nat := [7]
def baseStart_870 : Nat := 118140960795 + 870 * 2 ^ 59
def prefixEnd_870 : Nat := 4983230072969 + 3 ^ 40 * 870 * 2
def baseEnd_870 : Nat := 495804794618959832501

theorem tailTrace_870 : CollatzResearch.WordTrace tailWord_870 prefixEnd_870 495804794618959832501 := by
  unfold tailWord_870
  simp only [CollatzResearch.WordTrace]
  refine ⟨495804794618959832501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 21154337903742286186709 495804794618959832501)
  ·
    rfl

theorem cell_870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_870 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_870 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_870 prefixEnd_870 := by
    exact prefixLift 870
  have htrace : WordTrace (prefixWord ++ tailWord_870) baseStart_870 baseEnd_870 := by
    simpa [prefixWord, tailWord_870, baseEnd_870] using wordTrace_append hprefix tailTrace_870
  have hstable : (prefixWord ++ tailWord_870).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870).length < 2 ^ (prefixWord ++ tailWord_870).sum := by decide
  have hdescent : baseEnd_870 < baseStart_870 := by decide
  rcases family_descends (prefixWord ++ tailWord_870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884 : List Nat := [2, 10]
def baseStart_884 : Nat := 118140960795 + 884 * 2 ^ 59
def prefixEnd_884 : Nat := 4983230072969 + 3 ^ 40 * 884 * 2
def baseEnd_884 : Nat := 47229680866543682065

theorem tailTrace_884 : CollatzResearch.WordTrace tailWord_884 prefixEnd_884 47229680866543682065 := by
  unfold tailWord_884
  simp only [CollatzResearch.WordTrace]
  refine ⟨16121064402446910144853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21494752536595880193137 16121064402446910144853)
  ·
    refine ⟨47229680866543682065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 10 16121064402446910144853 47229680866543682065)
    ·
      rfl

theorem cell_884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_884 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_884 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_884 prefixEnd_884 := by
    exact prefixLift 884
  have htrace : WordTrace (prefixWord ++ tailWord_884) baseStart_884 baseEnd_884 := by
    simpa [prefixWord, tailWord_884, baseEnd_884] using wordTrace_append hprefix tailTrace_884
  have hstable : (prefixWord ++ tailWord_884).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884).length < 2 ^ (prefixWord ++ tailWord_884).sum := by decide
  have hdescent : baseEnd_884 < baseStart_884 := by decide
  rcases family_descends (prefixWord ++ tailWord_884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897 : List Nat := [1, 2, 4, 5]
def baseStart_897 : Nat := 118140960795 + 897 * 2 ^ 59
def prefixEnd_897 : Nat := 4983230072969 + 3 ^ 40 * 897 * 2
def baseEnd_897 : Nat := 431318114970957077075

theorem tailTrace_897 : CollatzResearch.WordTrace tailWord_897 prefixEnd_897 431318114970957077075 := by
  unfold tailWord_897
  simp only [CollatzResearch.WordTrace]
  refine ⟨32716277757797040512945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21810851838531360341963 32716277757797040512945)
  ·
    refine ⟨24537208318347780384709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32716277757797040512945 24537208318347780384709)
    ·
      refine ⟨4600726559690208822133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24537208318347780384709 4600726559690208822133)
      ·
        refine ⟨431318114970957077075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4600726559690208822133 431318114970957077075)
        ·
          rfl

theorem cell_897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_897 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_897 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_897 prefixEnd_897 := by
    exact prefixLift 897
  have htrace : WordTrace (prefixWord ++ tailWord_897) baseStart_897 baseEnd_897 := by
    simpa [prefixWord, tailWord_897, baseEnd_897] using wordTrace_append hprefix tailTrace_897
  have hstable : (prefixWord ++ tailWord_897).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897).length < 2 ^ (prefixWord ++ tailWord_897).sum := by decide
  have hdescent : baseEnd_897 < baseStart_897 := by decide
  rcases family_descends (prefixWord ++ tailWord_897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902 : List Nat := [6, 3]
def baseStart_902 : Nat := 118140960795 + 902 * 2 ^ 59
def prefixEnd_902 : Nat := 4983230072969 + 3 ^ 40 * 902 * 2
def baseEnd_902 : Nat := 385530969605658919277

theorem tailTrace_902 : CollatzResearch.WordTrace tailWord_902 prefixEnd_902 385530969605658919277 := by
  unfold tailWord_902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028082585615090451405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21932428493121929629973 1028082585615090451405)
  ·
    refine ⟨385530969605658919277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1028082585615090451405 385530969605658919277)
    ·
      rfl

theorem cell_902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_902 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_902 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_902 prefixEnd_902 := by
    exact prefixLift 902
  have htrace : WordTrace (prefixWord ++ tailWord_902) baseStart_902 baseEnd_902 := by
    simpa [prefixWord, tailWord_902, baseEnd_902] using wordTrace_append hprefix tailTrace_902
  have hstable : (prefixWord ++ tailWord_902).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902).length < 2 ^ (prefixWord ++ tailWord_902).sum := by decide
  have hdescent : baseEnd_902 < baseStart_902 := by decide
  rcases family_descends (prefixWord ++ tailWord_902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909 : List Nat := [1, 8]
def baseStart_909 : Nat := 118140960795 + 909 * 2 ^ 59
def prefixEnd_909 : Nat := 4983230072969 + 3 ^ 40 * 909 * 2
def baseEnd_909 : Nat := 388522895089723710349

theorem tailTrace_909 : CollatzResearch.WordTrace tailWord_909 prefixEnd_909 388522895089723710349 := by
  unfold tailWord_909
  simp only [CollatzResearch.WordTrace]
  refine ⟨33153953714323089949781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22102635809548726633187 33153953714323089949781)
  ·
    refine ⟨388522895089723710349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 33153953714323089949781 388522895089723710349)
    ·
      rfl

theorem cell_909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_909 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_909 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_909 prefixEnd_909 := by
    exact prefixLift 909
  have htrace : WordTrace (prefixWord ++ tailWord_909) baseStart_909 baseEnd_909 := by
    simpa [prefixWord, tailWord_909, baseEnd_909] using wordTrace_append hprefix tailTrace_909
  have hstable : (prefixWord ++ tailWord_909).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909).length < 2 ^ (prefixWord ++ tailWord_909).sum := by decide
  have hdescent : baseEnd_909 < baseStart_909 := by decide
  rcases family_descends (prefixWord ++ tailWord_909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910 : List Nat := [4, 1, 1, 6]
def baseStart_910 : Nat := 118140960795 + 910 * 2 ^ 59
def prefixEnd_910 : Nat := 4983230072969 + 3 ^ 40 * 910 * 2
def baseEnd_910 : Nat := 437569102143021015565

theorem tailTrace_910 : CollatzResearch.WordTrace tailWord_910 prefixEnd_910 437569102143021015565 := by
  unfold tailWord_910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4148803338837532592023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22126951140466840490789 4148803338837532592023)
  ·
    refine ⟨6223205008256298888035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4148803338837532592023 6223205008256298888035)
    ·
      refine ⟨9334807512384448332053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6223205008256298888035 9334807512384448332053)
      ·
        refine ⟨437569102143021015565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9334807512384448332053 437569102143021015565)
        ·
          rfl

theorem cell_910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_910 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_910 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_910 prefixEnd_910 := by
    exact prefixLift 910
  have htrace : WordTrace (prefixWord ++ tailWord_910) baseStart_910 baseEnd_910 := by
    simpa [prefixWord, tailWord_910, baseEnd_910] using wordTrace_append hprefix tailTrace_910
  have hstable : (prefixWord ++ tailWord_910).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910).length < 2 ^ (prefixWord ++ tailWord_910).sum := by decide
  have hdescent : baseEnd_910 < baseStart_910 := by decide
  rcases family_descends (prefixWord ++ tailWord_910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934 : List Nat := [10]
def baseStart_934 : Nat := 118140960795 + 934 * 2 ^ 59
def prefixEnd_934 : Nat := 4983230072969 + 3 ^ 40 * 934 * 2
def baseEnd_934 : Nat := 66534723874516327363

theorem tailTrace_934 : CollatzResearch.WordTrace tailWord_934 prefixEnd_934 66534723874516327363 := by
  unfold tailWord_934
  simp only [CollatzResearch.WordTrace]
  refine ⟨66534723874516327363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 10 22710519082501573073237 66534723874516327363)
  ·
    rfl

theorem cell_934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_934 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_934 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_934 prefixEnd_934 := by
    exact prefixLift 934
  have htrace : WordTrace (prefixWord ++ tailWord_934) baseStart_934 baseEnd_934 := by
    simpa [prefixWord, tailWord_934, baseEnd_934] using wordTrace_append hprefix tailTrace_934
  have hstable : (prefixWord ++ tailWord_934).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934).length < 2 ^ (prefixWord ++ tailWord_934).sum := by decide
  have hdescent : baseEnd_934 < baseStart_934 := by decide
  rcases family_descends (prefixWord ++ tailWord_934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936 : List Nat := [2, 1, 6, 3]
def baseStart_936 : Nat := 118140960795 + 936 * 2 ^ 59
def prefixEnd_936 : Nat := 4983230072969 + 3 ^ 40 * 936 * 2
def baseEnd_936 : Nat := 450071076487148892545

theorem tailTrace_936 : CollatzResearch.WordTrace tailWord_936 prefixEnd_936 450071076487148892545 := by
  unfold tailWord_936
  simp only [CollatzResearch.WordTrace]
  refine ⟨17069362308253350591331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22759149744337800788441 17069362308253350591331)
  ·
    refine ⟨25604043462380025886997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17069362308253350591331 25604043462380025886997)
    ·
      refine ⟨1200189537299063713453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25604043462380025886997 1200189537299063713453)
      ·
        refine ⟨450071076487148892545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1200189537299063713453 450071076487148892545)
        ·
          rfl

theorem cell_936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_936 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_936 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_936 prefixEnd_936 := by
    exact prefixLift 936
  have htrace : WordTrace (prefixWord ++ tailWord_936) baseStart_936 baseEnd_936 := by
    simpa [prefixWord, tailWord_936, baseEnd_936] using wordTrace_append hprefix tailTrace_936
  have hstable : (prefixWord ++ tailWord_936).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936).length < 2 ^ (prefixWord ++ tailWord_936).sum := by decide
  have hdescent : baseEnd_936 < baseStart_936 := by decide
  rcases family_descends (prefixWord ++ tailWord_936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938 : List Nat := [3, 1, 7]
def baseStart_938 : Nat := 118140960795 + 938 * 2 ^ 59
def prefixEnd_938 : Nat := 4983230072969 + 3 ^ 40 * 938 * 2
def baseEnd_938 : Nat := 300688511214208383593

theorem tailTrace_938 : CollatzResearch.WordTrace tailWord_938 prefixEnd_938 300688511214208383593 := by
  unfold tailWord_938
  simp only [CollatzResearch.WordTrace]
  refine ⟨8552917652315260688867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22807780406174028503645 8552917652315260688867)
  ·
    refine ⟨12829376478472891033301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8552917652315260688867 12829376478472891033301)
    ·
      refine ⟨300688511214208383593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 12829376478472891033301 300688511214208383593)
      ·
        rfl

theorem cell_938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_938 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_938 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_938 prefixEnd_938 := by
    exact prefixLift 938
  have htrace : WordTrace (prefixWord ++ tailWord_938) baseStart_938 baseEnd_938 := by
    simpa [prefixWord, tailWord_938, baseEnd_938] using wordTrace_append hprefix tailTrace_938
  have hstable : (prefixWord ++ tailWord_938).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938).length < 2 ^ (prefixWord ++ tailWord_938).sum := by decide
  have hdescent : baseEnd_938 < baseStart_938 := by decide
  rcases family_descends (prefixWord ++ tailWord_938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942 : List Nat := [4, 1, 5, 2]
def baseStart_942 : Nat := 118140960795 + 942 * 2 ^ 59
def prefixEnd_942 : Nat := 4983230072969 + 3 ^ 40 * 942 * 2
def baseEnd_942 : Nat := 452956147489639941079

theorem tailTrace_942 : CollatzResearch.WordTrace tailWord_942 prefixEnd_942 452956147489639941079 := by
  unfold tailWord_942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294695324346215737635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22905041729846483934053 4294695324346215737635)
  ·
    refine ⟨6442042986519323606453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4294695324346215737635 6442042986519323606453)
    ·
      refine ⟨603941529986186588105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6442042986519323606453 603941529986186588105)
      ·
        refine ⟨452956147489639941079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 603941529986186588105 452956147489639941079)
        ·
          rfl

theorem cell_942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_942 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_942 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_942 prefixEnd_942 := by
    exact prefixLift 942
  have htrace : WordTrace (prefixWord ++ tailWord_942) baseStart_942 baseEnd_942 := by
    simpa [prefixWord, tailWord_942, baseEnd_942] using wordTrace_append hprefix tailTrace_942
  have hstable : (prefixWord ++ tailWord_942).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942).length < 2 ^ (prefixWord ++ tailWord_942).sum := by decide
  have hdescent : baseEnd_942 < baseStart_942 := by decide
  rcases family_descends (prefixWord ++ tailWord_942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956 : List Nat := [2, 2, 2, 6]
def baseStart_956 : Nat := 118140960795 + 956 * 2 ^ 59
def prefixEnd_956 : Nat := 4983230072969 + 3 ^ 40 * 956 * 2
def baseEnd_956 : Nat := 459687979828785720991

theorem tailTrace_956 : CollatzResearch.WordTrace tailWord_956 prefixEnd_956 459687979828785720991 := by
  unfold tailWord_956
  simp only [CollatzResearch.WordTrace]
  refine ⟨17434092272025058455361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23245456362700077940481 17434092272025058455361)
  ·
    refine ⟨13075569204018793841521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17434092272025058455361 13075569204018793841521)
    ·
      refine ⟨9806676903014095381141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13075569204018793841521 9806676903014095381141)
      ·
        refine ⟨459687979828785720991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9806676903014095381141 459687979828785720991)
        ·
          rfl

theorem cell_956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_956 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_956 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_956 prefixEnd_956 := by
    exact prefixLift 956
  have htrace : WordTrace (prefixWord ++ tailWord_956) baseStart_956 baseEnd_956 := by
    simpa [prefixWord, tailWord_956, baseEnd_956] using wordTrace_append hprefix tailTrace_956
  have hstable : (prefixWord ++ tailWord_956).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956).length < 2 ^ (prefixWord ++ tailWord_956).sum := by decide
  have hdescent : baseEnd_956 < baseStart_956 := by decide
  rcases family_descends (prefixWord ++ tailWord_956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961 : List Nat := [1, 2, 8]
def baseStart_961 : Nat := 118140960795 + 961 * 2 ^ 59
def prefixEnd_961 : Nat := 4983230072969 + 3 ^ 40 * 961 * 2
def baseEnd_961 : Nat := 308061470442796618735

theorem tailTrace_961 : CollatzResearch.WordTrace tailWord_961 prefixEnd_961 308061470442796618735 := by
  unfold tailWord_961
  simp only [CollatzResearch.WordTrace]
  refine ⟨35050549525935970842737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23367033017290647228491 35050549525935970842737)
  ·
    refine ⟨26287912144451978132053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35050549525935970842737 26287912144451978132053)
    ·
      refine ⟨308061470442796618735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 26287912144451978132053 308061470442796618735)
      ·
        rfl

theorem cell_961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_961 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_961 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_961 prefixEnd_961 := by
    exact prefixLift 961
  have htrace : WordTrace (prefixWord ++ tailWord_961) baseStart_961 baseEnd_961 := by
    simpa [prefixWord, tailWord_961, baseEnd_961] using wordTrace_append hprefix tailTrace_961
  have hstable : (prefixWord ++ tailWord_961).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961).length < 2 ^ (prefixWord ++ tailWord_961).sum := by decide
  have hdescent : baseEnd_961 < baseStart_961 := by decide
  rcases family_descends (prefixWord ++ tailWord_961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962 : List Nat := [3, 5, 4]
def baseStart_962 : Nat := 118140960795 + 962 * 2 ^ 59
def prefixEnd_962 : Nat := 4983230072969 + 3 ^ 40 * 962 * 2
def baseEnd_962 : Nat := 154191016943758923175

theorem tailTrace_962 : CollatzResearch.WordTrace tailWord_962 prefixEnd_962 154191016943758923175 := by
  unfold tailWord_962
  simp only [CollatzResearch.WordTrace]
  refine ⟨8771755630578285407285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23391348348208761086093 8771755630578285407285)
  ·
    refine ⟨822352090366714256933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8771755630578285407285 822352090366714256933)
    ·
      refine ⟨154191016943758923175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 822352090366714256933 154191016943758923175)
      ·
        rfl

theorem cell_962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_962 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_962 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_962 prefixEnd_962 := by
    exact prefixLift 962
  have htrace : WordTrace (prefixWord ++ tailWord_962) baseStart_962 baseEnd_962 := by
    simpa [prefixWord, tailWord_962, baseEnd_962] using wordTrace_append hprefix tailTrace_962
  have hstable : (prefixWord ++ tailWord_962).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962).length < 2 ^ (prefixWord ++ tailWord_962).sum := by decide
  have hdescent : baseEnd_962 < baseStart_962 := by decide
  rcases family_descends (prefixWord ++ tailWord_962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988 : List Nat := [2, 2, 6, 2]
def baseStart_988 : Nat := 118140960795 + 988 * 2 ^ 59
def prefixEnd_988 : Nat := 4983230072969 + 3 ^ 40 * 988 * 2
def baseEnd_988 : Nat := 475075025175404646505

theorem tailTrace_988 : CollatzResearch.WordTrace tailWord_988 prefixEnd_988 475075025175404646505 := by
  unfold tailWord_988
  simp only [CollatzResearch.WordTrace]
  refine ⟨18017660214059791037809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24023546952079721383745 18017660214059791037809)
  ·
    refine ⟨13513245160544843278357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18017660214059791037809 13513245160544843278357)
    ·
      refine ⟨633433366900539528673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13513245160544843278357 633433366900539528673)
      ·
        refine ⟨475075025175404646505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633433366900539528673 475075025175404646505)
        ·
          rfl

theorem cell_988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_988 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_988 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_988 prefixEnd_988 := by
    exact prefixLift 988
  have htrace : WordTrace (prefixWord ++ tailWord_988) baseStart_988 baseEnd_988 := by
    simpa [prefixWord, tailWord_988, baseEnd_988] using wordTrace_append hprefix tailTrace_988
  have hstable : (prefixWord ++ tailWord_988).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988).length < 2 ^ (prefixWord ++ tailWord_988).sum := by decide
  have hdescent : baseEnd_988 < baseStart_988 := by decide
  rcases family_descends (prefixWord ++ tailWord_988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990 : List Nat := [4, 5]
def baseStart_990 : Nat := 118140960795 + 990 * 2 ^ 59
def prefixEnd_990 : Nat := 4983230072969 + 3 ^ 40 * 990 * 2
def baseEnd_990 : Nat := 423143747119616292755

theorem tailTrace_990 : CollatzResearch.WordTrace tailWord_990 prefixEnd_990 423143747119616292755 := by
  unfold tailWord_990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4513533302609240456053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24072177613915949098949 4513533302609240456053)
  ·
    refine ⟨423143747119616292755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4513533302609240456053 423143747119616292755)
    ·
      rfl

theorem cell_990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_990 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_990 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_990 prefixEnd_990 := by
    exact prefixLift 990
  have htrace : WordTrace (prefixWord ++ tailWord_990) baseStart_990 baseEnd_990 := by
    simpa [prefixWord, tailWord_990, baseEnd_990] using wordTrace_append hprefix tailTrace_990
  have hstable : (prefixWord ++ tailWord_990).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990).length < 2 ^ (prefixWord ++ tailWord_990).sum := by decide
  have hdescent : baseEnd_990 < baseStart_990 := by decide
  rcases family_descends (prefixWord ++ tailWord_990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_998 : List Nat := [7]
def baseStart_998 : Nat := 118140960795 + 998 * 2 ^ 59
def prefixEnd_998 : Nat := 4983230072969 + 3 ^ 40 * 998 * 2
def baseEnd_998 : Nat := 568750787373301405307

theorem tailTrace_998 : CollatzResearch.WordTrace tailWord_998 prefixEnd_998 568750787373301405307 := by
  unfold tailWord_998
  simp only [CollatzResearch.WordTrace]
  refine ⟨568750787373301405307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 24266700261260859959765 568750787373301405307)
  ·
    rfl

theorem cell_998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_998 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_998 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_998 prefixEnd_998 := by
    exact prefixLift 998
  have htrace : WordTrace (prefixWord ++ tailWord_998) baseStart_998 baseEnd_998 := by
    simpa [prefixWord, tailWord_998, baseEnd_998] using wordTrace_append hprefix tailTrace_998
  have hstable : (prefixWord ++ tailWord_998).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_998).length < 2 ^ (prefixWord ++ tailWord_998).sum := by decide
  have hdescent : baseEnd_998 < baseStart_998 := by decide
  rcases family_descends (prefixWord ++ tailWord_998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1028 : List Nat := [2, 3, 2, 5]
def baseStart_1028 : Nat := 118140960795 + 1028 * 2 ^ 59
def prefixEnd_1028 : Nat := 4983230072969 + 3 ^ 40 * 1028 * 2
def baseEnd_1028 : Nat := 494308831858678303397

theorem tailTrace_1028 : CollatzResearch.WordTrace tailWord_1028 prefixEnd_1028 494308831858678303397 := by
  unfold tailWord_1028
  simp only [CollatzResearch.WordTrace]
  refine ⟨18747120141603206765869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24996160188804275687825 18747120141603206765869)
  ·
    refine ⟨7030170053101202537201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18747120141603206765869 7030170053101202537201)
    ·
      refine ⟨5272627539825901902901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7030170053101202537201 5272627539825901902901)
      ·
        refine ⟨494308831858678303397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5272627539825901902901 494308831858678303397)
        ·
          rfl

theorem cell_1028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_1028 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1028 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1028 prefixEnd_1028 := by
    exact prefixLift 1028
  have htrace : WordTrace (prefixWord ++ tailWord_1028) baseStart_1028 baseEnd_1028 := by
    simpa [prefixWord, tailWord_1028, baseEnd_1028] using wordTrace_append hprefix tailTrace_1028
  have hstable : (prefixWord ++ tailWord_1028).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1028).length < 2 ^ (prefixWord ++ tailWord_1028).sum := by decide
  have hdescent : baseEnd_1028 < baseStart_1028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046 : List Nat := [5, 6]
def baseStart_1046 : Nat := 118140960795 + 1046 * 2 ^ 59
def prefixEnd_1046 : Nat := 4983230072969 + 3 ^ 40 * 1046 * 2
def baseEnd_1046 : Nat := 111769787748033655333

theorem tailTrace_1046 : CollatzResearch.WordTrace tailWord_1046 prefixEnd_1046 111769787748033655333 := by
  unfold tailWord_1046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2384422138624717980437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25433836145330325124661 2384422138624717980437)
  ·
    refine ⟨111769787748033655333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2384422138624717980437 111769787748033655333)
    ·
      rfl

theorem cell_1046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_1046 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1046 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1046 prefixEnd_1046 := by
    exact prefixLift 1046
  have htrace : WordTrace (prefixWord ++ tailWord_1046) baseStart_1046 baseEnd_1046 := by
    simpa [prefixWord, tailWord_1046, baseEnd_1046] using wordTrace_append hprefix tailTrace_1046
  have hstable : (prefixWord ++ tailWord_1046).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046).length < 2 ^ (prefixWord ++ tailWord_1046).sum := by decide
  have hdescent : baseEnd_1046 < baseStart_1046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054 : List Nat := [4, 3, 5]
def baseStart_1054 : Nat := 118140960795 + 1054 * 2 ^ 59
def prefixEnd_1054 : Nat := 4983230072969 + 3 ^ 40 * 1054 * 2
def baseEnd_1054 : Nat := 168936935400935393459

theorem tailTrace_1054 : CollatzResearch.WordTrace tailWord_1054 prefixEnd_1054 168936935400935393459 := by
  unfold tailWord_1054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4805317273626606747277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25628358792675235985477 4805317273626606747277)
  ·
    refine ⟨1801993977609977530229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4805317273626606747277 1801993977609977530229)
    ·
      refine ⟨168936935400935393459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1801993977609977530229 168936935400935393459)
      ·
        rfl

theorem cell_1054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_1054 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1054 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1054 prefixEnd_1054 := by
    exact prefixLift 1054
  have htrace : WordTrace (prefixWord ++ tailWord_1054) baseStart_1054 baseEnd_1054 := by
    simpa [prefixWord, tailWord_1054, baseEnd_1054] using wordTrace_append hprefix tailTrace_1054
  have hstable : (prefixWord ++ tailWord_1054).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054).length < 2 ^ (prefixWord ++ tailWord_1054).sum := by decide
  have hdescent : baseEnd_1054 < baseStart_1054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062 : List Nat := [8]
def baseStart_1062 : Nat := 118140960795 + 1062 * 2 ^ 59
def prefixEnd_1062 : Nat := 4983230072969 + 3 ^ 40 * 1062 * 2
def baseEnd_1062 : Nat := 302611891875236095855

theorem tailTrace_1062 : CollatzResearch.WordTrace tailWord_1062 prefixEnd_1062 302611891875236095855 := by
  unfold tailWord_1062
  simp only [CollatzResearch.WordTrace]
  refine ⟨302611891875236095855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 25822881440020146846293 302611891875236095855)
  ·
    rfl

theorem cell_1062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1062 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1062 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1062 prefixEnd_1062 := by
    exact prefixLift 1062
  have htrace : WordTrace (prefixWord ++ tailWord_1062) baseStart_1062 baseEnd_1062 := by
    simpa [prefixWord, tailWord_1062, baseEnd_1062] using wordTrace_append hprefix tailTrace_1062
  have hstable : (prefixWord ++ tailWord_1062).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062).length < 2 ^ (prefixWord ++ tailWord_1062).sum := by decide
  have hdescent : baseEnd_1062 < baseStart_1062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069 : List Nat := [1, 5, 5]
def baseStart_1069 : Nat := 118140960795 + 1069 * 2 ^ 59
def prefixEnd_1069 : Nat := 4983230072969 + 3 ^ 40 * 1069 * 2
def baseEnd_1069 : Nat := 342682322472689201141

theorem tailTrace_1069 : CollatzResearch.WordTrace tailWord_1069 prefixEnd_1069 342682322472689201141 := by
  unfold tailWord_1069
  simp only [CollatzResearch.WordTrace]
  refine ⟨38989633134670415774261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25993088756446943849507 38989633134670415774261)
  ·
    refine ⟨3655278106375351478837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38989633134670415774261 3655278106375351478837)
    ·
      refine ⟨342682322472689201141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3655278106375351478837 342682322472689201141)
      ·
        rfl

theorem cell_1069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_1069 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1069 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1069 prefixEnd_1069 := by
    exact prefixLift 1069
  have htrace : WordTrace (prefixWord ++ tailWord_1069) baseStart_1069 baseEnd_1069 := by
    simpa [prefixWord, tailWord_1069, baseEnd_1069] using wordTrace_append hprefix tailTrace_1069
  have hstable : (prefixWord ++ tailWord_1069).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069).length < 2 ^ (prefixWord ++ tailWord_1069).sum := by decide
  have hdescent : baseEnd_1069 < baseStart_1069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090 : List Nat := [3, 6]
def baseStart_1090 : Nat := 118140960795 + 1090 * 2 ^ 59
def prefixEnd_1090 : Nat := 4983230072969 + 3 ^ 40 * 1090 * 2
def baseEnd_1090 : Nat := 465885539749113308071

theorem tailTrace_1090 : CollatzResearch.WordTrace tailWord_1090 prefixEnd_1090 465885539749113308071 := by
  unfold tailWord_1090
  simp only [CollatzResearch.WordTrace]
  refine ⟨9938891514647750572181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26503710705727334859149 9938891514647750572181)
  ·
    refine ⟨465885539749113308071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9938891514647750572181 465885539749113308071)
    ·
      rfl

theorem cell_1090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_1090 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1090 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1090 prefixEnd_1090 := by
    exact prefixLift 1090
  have htrace : WordTrace (prefixWord ++ tailWord_1090) baseStart_1090 baseEnd_1090 := by
    simpa [prefixWord, tailWord_1090, baseEnd_1090] using wordTrace_append hprefix tailTrace_1090
  have hstable : (prefixWord ++ tailWord_1090).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090).length < 2 ^ (prefixWord ++ tailWord_1090).sum := by decide
  have hdescent : baseEnd_1090 < baseStart_1090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1092 : List Nat := [2, 3, 6]
def baseStart_1092 : Nat := 118140960795 + 1092 * 2 ^ 59
def prefixEnd_1092 : Nat := 4983230072969 + 3 ^ 40 * 1092 * 2
def baseEnd_1092 : Nat := 350055281701277436283

theorem tailTrace_1092 : CollatzResearch.WordTrace tailWord_1092 prefixEnd_1092 350055281701277436283 := by
  unfold tailWord_1092
  simp only [CollatzResearch.WordTrace]
  refine ⟨19914256025672671930765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26552341367563562574353 19914256025672671930765)
  ·
    refine ⟨7467846009627251974037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19914256025672671930765 7467846009627251974037)
    ·
      refine ⟨350055281701277436283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7467846009627251974037 350055281701277436283)
      ·
        rfl

theorem cell_1092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_1092 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1092 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1092 prefixEnd_1092 := by
    exact prefixLift 1092
  have htrace : WordTrace (prefixWord ++ tailWord_1092) baseStart_1092 baseEnd_1092 := by
    simpa [prefixWord, tailWord_1092, baseEnd_1092] using wordTrace_append hprefix tailTrace_1092
  have hstable : (prefixWord ++ tailWord_1092).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1092).length < 2 ^ (prefixWord ++ tailWord_1092).sum := by decide
  have hdescent : baseEnd_1092 < baseStart_1092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126 : List Nat := [7]
def baseStart_1126 : Nat := 118140960795 + 1126 * 2 ^ 59
def prefixEnd_1126 : Nat := 4983230072969 + 3 ^ 40 * 1126 * 2
def baseEnd_1126 : Nat := 641696780127642978113

theorem tailTrace_1126 : CollatzResearch.WordTrace tailWord_1126 prefixEnd_1126 641696780127642978113 := by
  unfold tailWord_1126
  simp only [CollatzResearch.WordTrace]
  refine ⟨641696780127642978113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 27379062618779433732821 641696780127642978113)
  ·
    rfl

theorem cell_1126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1126 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1126 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1126 prefixEnd_1126 := by
    exact prefixLift 1126
  have htrace : WordTrace (prefixWord ++ tailWord_1126) baseStart_1126 baseEnd_1126 := by
    simpa [prefixWord, tailWord_1126, baseEnd_1126] using wordTrace_append hprefix tailTrace_1126
  have hstable : (prefixWord ++ tailWord_1126).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126).length < 2 ^ (prefixWord ++ tailWord_1126).sum := by decide
  have hdescent : baseEnd_1126 < baseStart_1126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140 : List Nat := [2, 7]
def baseStart_1140 : Nat := 118140960795 + 1140 * 2 ^ 59
def prefixEnd_1140 : Nat := 4983230072969 + 3 ^ 40 * 1140 * 2
def baseEnd_1140 : Nat := 487256436063861815729

theorem tailTrace_1140 : CollatzResearch.WordTrace tailWord_1140 prefixEnd_1140 487256436063861815729 := by
  unfold tailWord_1140
  simp only [CollatzResearch.WordTrace]
  refine ⟨20789607938724770804437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27719477251633027739249 20789607938724770804437)
  ·
    refine ⟨487256436063861815729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 20789607938724770804437 487256436063861815729)
    ·
      rfl

theorem cell_1140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_1140 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1140 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1140 prefixEnd_1140 := by
    exact prefixLift 1140
  have htrace : WordTrace (prefixWord ++ tailWord_1140) baseStart_1140 baseEnd_1140 := by
    simpa [prefixWord, tailWord_1140, baseEnd_1140] using wordTrace_append hprefix tailTrace_1140
  have hstable : (prefixWord ++ tailWord_1140).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140).length < 2 ^ (prefixWord ++ tailWord_1140).sum := by decide
  have hdescent : baseEnd_1140 < baseStart_1140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154 : List Nat := [3, 4, 4]
def baseStart_1154 : Nat := 118140960795 + 1154 * 2 ^ 59
def prefixEnd_1154 : Nat := 4983230072969 + 3 ^ 40 * 1154 * 2
def baseEnd_1154 : Nat := 369930215273993548405

theorem tailTrace_1154 : CollatzResearch.WordTrace tailWord_1154 prefixEnd_1154 369930215273993548405 := by
  unfold tailWord_1154
  simp only [CollatzResearch.WordTrace]
  refine ⟨10522459456682483154629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28059891884486621745677 10522459456682483154629)
  ·
    refine ⟨1972961148127965591493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10522459456682483154629 1972961148127965591493)
    ·
      refine ⟨369930215273993548405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1972961148127965591493 369930215273993548405)
      ·
        rfl

theorem cell_1154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_1154 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1154 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1154 prefixEnd_1154 := by
    exact prefixLift 1154
  have htrace : WordTrace (prefixWord ++ tailWord_1154) baseStart_1154 baseEnd_1154 := by
    simpa [prefixWord, tailWord_1154, baseEnd_1154] using wordTrace_append hprefix tailTrace_1154
  have hstable : (prefixWord ++ tailWord_1154).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154).length < 2 ^ (prefixWord ++ tailWord_1154).sum := by decide
  have hdescent : baseEnd_1154 < baseStart_1154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158 : List Nat := [6, 4]
def baseStart_1158 : Nat := 118140960795 + 1158 * 2 ^ 59
def prefixEnd_1158 : Nat := 4983230072969 + 3 ^ 40 * 1158 * 2
def baseEnd_1158 : Nat := 247474979368585639243

theorem tailTrace_1158 : CollatzResearch.WordTrace tailWord_1158 prefixEnd_1158 247474979368585639243 := by
  unfold tailWord_1158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1319866556632456742629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28157153208159077176085 1319866556632456742629)
  ·
    refine ⟨247474979368585639243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1319866556632456742629 247474979368585639243)
    ·
      rfl

theorem cell_1158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_1158 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1158 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1158 prefixEnd_1158 := by
    exact prefixLift 1158
  have htrace : WordTrace (prefixWord ++ tailWord_1158) baseStart_1158 baseEnd_1158 := by
    simpa [prefixWord, tailWord_1158, baseEnd_1158] using wordTrace_append hprefix tailTrace_1158
  have hstable : (prefixWord ++ tailWord_1158).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158).length < 2 ^ (prefixWord ++ tailWord_1158).sum := by decide
  have hdescent : baseEnd_1158 < baseStart_1158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165 : List Nat := [1, 9]
def baseStart_1165 : Nat := 118140960795 + 1165 * 2 ^ 59
def prefixEnd_1165 : Nat := 4983230072969 + 3 ^ 40 * 1165 * 2
def baseEnd_1165 : Nat := 248970942110618034779

theorem tailTrace_1165 : CollatzResearch.WordTrace tailWord_1165 prefixEnd_1165 248970942110618034779 := by
  unfold tailWord_1165
  simp only [CollatzResearch.WordTrace]
  refine ⟨42491040786878811268949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28327360524585874179299 42491040786878811268949)
  ·
    refine ⟨248970942110618034779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 9 42491040786878811268949 248970942110618034779)
    ·
      rfl

theorem cell_1165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_1165 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1165 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1165 prefixEnd_1165 := by
    exact prefixLift 1165
  have htrace : WordTrace (prefixWord ++ tailWord_1165) baseStart_1165 baseEnd_1165 := by
    simpa [prefixWord, tailWord_1165, baseEnd_1165] using wordTrace_append hprefix tailTrace_1165
  have hstable : (prefixWord ++ tailWord_1165).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165).length < 2 ^ (prefixWord ++ tailWord_1165).sum := by decide
  have hdescent : baseEnd_1165 < baseStart_1165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172 : List Nat := [2, 4, 2, 4]
def baseStart_1172 : Nat := 118140960795 + 1172 * 2 ^ 59
def prefixEnd_1172 : Nat := 4983230072969 + 3 ^ 40 * 1172 * 2
def baseEnd_1172 : Nat := 563550535918463468209

theorem tailTrace_1172 : CollatzResearch.WordTrace tailWord_1172 prefixEnd_1172 563550535918463468209 := by
  unfold tailWord_1172
  simp only [CollatzResearch.WordTrace]
  refine ⟨21373175880759503386885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28497567841012671182513 21373175880759503386885)
  ·
    refine ⟨4007470477642406885041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21373175880759503386885 4007470477642406885041)
    ·
      refine ⟨3005602858231805163781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4007470477642406885041 3005602858231805163781)
      ·
        refine ⟨563550535918463468209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3005602858231805163781 563550535918463468209)
        ·
          rfl

theorem cell_1172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_1172 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1172 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1172 prefixEnd_1172 := by
    exact prefixLift 1172
  have htrace : WordTrace (prefixWord ++ tailWord_1172) baseStart_1172 baseEnd_1172 := by
    simpa [prefixWord, tailWord_1172, baseEnd_1172] using wordTrace_append hprefix tailTrace_1172
  have hstable : (prefixWord ++ tailWord_1172).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172).length < 2 ^ (prefixWord ++ tailWord_1172).sum := by decide
  have hdescent : baseEnd_1172 < baseStart_1172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190 : List Nat := [9]
def baseStart_1190 : Nat := 118140960795 + 1190 * 2 ^ 59
def prefixEnd_1190 : Nat := 4983230072969 + 3 ^ 40 * 1190 * 2
def baseEnd_1190 : Nat := 169542444126203441129

theorem tailTrace_1190 : CollatzResearch.WordTrace tailWord_1190 prefixEnd_1190 169542444126203441129 := by
  unfold tailWord_1190
  simp only [CollatzResearch.WordTrace]
  refine ⟨169542444126203441129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 9 28935243797538720619349 169542444126203441129)
  ·
    rfl

theorem cell_1190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_1190 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1190 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1190 prefixEnd_1190 := by
    exact prefixLift 1190
  have htrace : WordTrace (prefixWord ++ tailWord_1190) baseStart_1190 baseEnd_1190 := by
    simpa [prefixWord, tailWord_1190, baseEnd_1190] using wordTrace_append hprefix tailTrace_1190
  have hstable : (prefixWord ++ tailWord_1190).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190).length < 2 ^ (prefixWord ++ tailWord_1190).sum := by decide
  have hdescent : baseEnd_1190 < baseStart_1190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192 : List Nat := [2, 1, 9]
def baseStart_1192 : Nat := 118140960795 + 1192 * 2 ^ 59
def prefixEnd_1192 : Nat := 4983230072969 + 3 ^ 40 * 1192 * 2
def baseEnd_1192 : Nat := 191055813086700098885

theorem tailTrace_1192 : CollatzResearch.WordTrace tailWord_1192 prefixEnd_1192 191055813086700098885 := by
  unfold tailWord_1192
  simp only [CollatzResearch.WordTrace]
  refine ⟨21737905844531211250915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28983874459374948334553 21737905844531211250915)
  ·
    refine ⟨32606858766796816876373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21737905844531211250915 32606858766796816876373)
    ·
      refine ⟨191055813086700098885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 9 32606858766796816876373 191055813086700098885)
      ·
        rfl

theorem cell_1192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_1192 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1192 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1192 prefixEnd_1192 := by
    exact prefixLift 1192
  have htrace : WordTrace (prefixWord ++ tailWord_1192) baseStart_1192 baseEnd_1192 := by
    simpa [prefixWord, tailWord_1192, baseEnd_1192] using wordTrace_append hprefix tailTrace_1192
  have hstable : (prefixWord ++ tailWord_1192).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192).length < 2 ^ (prefixWord ++ tailWord_1192).sum := by decide
  have hdescent : baseEnd_1192 < baseStart_1192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198 : List Nat := [4, 1, 4, 3]
def baseStart_1198 : Nat := 118140960795 + 1198 * 2 ^ 59
def prefixEnd_1198 : Nat := 4983230072969 + 3 ^ 40 * 1198 * 2
def baseEnd_1198 : Nat := 576052510262591345189

theorem tailTrace_1198 : CollatzResearch.WordTrace tailWord_1198 prefixEnd_1198 576052510262591345189 := by
  unfold tailWord_1198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5461831208415680902531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29129766444883631480165 5461831208415680902531)
  ·
    refine ⟨8192746812623521353797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5461831208415680902531 8192746812623521353797)
    ·
      refine ⟨1536140027366910253837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8192746812623521353797 1536140027366910253837)
      ·
        refine ⟨576052510262591345189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1536140027366910253837 576052510262591345189)
        ·
          rfl

theorem cell_1198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_1198 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1198 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1198 prefixEnd_1198 := by
    exact prefixLift 1198
  have htrace : WordTrace (prefixWord ++ tailWord_1198) baseStart_1198 baseEnd_1198 := by
    simpa [prefixWord, tailWord_1198, baseEnd_1198] using wordTrace_append hprefix tailTrace_1198
  have hstable : (prefixWord ++ tailWord_1198).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198).length < 2 ^ (prefixWord ++ tailWord_1198).sum := by decide
  have hdescent : baseEnd_1198 < baseStart_1198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204 : List Nat := [2, 5, 3, 2]
def baseStart_1204 : Nat := 118140960795 + 1204 * 2 ^ 59
def prefixEnd_1204 : Nat := 4983230072969 + 3 ^ 40 * 1204 * 2
def baseEnd_1204 : Nat := 578937581265082393723

theorem tailTrace_1204 : CollatzResearch.WordTrace tailWord_1204 prefixEnd_1204 578937581265082393723 := by
  unfold tailWord_1204
  simp only [CollatzResearch.WordTrace]
  refine ⟨21956743822794235969333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29275658430392314625777 21956743822794235969333)
  ·
    refine ⟨2058444733386959622125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21956743822794235969333 2058444733386959622125)
    ·
      refine ⟨771916775020109858297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2058444733386959622125 771916775020109858297)
      ·
        refine ⟨578937581265082393723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 771916775020109858297 578937581265082393723)
        ·
          rfl

theorem cell_1204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_1204 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1204 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1204 prefixEnd_1204 := by
    exact prefixLift 1204
  have htrace : WordTrace (prefixWord ++ tailWord_1204) baseStart_1204 baseEnd_1204 := by
    simpa [prefixWord, tailWord_1204, baseEnd_1204] using wordTrace_append hprefix tailTrace_1204
  have hstable : (prefixWord ++ tailWord_1204).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204).length < 2 ^ (prefixWord ++ tailWord_1204).sum := by decide
  have hdescent : baseEnd_1204 < baseStart_1204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205 : List Nat := [1, 3, 3, 5]
def baseStart_1205 : Nat := 118140960795 + 1205 * 2 ^ 59
def prefixEnd_1205 : Nat := 4983230072969 + 3 ^ 40 * 1205 * 2
def baseEnd_1205 : Nat := 579418426432164235145

theorem tailTrace_1205 : CollatzResearch.WordTrace tailWord_1205 prefixEnd_1205 579418426432164235145 := by
  unfold tailWord_1205
  simp only [CollatzResearch.WordTrace]
  refine ⟨43949960641965642725069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29299973761310428483379 43949960641965642725069)
  ·
    refine ⟨16481235240737116021901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43949960641965642725069 16481235240737116021901)
    ·
      refine ⟨6180463215276418508213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16481235240737116021901 6180463215276418508213)
      ·
        refine ⟨579418426432164235145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6180463215276418508213 579418426432164235145)
        ·
          rfl

theorem cell_1205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_1205 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1205 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1205 prefixEnd_1205 := by
    exact prefixLift 1205
  have htrace : WordTrace (prefixWord ++ tailWord_1205) baseStart_1205 baseEnd_1205 := by
    simpa [prefixWord, tailWord_1205, baseEnd_1205] using wordTrace_append hprefix tailTrace_1205
  have hstable : (prefixWord ++ tailWord_1205).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205).length < 2 ^ (prefixWord ++ tailWord_1205).sum := by decide
  have hdescent : baseEnd_1205 < baseStart_1205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244 : List Nat := [2, 2, 5, 3]
def baseStart_1244 : Nat := 118140960795 + 1244 * 2 ^ 59
def prefixEnd_1244 : Nat := 4983230072969 + 3 ^ 40 * 1244 * 2
def baseEnd_1244 : Nat := 598171387948356050615

theorem tailTrace_1244 : CollatzResearch.WordTrace tailWord_1244 prefixEnd_1244 598171387948356050615 := by
  unfold tailWord_1244
  simp only [CollatzResearch.WordTrace]
  refine ⟨22686203750337651697393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30248271667116868929857 22686203750337651697393)
  ·
    refine ⟨17014652812753238773045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22686203750337651697393 17014652812753238773045)
    ·
      refine ⟨1595123701195616134973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17014652812753238773045 1595123701195616134973)
      ·
        refine ⟨598171387948356050615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1595123701195616134973 598171387948356050615)
        ·
          rfl

theorem cell_1244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_1244 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1244 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1244 prefixEnd_1244 := by
    exact prefixLift 1244
  have htrace : WordTrace (prefixWord ++ tailWord_1244) baseStart_1244 baseEnd_1244 := by
    simpa [prefixWord, tailWord_1244, baseEnd_1244] using wordTrace_append hprefix tailTrace_1244
  have hstable : (prefixWord ++ tailWord_1244).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244).length < 2 ^ (prefixWord ++ tailWord_1244).sum := by decide
  have hdescent : baseEnd_1244 < baseStart_1244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246 : List Nat := [4, 7]
def baseStart_1246 : Nat := 118140960795 + 1246 * 2 ^ 59
def prefixEnd_1246 : Nat := 4983230072969 + 3 ^ 40 * 1246 * 2
def baseEnd_1246 : Nat := 133140684062782162991

theorem tailTrace_1246 : CollatzResearch.WordTrace tailWord_1246 prefixEnd_1246 133140684062782162991 := by
  unfold tailWord_1246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5680669186678705620949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30296902328953096645061 5680669186678705620949)
  ·
    refine ⟨133140684062782162991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 5680669186678705620949 133140684062782162991)
    ·
      rfl

theorem cell_1246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_1246 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1246 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1246 prefixEnd_1246 := by
    exact prefixLift 1246
  have htrace : WordTrace (prefixWord ++ tailWord_1246) baseStart_1246 baseEnd_1246 := by
    simpa [prefixWord, tailWord_1246, baseEnd_1246] using wordTrace_append hprefix tailTrace_1246
  have hstable : (prefixWord ++ tailWord_1246).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246).length < 2 ^ (prefixWord ++ tailWord_1246).sum := by decide
  have hdescent : baseEnd_1246 < baseStart_1246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250 : List Nat := [3, 3, 4, 2]
def baseStart_1250 : Nat := 118140960795 + 1250 * 2 ^ 59
def prefixEnd_1250 : Nat := 4983230072969 + 3 ^ 40 * 1250 * 2
def baseEnd_1250 : Nat := 601056458950847099149

theorem tailTrace_1250 : CollatzResearch.WordTrace tailWord_1250 prefixEnd_1250 601056458950847099149 := by
  unfold tailWord_1250
  simp only [CollatzResearch.WordTrace]
  refine ⟨11397811369734582028301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30394163652625552075469 11397811369734582028301)
  ·
    refine ⟨4274179263650468260613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11397811369734582028301 4274179263650468260613)
    ·
      refine ⟨801408611934462798865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4274179263650468260613 801408611934462798865)
      ·
        refine ⟨601056458950847099149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 801408611934462798865 601056458950847099149)
        ·
          rfl

theorem cell_1250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_1250 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1250 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1250 prefixEnd_1250 := by
    exact prefixLift 1250
  have htrace : WordTrace (prefixWord ++ tailWord_1250) baseStart_1250 baseEnd_1250 := by
    simpa [prefixWord, tailWord_1250, baseEnd_1250] using wordTrace_append hprefix tailTrace_1250
  have hstable : (prefixWord ++ tailWord_1250).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250).length < 2 ^ (prefixWord ++ tailWord_1250).sum := by decide
  have hdescent : baseEnd_1250 < baseStart_1250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251 : List Nat := [1, 1, 1, 9]
def baseStart_1251 : Nat := 118140960795 + 1251 * 2 ^ 59
def prefixEnd_1251 : Nat := 4983230072969 + 3 ^ 40 * 1251 * 2
def baseEnd_1251 : Nat := 601537304117928940571

theorem tailTrace_1251 : CollatzResearch.WordTrace tailWord_1251 prefixEnd_1251 601537304117928940571 := by
  unfold tailWord_1251
  simp only [CollatzResearch.WordTrace]
  refine ⟨45627718475315498899607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30418478983543665933071 45627718475315498899607)
  ·
    refine ⟨68441577712973248349411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45627718475315498899607 68441577712973248349411)
    ·
      refine ⟨102662366569459872524117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68441577712973248349411 102662366569459872524117)
      ·
        refine ⟨601537304117928940571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 102662366569459872524117 601537304117928940571)
        ·
          rfl

theorem cell_1251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_1251 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1251 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1251 prefixEnd_1251 := by
    exact prefixLift 1251
  have htrace : WordTrace (prefixWord ++ tailWord_1251) baseStart_1251 baseEnd_1251 := by
    simpa [prefixWord, tailWord_1251, baseEnd_1251] using wordTrace_append hprefix tailTrace_1251
  have hstable : (prefixWord ++ tailWord_1251).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251).length < 2 ^ (prefixWord ++ tailWord_1251).sum := by decide
  have hdescent : baseEnd_1251 < baseStart_1251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254 : List Nat := [7]
def baseStart_1254 : Nat := 118140960795 + 1254 * 2 ^ 59
def prefixEnd_1254 : Nat := 4983230072969 + 3 ^ 40 * 1254 * 2
def baseEnd_1254 : Nat := 714642772881984550919

theorem tailTrace_1254 : CollatzResearch.WordTrace tailWord_1254 prefixEnd_1254 714642772881984550919 := by
  unfold tailWord_1254
  simp only [CollatzResearch.WordTrace]
  refine ⟨714642772881984550919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 30491424976298007505877 714642772881984550919)
  ·
    rfl

theorem cell_1254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1254 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1254 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1254 prefixEnd_1254 := by
    exact prefixLift 1254
  have htrace : WordTrace (prefixWord ++ tailWord_1254) baseStart_1254 baseEnd_1254 := by
    simpa [prefixWord, tailWord_1254, baseEnd_1254] using wordTrace_append hprefix tailTrace_1254
  have hstable : (prefixWord ++ tailWord_1254).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254).length < 2 ^ (prefixWord ++ tailWord_1254).sum := by decide
  have hdescent : baseEnd_1254 < baseStart_1254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269 : List Nat := [1, 3, 7]
def baseStart_1269 : Nat := 118140960795 + 1269 * 2 ^ 59
def prefixEnd_1269 : Nat := 4983230072969 + 3 ^ 40 * 1269 * 2
def baseEnd_1269 : Nat := 406795011416934724115

theorem tailTrace_1269 : CollatzResearch.WordTrace tailWord_1269 prefixEnd_1269 406795011416934724115 := by
  unfold tailWord_1269
  simp only [CollatzResearch.WordTrace]
  refine ⟨46284232410104573054861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30856154940069715369907 46284232410104573054861)
  ·
    refine ⟨17356587153789214895573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46284232410104573054861 17356587153789214895573)
    ·
      refine ⟨406795011416934724115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 17356587153789214895573 406795011416934724115)
      ·
        rfl

theorem cell_1269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_1269 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1269 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1269 prefixEnd_1269 := by
    exact prefixLift 1269
  have htrace : WordTrace (prefixWord ++ tailWord_1269) baseStart_1269 baseEnd_1269 := by
    simpa [prefixWord, tailWord_1269, baseEnd_1269] using wordTrace_append hprefix tailTrace_1269
  have hstable : (prefixWord ++ tailWord_1269).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269).length < 2 ^ (prefixWord ++ tailWord_1269).sum := by decide
  have hdescent : baseEnd_1269 < baseStart_1269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302 : List Nat := [5, 4]
def baseStart_1302 : Nat := 118140960795 + 1302 * 2 ^ 59
def prefixEnd_1302 : Nat := 4983230072969 + 3 ^ 40 * 1302 * 2
def baseEnd_1302 : Nat := 556498140123646980541

theorem tailTrace_1302 : CollatzResearch.WordTrace tailWord_1302 prefixEnd_1302 556498140123646980541 := by
  unfold tailWord_1302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2967990080659450562885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31658560860367472670773 2967990080659450562885)
  ·
    refine ⟨556498140123646980541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2967990080659450562885 556498140123646980541)
    ·
      rfl

theorem cell_1302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_1302 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1302 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1302 prefixEnd_1302 := by
    exact prefixLift 1302
  have htrace : WordTrace (prefixWord ++ tailWord_1302) baseStart_1302 baseEnd_1302 := by
    simpa [prefixWord, tailWord_1302, baseEnd_1302] using wordTrace_append hprefix tailTrace_1302
  have hstable : (prefixWord ++ tailWord_1302).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302).length < 2 ^ (prefixWord ++ tailWord_1302).sum := by decide
  have hdescent : baseEnd_1302 < baseStart_1302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318 : List Nat := [8]
def baseStart_1318 : Nat := 118140960795 + 1318 * 2 ^ 59
def prefixEnd_1318 : Nat := 4983230072969 + 3 ^ 40 * 1318 * 2
def baseEnd_1318 : Nat := 375557884629577668661

theorem tailTrace_1318 : CollatzResearch.WordTrace tailWord_1318 prefixEnd_1318 375557884629577668661 := by
  unfold tailWord_1318
  simp only [CollatzResearch.WordTrace]
  refine ⟨375557884629577668661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 32047606155057294392405 375557884629577668661)
  ·
    rfl

theorem cell_1318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1318 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1318 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1318 prefixEnd_1318 := by
    exact prefixLift 1318
  have htrace : WordTrace (prefixWord ++ tailWord_1318) baseStart_1318 baseEnd_1318 := by
    simpa [prefixWord, tailWord_1318, baseEnd_1318] using wordTrace_append hprefix tailTrace_1318
  have hstable : (prefixWord ++ tailWord_1318).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318).length < 2 ^ (prefixWord ++ tailWord_1318).sum := by decide
  have hdescent : baseEnd_1318 < baseStart_1318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374 : List Nat := [4, 4, 2, 2]
def baseStart_1374 : Nat := 118140960795 + 1374 * 2 ^ 59
def prefixEnd_1374 : Nat := 4983230072969 + 3 ^ 40 * 1374 * 2
def baseEnd_1374 : Nat := 660681259668995435515

theorem tailTrace_1374 : CollatzResearch.WordTrace tailWord_1374 prefixEnd_1374 660681259668995435515 := by
  unfold tailWord_1374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6264237128713438203397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33409264686471670418117 6264237128713438203397)
  ·
    refine ⟨1174544461633769663137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6264237128713438203397 1174544461633769663137)
    ·
      refine ⟨880908346225327247353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1174544461633769663137 880908346225327247353)
      ·
        refine ⟨660681259668995435515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 880908346225327247353 660681259668995435515)
        ·
          rfl

theorem cell_1374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_1374 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1374 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1374 prefixEnd_1374 := by
    exact prefixLift 1374
  have htrace : WordTrace (prefixWord ++ tailWord_1374) baseStart_1374 baseEnd_1374 := by
    simpa [prefixWord, tailWord_1374, baseEnd_1374] using wordTrace_append hprefix tailTrace_1374
  have hstable : (prefixWord ++ tailWord_1374).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374).length < 2 ^ (prefixWord ++ tailWord_1374).sum := by decide
  have hdescent : baseEnd_1374 < baseStart_1374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1382 : List Nat := [7]
def baseStart_1382 : Nat := 118140960795 + 1382 * 2 ^ 59
def prefixEnd_1382 : Nat := 4983230072969 + 3 ^ 40 * 1382 * 2
def baseEnd_1382 : Nat := 787588765636326123725

theorem tailTrace_1382 : CollatzResearch.WordTrace tailWord_1382 prefixEnd_1382 787588765636326123725 := by
  unfold tailWord_1382
  simp only [CollatzResearch.WordTrace]
  refine ⟨787588765636326123725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 33603787333816581278933 787588765636326123725)
  ·
    rfl

theorem cell_1382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1382 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1382 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1382 prefixEnd_1382 := by
    exact prefixLift 1382
  have htrace : WordTrace (prefixWord ++ tailWord_1382) baseStart_1382 baseEnd_1382 := by
    simpa [prefixWord, tailWord_1382, baseEnd_1382] using wordTrace_append hprefix tailTrace_1382
  have hstable : (prefixWord ++ tailWord_1382).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1382).length < 2 ^ (prefixWord ++ tailWord_1382).sum := by decide
  have hdescent : baseEnd_1382 < baseStart_1382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396 : List Nat := [2, 8]
def baseStart_1396 : Nat := 118140960795 + 1396 * 2 ^ 59
def prefixEnd_1396 : Nat := 4983230072969 + 3 ^ 40 * 1396 * 2
def baseEnd_1396 : Nat := 298337712597687087469

theorem tailTrace_1396 : CollatzResearch.WordTrace tailWord_1396 prefixEnd_1396 298337712597687087469 := by
  unfold tailWord_1396
  simp only [CollatzResearch.WordTrace]
  refine ⟨25458151475002631464021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33944201966670175285361 25458151475002631464021)
  ·
    refine ⟨298337712597687087469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 25458151475002631464021 298337712597687087469)
    ·
      rfl

theorem cell_1396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_1396 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1396 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1396 prefixEnd_1396 := by
    exact prefixLift 1396
  have htrace : WordTrace (prefixWord ++ tailWord_1396) baseStart_1396 baseEnd_1396 := by
    simpa [prefixWord, tailWord_1396, baseEnd_1396] using wordTrace_append hprefix tailTrace_1396
  have hstable : (prefixWord ++ tailWord_1396).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396).length < 2 ^ (prefixWord ++ tailWord_1396).sum := by decide
  have hdescent : baseEnd_1396 < baseStart_1396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414 : List Nat := [6, 3]
def baseStart_1414 : Nat := 118140960795 + 1414 * 2 ^ 59
def prefixEnd_1414 : Nat := 4983230072969 + 3 ^ 40 * 1414 * 2
def baseEnd_1414 : Nat := 604368947868683637695

theorem tailTrace_1414 : CollatzResearch.WordTrace tailWord_1414 prefixEnd_1414 604368947868683637695 := by
  unfold tailWord_1414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1611650527649823033853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34381877923196224722197 1611650527649823033853)
  ·
    refine ⟨604368947868683637695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1611650527649823033853 604368947868683637695)
    ·
      rfl

theorem cell_1414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_1414 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1414 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1414 prefixEnd_1414 := by
    exact prefixLift 1414
  have htrace : WordTrace (prefixWord ++ tailWord_1414) baseStart_1414 baseEnd_1414 := by
    simpa [prefixWord, tailWord_1414, baseEnd_1414] using wordTrace_append hprefix tailTrace_1414
  have hstable : (prefixWord ++ tailWord_1414).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414).length < 2 ^ (prefixWord ++ tailWord_1414).sum := by decide
  have hdescent : baseEnd_1414 < baseStart_1414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1421 : List Nat := [1, 8]
def baseStart_1421 : Nat := 118140960795 + 1421 * 2 ^ 59
def prefixEnd_1421 : Nat := 4983230072969 + 3 ^ 40 * 1421 * 2
def baseEnd_1421 : Nat := 607360873352748428767

theorem tailTrace_1421 : CollatzResearch.WordTrace tailWord_1421 prefixEnd_1421 607360873352748428767 := by
  unfold tailWord_1421
  simp only [CollatzResearch.WordTrace]
  refine ⟨51828127859434532588117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34552085239623021725411 51828127859434532588117)
  ·
    refine ⟨607360873352748428767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 51828127859434532588117 607360873352748428767)
    ·
      rfl

theorem cell_1421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_1421 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1421 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1421 prefixEnd_1421 := by
    exact prefixLift 1421
  have htrace : WordTrace (prefixWord ++ tailWord_1421) baseStart_1421 baseEnd_1421 := by
    simpa [prefixWord, tailWord_1421, baseEnd_1421] using wordTrace_append hprefix tailTrace_1421
  have hstable : (prefixWord ++ tailWord_1421).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1421).length < 2 ^ (prefixWord ++ tailWord_1421).sum := by decide
  have hdescent : baseEnd_1421 < baseStart_1421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441 : List Nat := [1, 2, 3, 6]
def baseStart_1441 : Nat := 118140960795 + 1441 * 2 ^ 59
def prefixEnd_1441 : Nat := 4983230072969 + 3 ^ 40 * 1441 * 2
def baseEnd_1441 : Nat := 692897885863478810809

theorem tailTrace_1441 : CollatzResearch.WordTrace tailWord_1441 prefixEnd_1441 692897885863478810809 := by
  unfold tailWord_1441
  simp only [CollatzResearch.WordTrace]
  refine ⟨52557587786977948316177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35038391857985298877451 52557587786977948316177)
  ·
    refine ⟨39418190840233461237133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52557587786977948316177 39418190840233461237133)
    ·
      refine ⟨14781821565087547963925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39418190840233461237133 14781821565087547963925)
      ·
        refine ⟨692897885863478810809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14781821565087547963925 692897885863478810809)
        ·
          rfl

theorem cell_1441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_1441 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1441 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1441 prefixEnd_1441 := by
    exact prefixLift 1441
  have htrace : WordTrace (prefixWord ++ tailWord_1441) baseStart_1441 baseEnd_1441 := by
    simpa [prefixWord, tailWord_1441, baseEnd_1441] using wordTrace_append hprefix tailTrace_1441
  have hstable : (prefixWord ++ tailWord_1441).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441).length < 2 ^ (prefixWord ++ tailWord_1441).sum := by decide
  have hdescent : baseEnd_1441 < baseStart_1441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1446 : List Nat := [11]
def baseStart_1446 : Nat := 118140960795 + 1446 * 2 ^ 59
def prefixEnd_1446 : Nat := 4983230072969 + 3 ^ 40 * 1446 * 2
def baseEnd_1446 : Nat := 51503860125843556883

theorem tailTrace_1446 : CollatzResearch.WordTrace tailWord_1446 prefixEnd_1446 51503860125843556883 := by
  unfold tailWord_1446
  simp only [CollatzResearch.WordTrace]
  refine ⟨51503860125843556883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 11 35159968512575868165461 51503860125843556883)
  ·
    rfl

theorem cell_1446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_1446 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1446 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1446 prefixEnd_1446 := by
    exact prefixLift 1446
  have htrace : WordTrace (prefixWord ++ tailWord_1446) baseStart_1446 baseEnd_1446 := by
    simpa [prefixWord, tailWord_1446, baseEnd_1446] using wordTrace_append hprefix tailTrace_1446
  have hstable : (prefixWord ++ tailWord_1446).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1446).length < 2 ^ (prefixWord ++ tailWord_1446).sum := by decide
  have hdescent : baseEnd_1446 < baseStart_1446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454 : List Nat := [4, 1, 7]
def baseStart_1454 : Nat := 118140960795 + 1454 * 2 ^ 59
def prefixEnd_1454 : Nat := 4983230072969 + 3 ^ 40 * 1454 * 2
def baseEnd_1454 : Nat := 233049624345180916433

theorem tailTrace_1454 : CollatzResearch.WordTrace tailWord_1454 prefixEnd_1454 233049624345180916433 := by
  unfold tailWord_1454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6628967092485146067427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35354491159920779026277 6628967092485146067427)
  ·
    refine ⟨9943450638727719101141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6628967092485146067427 9943450638727719101141)
    ·
      refine ⟨233049624345180916433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 9943450638727719101141 233049624345180916433)
      ·
        rfl

theorem cell_1454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_1454 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1454 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1454 prefixEnd_1454 := by
    exact prefixLift 1454
  have htrace : WordTrace (prefixWord ++ tailWord_1454) baseStart_1454 baseEnd_1454 := by
    simpa [prefixWord, tailWord_1454, baseEnd_1454] using wordTrace_append hprefix tailTrace_1454
  have hstable : (prefixWord ++ tailWord_1454).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454).length < 2 ^ (prefixWord ++ tailWord_1454).sum := by decide
  have hdescent : baseEnd_1454 < baseStart_1454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460 : List Nat := [2, 5, 2, 3]
def baseStart_1460 : Nat := 118140960795 + 1460 * 2 ^ 59
def prefixEnd_1460 : Nat := 4983230072969 + 3 ^ 40 * 1460 * 2
def baseEnd_1460 : Nat := 702033944038033797833

theorem tailTrace_1460 : CollatzResearch.WordTrace tailWord_1460 prefixEnd_1460 702033944038033797833 := by
  unfold tailWord_1460
  simp only [CollatzResearch.WordTrace]
  refine ⟨26625287359072096628917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35500383145429462171889 26625287359072096628917)
  ·
    refine ⟨2496120689913009058961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26625287359072096628917 2496120689913009058961)
    ·
      refine ⟨1872090517434756794221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2496120689913009058961 1872090517434756794221)
      ·
        refine ⟨702033944038033797833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1872090517434756794221 702033944038033797833)
        ·
          rfl

theorem cell_1460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_1460 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1460 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1460 prefixEnd_1460 := by
    exact prefixLift 1460
  have htrace : WordTrace (prefixWord ++ tailWord_1460) baseStart_1460 baseEnd_1460 := by
    simpa [prefixWord, tailWord_1460, baseEnd_1460] using wordTrace_append hprefix tailTrace_1460
  have hstable : (prefixWord ++ tailWord_1460).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460).length < 2 ^ (prefixWord ++ tailWord_1460).sum := by decide
  have hdescent : baseEnd_1460 < baseStart_1460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462 : List Nat := [5, 1, 5]
def baseStart_1462 : Nat := 118140960795 + 1462 * 2 ^ 59
def prefixEnd_1462 : Nat := 4983230072969 + 3 ^ 40 * 1462 * 2
def baseEnd_1462 : Nat := 468663756248131653785

theorem tailTrace_1462 : CollatzResearch.WordTrace tailWord_1462 prefixEnd_1462 468663756248131653785 := by
  unfold tailWord_1462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3332720044431158426915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35549013807265689887093 3332720044431158426915)
  ·
    refine ⟨4999080066646737640373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3332720044431158426915 4999080066646737640373)
    ·
      refine ⟨468663756248131653785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4999080066646737640373 468663756248131653785)
      ·
        rfl

theorem cell_1462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_1462 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1462 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1462 prefixEnd_1462 := by
    exact prefixLift 1462
  have htrace : WordTrace (prefixWord ++ tailWord_1462) baseStart_1462 baseEnd_1462 := by
    simpa [prefixWord, tailWord_1462, baseEnd_1462] using wordTrace_append hprefix tailTrace_1462
  have hstable : (prefixWord ++ tailWord_1462).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462).length < 2 ^ (prefixWord ++ tailWord_1462).sum := by decide
  have hdescent : baseEnd_1462 < baseStart_1462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473 : List Nat := [1, 2, 7, 2]
def baseStart_1473 : Nat := 118140960795 + 1473 * 2 ^ 59
def prefixEnd_1473 : Nat := 4983230072969 + 3 ^ 40 * 1473 * 2
def baseEnd_1473 : Nat := 708284931210097736323

theorem tailTrace_1473 : CollatzResearch.WordTrace tailWord_1473 prefixEnd_1473 708284931210097736323 := by
  unfold tailWord_1473
  simp only [CollatzResearch.WordTrace]
  refine ⟨53724723671047413481073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35816482447364942320715 53724723671047413481073)
  ·
    refine ⟨40293542753285560110805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53724723671047413481073 40293542753285560110805)
    ·
      refine ⟨944379908280130315097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 40293542753285560110805 944379908280130315097)
      ·
        refine ⟨708284931210097736323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 944379908280130315097 708284931210097736323)
        ·
          rfl

theorem cell_1473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_1473 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1473 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1473 prefixEnd_1473 := by
    exact prefixLift 1473
  have htrace : WordTrace (prefixWord ++ tailWord_1473) baseStart_1473 baseEnd_1473 := by
    simpa [prefixWord, tailWord_1473, baseEnd_1473] using wordTrace_append hprefix tailTrace_1473
  have hstable : (prefixWord ++ tailWord_1473).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473).length < 2 ^ (prefixWord ++ tailWord_1473).sum := by decide
  have hdescent : baseEnd_1473 < baseStart_1473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478 : List Nat := [6, 1, 4]
def baseStart_1478 : Nat := 118140960795 + 1478 * 2 ^ 59
def prefixEnd_1478 : Nat := 4983230072969 + 3 ^ 40 * 1478 * 2
def baseEnd_1478 : Nat := 473792771363671295623

theorem tailTrace_1478 : CollatzResearch.WordTrace tailWord_1478 prefixEnd_1478 473792771363671295623 := by
  unfold tailWord_1478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1684596520404164606659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35938059101955511608725 1684596520404164606659)
  ·
    refine ⟨2526894780606246909989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1684596520404164606659 2526894780606246909989)
    ·
      refine ⟨473792771363671295623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2526894780606246909989 473792771363671295623)
      ·
        rfl

theorem cell_1478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_1478 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1478 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1478 prefixEnd_1478 := by
    exact prefixLift 1478
  have htrace : WordTrace (prefixWord ++ tailWord_1478) baseStart_1478 baseEnd_1478 := by
    simpa [prefixWord, tailWord_1478, baseEnd_1478] using wordTrace_append hprefix tailTrace_1478
  have hstable : (prefixWord ++ tailWord_1478).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478).length < 2 ^ (prefixWord ++ tailWord_1478).sum := by decide
  have hdescent : baseEnd_1478 < baseStart_1478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485 : List Nat := [1, 6, 4]
def baseStart_1485 : Nat := 118140960795 + 1485 * 2 ^ 59
def prefixEnd_1485 : Nat := 4983230072969 + 3 ^ 40 * 1485 * 2
def baseEnd_1485 : Nat := 476036715476719888927

theorem tailTrace_1485 : CollatzResearch.WordTrace tailWord_1485 prefixEnd_1485 476036715476719888927 := by
  unfold tailWord_1485
  simp only [CollatzResearch.WordTrace]
  refine ⟨54162399627573462917909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36108266418382308611939 54162399627573462917909)
  ·
    refine ⟨2538862482542506074277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54162399627573462917909 2538862482542506074277)
    ·
      refine ⟨476036715476719888927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2538862482542506074277 476036715476719888927)
      ·
        rfl

theorem cell_1485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_1485 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1485 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1485 prefixEnd_1485 := by
    exact prefixLift 1485
  have htrace : WordTrace (prefixWord ++ tailWord_1485) baseStart_1485 baseEnd_1485 := by
    simpa [prefixWord, tailWord_1485, baseEnd_1485] using wordTrace_append hprefix tailTrace_1485
  have hstable : (prefixWord ++ tailWord_1485).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485).length < 2 ^ (prefixWord ++ tailWord_1485).sum := by decide
  have hdescent : baseEnd_1485 < baseStart_1485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500 : List Nat := [2, 2, 8]
def baseStart_1500 : Nat := 118140960795 + 1500 * 2 ^ 59
def prefixEnd_1500 : Nat := 4983230072969 + 3 ^ 40 * 1500 * 2
def baseEnd_1500 : Nat := 240422583573769151575

theorem tailTrace_1500 : CollatzResearch.WordTrace tailWord_1500 prefixEnd_1500 240422583573769151575 := by
  unfold tailWord_1500
  simp only [CollatzResearch.WordTrace]
  refine ⟨27354747286615512356977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36472996382154016475969 27354747286615512356977)
  ·
    refine ⟨20516060464961634267733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27354747286615512356977 20516060464961634267733)
    ·
      refine ⟨240422583573769151575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 20516060464961634267733 240422583573769151575)
      ·
        rfl

theorem cell_1500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_1500 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1500 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1500 prefixEnd_1500 := by
    exact prefixLift 1500
  have htrace : WordTrace (prefixWord ++ tailWord_1500) baseStart_1500 baseEnd_1500 := by
    simpa [prefixWord, tailWord_1500, baseEnd_1500] using wordTrace_append hprefix tailTrace_1500
  have hstable : (prefixWord ++ tailWord_1500).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500).length < 2 ^ (prefixWord ++ tailWord_1500).sum := by decide
  have hdescent : baseEnd_1500 < baseStart_1500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502 : List Nat := [4, 5]
def baseStart_1502 : Nat := 118140960795 + 1502 * 2 ^ 59
def prefixEnd_1502 : Nat := 4983230072969 + 3 ^ 40 * 1502 * 2
def baseEnd_1502 : Nat := 641981725382641011173

theorem tailTrace_1502 : CollatzResearch.WordTrace tailWord_1502 prefixEnd_1502 641981725382641011173 := by
  unfold tailWord_1502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6847805070748170785845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36521627043990244191173 6847805070748170785845)
  ·
    refine ⟨641981725382641011173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6847805070748170785845 641981725382641011173)
    ·
      rfl

theorem cell_1502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_1502 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1502 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1502 prefixEnd_1502 := by
    exact prefixLift 1502
  have htrace : WordTrace (prefixWord ++ tailWord_1502) baseStart_1502 baseEnd_1502 := by
    simpa [prefixWord, tailWord_1502, baseEnd_1502] using wordTrace_append hprefix tailTrace_1502
  have hstable : (prefixWord ++ tailWord_1502).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502).length < 2 ^ (prefixWord ++ tailWord_1502).sum := by decide
  have hdescent : baseEnd_1502 < baseStart_1502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506 : List Nat := [3, 3, 3, 3]
def baseStart_1506 : Nat := 118140960795 + 1506 * 2 ^ 59
def prefixEnd_1506 : Nat := 4983230072969 + 3 ^ 40 * 1506 * 2
def baseEnd_1506 : Nat := 724152821723798503259

theorem tailTrace_1506 : CollatzResearch.WordTrace tailWord_1506 prefixEnd_1506 724152821723798503259 := by
  unfold tailWord_1506
  simp only [CollatzResearch.WordTrace]
  refine ⟨13732083137873512358093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36618888367662699621581 13732083137873512358093)
  ·
    refine ⟨5149531176702567134285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13732083137873512358093 5149531176702567134285)
    ·
      refine ⟨1931074191263462675357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5149531176702567134285 1931074191263462675357)
      ·
        refine ⟨724152821723798503259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1931074191263462675357 724152821723798503259)
        ·
          rfl

theorem cell_1506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_1506 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1506 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1506 prefixEnd_1506 := by
    exact prefixLift 1506
  have htrace : WordTrace (prefixWord ++ tailWord_1506) baseStart_1506 baseEnd_1506 := by
    simpa [prefixWord, tailWord_1506, baseEnd_1506] using wordTrace_append hprefix tailTrace_1506
  have hstable : (prefixWord ++ tailWord_1506).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506).length < 2 ^ (prefixWord ++ tailWord_1506).sum := by decide
  have hdescent : baseEnd_1506 < baseStart_1506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510 : List Nat := [7]
def baseStart_1510 : Nat := 118140960795 + 1510 * 2 ^ 59
def prefixEnd_1510 : Nat := 4983230072969 + 3 ^ 40 * 1510 * 2
def baseEnd_1510 : Nat := 860534758390667696531

theorem tailTrace_1510 : CollatzResearch.WordTrace tailWord_1510 prefixEnd_1510 860534758390667696531 := by
  unfold tailWord_1510
  simp only [CollatzResearch.WordTrace]
  refine ⟨860534758390667696531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 36716149691335155051989 860534758390667696531)
  ·
    rfl

theorem cell_1510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1510 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1510 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1510 prefixEnd_1510 := by
    exact prefixLift 1510
  have htrace : WordTrace (prefixWord ++ tailWord_1510) baseStart_1510 baseEnd_1510 := by
    simpa [prefixWord, tailWord_1510, baseEnd_1510] using wordTrace_append hprefix tailTrace_1510
  have hstable : (prefixWord ++ tailWord_1510).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510).length < 2 ^ (prefixWord ++ tailWord_1510).sum := by decide
  have hdescent : baseEnd_1510 < baseStart_1510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1524 : List Nat := [2, 6, 3]
def baseStart_1524 : Nat := 118140960795 + 1524 * 2 ^ 59
def prefixEnd_1524 : Nat := 4983230072969 + 3 ^ 40 * 1524 * 2
def baseEnd_1524 : Nat := 488538689820847765907

theorem tailTrace_1524 : CollatzResearch.WordTrace tailWord_1524 prefixEnd_1524 488538689820847765907 := by
  unfold tailWord_1524
  simp only [CollatzResearch.WordTrace]
  refine ⟨27792423243141561793813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37056564324188749058417 27792423243141561793813)
  ·
    refine ⟨1302769839522260709085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27792423243141561793813 1302769839522260709085)
    ·
      refine ⟨488538689820847765907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1302769839522260709085 488538689820847765907)
      ·
        rfl

theorem cell_1524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_1524 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1524 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1524 prefixEnd_1524 := by
    exact prefixLift 1524
  have htrace : WordTrace (prefixWord ++ tailWord_1524) baseStart_1524 baseEnd_1524 := by
    simpa [prefixWord, tailWord_1524, baseEnd_1524] using wordTrace_append hprefix tailTrace_1524
  have hstable : (prefixWord ++ tailWord_1524).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1524).length < 2 ^ (prefixWord ++ tailWord_1524).sum := by decide
  have hdescent : baseEnd_1524 < baseStart_1524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1554 : List Nat := [3, 2, 6]
def baseStart_1554 : Nat := 118140960795 + 1554 * 2 ^ 59
def prefixEnd_1554 : Nat := 4983230072969 + 3 ^ 40 * 1554 * 2
def baseEnd_1554 : Nat := 498155593162484594353

theorem tailTrace_1554 : CollatzResearch.WordTrace tailWord_1554 prefixEnd_1554 498155593162484594353 := by
  unfold tailWord_1554
  simp only [CollatzResearch.WordTrace]
  refine ⟨14169759094399561794929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37786024251732164786477 14169759094399561794929)
  ·
    refine ⟨10627319320799671346197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14169759094399561794929 10627319320799671346197)
    ·
      refine ⟨498155593162484594353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10627319320799671346197 498155593162484594353)
      ·
        rfl

theorem cell_1554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_1554 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1554 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1554 prefixEnd_1554 := by
    exact prefixLift 1554
  have htrace : WordTrace (prefixWord ++ tailWord_1554) baseStart_1554 baseEnd_1554 := by
    simpa [prefixWord, tailWord_1554, baseEnd_1554] using wordTrace_append hprefix tailTrace_1554
  have hstable : (prefixWord ++ tailWord_1554).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1554).length < 2 ^ (prefixWord ++ tailWord_1554).sum := by decide
  have hdescent : baseEnd_1554 < baseStart_1554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1558 : List Nat := [5, 5]
def baseStart_1558 : Nat := 118140960795 + 1558 * 2 ^ 59
def prefixEnd_1558 : Nat := 4983230072969 + 3 ^ 40 * 1558 * 2
def baseEnd_1558 : Nat := 332958564627579669875

theorem tailTrace_1558 : CollatzResearch.WordTrace tailWord_1558 prefixEnd_1558 332958564627579669875 := by
  unfold tailWord_1558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3551558022694183145333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37883285575404620216885 3551558022694183145333)
  ·
    refine ⟨332958564627579669875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3551558022694183145333 332958564627579669875)
    ·
      rfl

theorem cell_1558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_1558 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1558 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1558 prefixEnd_1558 := by
    exact prefixLift 1558
  have htrace : WordTrace (prefixWord ++ tailWord_1558) baseStart_1558 baseEnd_1558 := by
    simpa [prefixWord, tailWord_1558, baseEnd_1558] using wordTrace_append hprefix tailTrace_1558
  have hstable : (prefixWord ++ tailWord_1558).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1558).length < 2 ^ (prefixWord ++ tailWord_1558).sum := by decide
  have hdescent : baseEnd_1558 < baseStart_1558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559 : List Nat := [1, 1, 3, 7]
def baseStart_1559 : Nat := 118140960795 + 1559 * 2 ^ 59
def prefixEnd_1559 : Nat := 4983230072969 + 3 ^ 40 * 1559 * 2
def baseEnd_1559 : Nat := 749637615579136098641

theorem tailTrace_1559 : CollatzResearch.WordTrace tailWord_1559 prefixEnd_1559 749637615579136098641 := by
  unfold tailWord_1559
  simp only [CollatzResearch.WordTrace]
  refine ⟨56861401359484101111731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37907600906322734074487 56861401359484101111731)
  ·
    refine ⟨85292102039226151667597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56861401359484101111731 85292102039226151667597)
    ·
      refine ⟨31984538264709806875349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85292102039226151667597 31984538264709806875349)
      ·
        refine ⟨749637615579136098641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 31984538264709806875349 749637615579136098641)
        ·
          rfl

theorem cell_1559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_1559 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1559 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1559 prefixEnd_1559 := by
    exact prefixLift 1559
  have htrace : WordTrace (prefixWord ++ tailWord_1559) baseStart_1559 baseEnd_1559 := by
    simpa [prefixWord, tailWord_1559, baseEnd_1559] using wordTrace_append hprefix tailTrace_1559
  have hstable : (prefixWord ++ tailWord_1559).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559).length < 2 ^ (prefixWord ++ tailWord_1559).sum := by decide
  have hdescent : baseEnd_1559 < baseStart_1559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572 : List Nat := [2, 3, 1, 6]
def baseStart_1572 : Nat := 118140960795 + 1572 * 2 ^ 59
def prefixEnd_1572 : Nat := 4983230072969 + 3 ^ 40 * 1572 * 2
def baseEnd_1572 : Nat := 755888602751200037131

theorem tailTrace_1572 : CollatzResearch.WordTrace tailWord_1572 prefixEnd_1572 755888602751200037131 := by
  unfold tailWord_1572
  simp only [CollatzResearch.WordTrace]
  refine ⟨28667775156193660667485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38223700208258214223313 28667775156193660667485)
  ·
    refine ⟨10750415683572622750307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28667775156193660667485 10750415683572622750307)
    ·
      refine ⟨16125623525358934125461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10750415683572622750307 16125623525358934125461)
      ·
        refine ⟨755888602751200037131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16125623525358934125461 755888602751200037131)
        ·
          rfl

theorem cell_1572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_1572 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1572 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1572 prefixEnd_1572 := by
    exact prefixLift 1572
  have htrace : WordTrace (prefixWord ++ tailWord_1572) baseStart_1572 baseEnd_1572 := by
    simpa [prefixWord, tailWord_1572, baseEnd_1572] using wordTrace_append hprefix tailTrace_1572
  have hstable : (prefixWord ++ tailWord_1572).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572).length < 2 ^ (prefixWord ++ tailWord_1572).sum := by decide
  have hdescent : baseEnd_1572 < baseStart_1572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574 : List Nat := [8]
def baseStart_1574 : Nat := 118140960795 + 1574 * 2 ^ 59
def prefixEnd_1574 : Nat := 4983230072969 + 3 ^ 40 * 1574 * 2
def baseEnd_1574 : Nat := 448503877383919241467

theorem tailTrace_1574 : CollatzResearch.WordTrace tailWord_1574 prefixEnd_1574 448503877383919241467 := by
  unfold tailWord_1574
  simp only [CollatzResearch.WordTrace]
  refine ⟨448503877383919241467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 38272330870094441938517 448503877383919241467)
  ·
    rfl

theorem cell_1574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1574 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1574 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1574 prefixEnd_1574 := by
    exact prefixLift 1574
  have htrace : WordTrace (prefixWord ++ tailWord_1574) baseStart_1574 baseEnd_1574 := by
    simpa [prefixWord, tailWord_1574, baseEnd_1574] using wordTrace_append hprefix tailTrace_1574
  have hstable : (prefixWord ++ tailWord_1574).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574).length < 2 ^ (prefixWord ++ tailWord_1574).sum := by decide
  have hdescent : baseEnd_1574 < baseStart_1574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598 : List Nat := [4, 2, 1, 5]
def baseStart_1598 : Nat := 118140960795 + 1598 * 2 ^ 59
def prefixEnd_1598 : Nat := 4983230072969 + 3 ^ 40 * 1598 * 2
def baseEnd_1598 : Nat := 768390577095327914111

theorem tailTrace_1598 : CollatzResearch.WordTrace tailWord_1598 prefixEnd_1598 768390577095327914111 := by
  unfold tailWord_1598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7285481027274220222681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38855898812129174520965 7285481027274220222681)
  ·
    refine ⟨5464110770455665167011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7285481027274220222681 5464110770455665167011)
    ·
      refine ⟨8196166155683497750517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5464110770455665167011 8196166155683497750517)
      ·
        refine ⟨768390577095327914111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8196166155683497750517 768390577095327914111)
        ·
          rfl

theorem cell_1598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_1598 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1598 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1598 prefixEnd_1598 := by
    exact prefixLift 1598
  have htrace : WordTrace (prefixWord ++ tailWord_1598) baseStart_1598 baseEnd_1598 := by
    simpa [prefixWord, tailWord_1598, baseEnd_1598] using wordTrace_append hprefix tailTrace_1598
  have hstable : (prefixWord ++ tailWord_1598).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598).length < 2 ^ (prefixWord ++ tailWord_1598).sum := by decide
  have hdescent : baseEnd_1598 < baseStart_1598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602 : List Nat := [3, 6]
def baseStart_1602 : Nat := 118140960795 + 1602 * 2 ^ 59
def prefixEnd_1602 : Nat := 4983230072969 + 3 ^ 40 * 1602 * 2
def baseEnd_1602 : Nat := 684723518012138026489

theorem tailTrace_1602 : CollatzResearch.WordTrace tailWord_1602 prefixEnd_1602 684723518012138026489 := by
  unfold tailWord_1602
  simp only [CollatzResearch.WordTrace]
  refine ⟨14607435050925611231765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38953160135801629951373 14607435050925611231765)
  ·
    refine ⟨684723518012138026489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14607435050925611231765 684723518012138026489)
    ·
      rfl

theorem cell_1602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_1602 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1602 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1602 prefixEnd_1602 := by
    exact prefixLift 1602
  have htrace : WordTrace (prefixWord ++ tailWord_1602) baseStart_1602 baseEnd_1602 := by
    simpa [prefixWord, tailWord_1602, baseEnd_1602] using wordTrace_append hprefix tailTrace_1602
  have hstable : (prefixWord ++ tailWord_1602).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602).length < 2 ^ (prefixWord ++ tailWord_1602).sum := by decide
  have hdescent : baseEnd_1602 < baseStart_1602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604 : List Nat := [2, 3, 5, 2]
def baseStart_1604 : Nat := 118140960795 + 1604 * 2 ^ 59
def prefixEnd_1604 : Nat := 4983230072969 + 3 ^ 40 * 1604 * 2
def baseEnd_1604 : Nat := 771275648097818962645

theorem tailTrace_1604 : CollatzResearch.WordTrace tailWord_1604 prefixEnd_1604 771275648097818962645 := by
  unfold tailWord_1604
  simp only [CollatzResearch.WordTrace]
  refine ⟨29251343098228393249933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39001790797637857666577 29251343098228393249933)
  ·
    refine ⟨10969253661835647468725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29251343098228393249933 10969253661835647468725)
    ·
      refine ⟨1028367530797091950193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10969253661835647468725 1028367530797091950193)
      ·
        refine ⟨771275648097818962645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1028367530797091950193 771275648097818962645)
        ·
          rfl

theorem cell_1604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_1604 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1604 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1604 prefixEnd_1604 := by
    exact prefixLift 1604
  have htrace : WordTrace (prefixWord ++ tailWord_1604) baseStart_1604 baseEnd_1604 := by
    simpa [prefixWord, tailWord_1604, baseEnd_1604] using wordTrace_append hprefix tailTrace_1604
  have hstable : (prefixWord ++ tailWord_1604).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604).length < 2 ^ (prefixWord ++ tailWord_1604).sum := by decide
  have hdescent : baseEnd_1604 < baseStart_1604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630 : List Nat := [4, 4, 1, 3]
def baseStart_1630 : Nat := 118140960795 + 1630 * 2 ^ 59
def prefixEnd_1630 : Nat := 4983230072969 + 3 ^ 40 * 1630 * 2
def baseEnd_1630 : Nat := 783777622441946839625

theorem tailTrace_1630 : CollatzResearch.WordTrace tailWord_1630 prefixEnd_1630 783777622441946839625 := by
  unfold tailWord_1630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7431373012782903368293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39633989401508817964229 7431373012782903368293)
  ·
    refine ⟨1393382439896794381555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7431373012782903368293 1393382439896794381555)
    ·
      refine ⟨2090073659845191572333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1393382439896794381555 2090073659845191572333)
      ·
        refine ⟨783777622441946839625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2090073659845191572333 783777622441946839625)
        ·
          rfl

theorem cell_1630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_1630 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1630 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1630 prefixEnd_1630 := by
    exact prefixLift 1630
  have htrace : WordTrace (prefixWord ++ tailWord_1630) baseStart_1630 baseEnd_1630 := by
    simpa [prefixWord, tailWord_1630, baseEnd_1630] using wordTrace_append hprefix tailTrace_1630
  have hstable : (prefixWord ++ tailWord_1630).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630).length < 2 ^ (prefixWord ++ tailWord_1630).sum := by decide
  have hdescent : baseEnd_1630 < baseStart_1630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638 : List Nat := [7]
def baseStart_1638 : Nat := 118140960795 + 1638 * 2 ^ 59
def prefixEnd_1638 : Nat := 4983230072969 + 3 ^ 40 * 1638 * 2
def baseEnd_1638 : Nat := 933480751145009269337

theorem tailTrace_1638 : CollatzResearch.WordTrace tailWord_1638 prefixEnd_1638 933480751145009269337 := by
  unfold tailWord_1638
  simp only [CollatzResearch.WordTrace]
  refine ⟨933480751145009269337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 39828512048853728825045 933480751145009269337)
  ·
    rfl

theorem cell_1638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1638 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1638 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1638 prefixEnd_1638 := by
    exact prefixLift 1638
  have htrace : WordTrace (prefixWord ++ tailWord_1638) baseStart_1638 baseEnd_1638 := by
    simpa [prefixWord, tailWord_1638, baseEnd_1638] using wordTrace_append hprefix tailTrace_1638
  have hstable : (prefixWord ++ tailWord_1638).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638).length < 2 ^ (prefixWord ++ tailWord_1638).sum := by decide
  have hdescent : baseEnd_1638 < baseStart_1638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652 : List Nat := [2, 7]
def baseStart_1652 : Nat := 118140960795 + 1652 * 2 ^ 59
def prefixEnd_1652 : Nat := 4983230072969 + 3 ^ 40 * 1652 * 2
def baseEnd_1652 : Nat := 706094414326886534147

theorem tailTrace_1652 : CollatzResearch.WordTrace tailWord_1652 prefixEnd_1652 706094414326886534147 := by
  unfold tailWord_1652
  simp only [CollatzResearch.WordTrace]
  refine ⟨30126695011280492123605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40168926681707322831473 30126695011280492123605)
  ·
    refine ⟨706094414326886534147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 30126695011280492123605 706094414326886534147)
    ·
      rfl

theorem cell_1652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_1652 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1652 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1652 prefixEnd_1652 := by
    exact prefixLift 1652
  have htrace : WordTrace (prefixWord ++ tailWord_1652) baseStart_1652 baseEnd_1652 := by
    simpa [prefixWord, tailWord_1652, baseEnd_1652] using wordTrace_append hprefix tailTrace_1652
  have hstable : (prefixWord ++ tailWord_1652).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652).length < 2 ^ (prefixWord ++ tailWord_1652).sum := by decide
  have hdescent : baseEnd_1652 < baseStart_1652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662 : List Nat := [4, 2, 5]
def baseStart_1662 : Nat := 118140960795 + 1662 * 2 ^ 59
def prefixEnd_1662 : Nat := 4983230072969 + 3 ^ 40 * 1662 * 2
def baseEnd_1662 : Nat := 532776445192377176759

theorem tailTrace_1662 : CollatzResearch.WordTrace tailWord_1662 prefixEnd_1662 532776445192377176759 := by
  unfold tailWord_1662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7577264998291586513905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40412079990888461407493 7577264998291586513905)
  ·
    refine ⟨5682948748718689885429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7577264998291586513905 5682948748718689885429)
    ·
      refine ⟨532776445192377176759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5682948748718689885429 532776445192377176759)
      ·
        rfl

theorem cell_1662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_1662 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1662 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1662 prefixEnd_1662 := by
    exact prefixLift 1662
  have htrace : WordTrace (prefixWord ++ tailWord_1662) baseStart_1662 baseEnd_1662 := by
    simpa [prefixWord, tailWord_1662, baseEnd_1662] using wordTrace_append hprefix tailTrace_1662
  have hstable : (prefixWord ++ tailWord_1662).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662).length < 2 ^ (prefixWord ++ tailWord_1662).sum := by decide
  have hdescent : baseEnd_1662 < baseStart_1662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670 : List Nat := [6, 6]
def baseStart_1670 : Nat := 118140960795 + 1670 * 2 ^ 59
def prefixEnd_1670 : Nat := 4983230072969 + 3 ^ 40 * 1670 * 2
def baseEnd_1670 : Nat := 89223492125024499613

theorem tailTrace_1670 : CollatzResearch.WordTrace tailWord_1670 prefixEnd_1670 89223492125024499613 := by
  unfold tailWord_1670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1903434498667189325077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40606602638233372268309 1903434498667189325077)
  ·
    refine ⟨89223492125024499613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1903434498667189325077 89223492125024499613)
    ·
      rfl

theorem cell_1670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_1670 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1670 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1670 prefixEnd_1670 := by
    exact prefixLift 1670
  have htrace : WordTrace (prefixWord ++ tailWord_1670) baseStart_1670 baseEnd_1670 := by
    simpa [prefixWord, tailWord_1670, baseEnd_1670] using wordTrace_append hprefix tailTrace_1670
  have hstable : (prefixWord ++ tailWord_1670).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670).length < 2 ^ (prefixWord ++ tailWord_1670).sum := by decide
  have hdescent : baseEnd_1670 < baseStart_1670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677 : List Nat := [1, 11]
def baseStart_1677 : Nat := 118140960795 + 1677 * 2 ^ 59
def prefixEnd_1677 : Nat := 4983230072969 + 3 ^ 40 * 1677 * 2
def baseEnd_1677 : Nat := 89597482810532598497

theorem tailTrace_1677 : CollatzResearch.WordTrace tailWord_1677 prefixEnd_1677 89597482810532598497 := by
  unfold tailWord_1677
  simp only [CollatzResearch.WordTrace]
  refine ⟨61165214931990253907285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40776809954660169271523 61165214931990253907285)
  ·
    refine ⟨89597482810532598497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 11 61165214931990253907285 89597482810532598497)
    ·
      rfl

theorem cell_1677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_1677 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1677 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1677 prefixEnd_1677 := by
    exact prefixLift 1677
  have htrace : WordTrace (prefixWord ++ tailWord_1677) baseStart_1677 baseEnd_1677 := by
    simpa [prefixWord, tailWord_1677, baseEnd_1677] using wordTrace_append hprefix tailTrace_1677
  have hstable : (prefixWord ++ tailWord_1677).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677).length < 2 ^ (prefixWord ++ tailWord_1677).sum := by decide
  have hdescent : baseEnd_1677 < baseStart_1677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690 : List Nat := [3, 1, 1, 7]
def baseStart_1690 : Nat := 118140960795 + 1690 * 2 ^ 59
def prefixEnd_1690 : Nat := 4983230072969 + 3 ^ 40 * 1690 * 2
def baseEnd_1690 : Nat := 812628332466857324963

theorem tailTrace_1690 : CollatzResearch.WordTrace tailWord_1690 prefixEnd_1690 812628332466857324963 := by
  unfold tailWord_1690
  simp only [CollatzResearch.WordTrace]
  refine ⟨15409840971223368532631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41092909256595649420349 15409840971223368532631)
  ·
    refine ⟨23114761456835052798947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15409840971223368532631 23114761456835052798947)
    ·
      refine ⟨34672142185252579198421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23114761456835052798947 34672142185252579198421)
      ·
        refine ⟨812628332466857324963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 34672142185252579198421 812628332466857324963)
        ·
          rfl

theorem cell_1690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_1690 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1690 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1690 prefixEnd_1690 := by
    exact prefixLift 1690
  have htrace : WordTrace (prefixWord ++ tailWord_1690) baseStart_1690 baseEnd_1690 := by
    simpa [prefixWord, tailWord_1690, baseEnd_1690] using wordTrace_append hprefix tailTrace_1690
  have hstable : (prefixWord ++ tailWord_1690).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690).length < 2 ^ (prefixWord ++ tailWord_1690).sum := by decide
  have hdescent : baseEnd_1690 < baseStart_1690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702 : List Nat := [9]
def baseStart_1702 : Nat := 118140960795 + 1702 * 2 ^ 59
def prefixEnd_1702 : Nat := 4983230072969 + 3 ^ 40 * 1702 * 2
def baseEnd_1702 : Nat := 242488436880545013935

theorem tailTrace_1702 : CollatzResearch.WordTrace tailWord_1702 prefixEnd_1702 242488436880545013935 := by
  unfold tailWord_1702
  simp only [CollatzResearch.WordTrace]
  refine ⟨242488436880545013935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 9 41384693227613015711573 242488436880545013935)
  ·
    rfl

theorem cell_1702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_1702 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1702 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1702 prefixEnd_1702 := by
    exact prefixLift 1702
  have htrace : WordTrace (prefixWord ++ tailWord_1702) baseStart_1702 baseEnd_1702 := by
    simpa [prefixWord, tailWord_1702, baseEnd_1702] using wordTrace_append hprefix tailTrace_1702
  have hstable : (prefixWord ++ tailWord_1702).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702).length < 2 ^ (prefixWord ++ tailWord_1702).sum := by decide
  have hdescent : baseEnd_1702 < baseStart_1702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703 : List Nat := [1, 1, 6, 4]
def baseStart_1703 : Nat := 118140960795 + 1703 * 2 ^ 59
def prefixEnd_1703 : Nat := 4983230072969 + 3 ^ 40 * 1703 * 2
def baseEnd_1703 : Nat := 818879319638921263453

theorem tailTrace_1703 : CollatzResearch.WordTrace tailWord_1703 prefixEnd_1703 818879319638921263453 := by
  unfold tailWord_1703
  simp only [CollatzResearch.WordTrace]
  refine ⟨62113512837796694353763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41409008558531129569175 62113512837796694353763)
  ·
    refine ⟨93170269256695041530645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62113512837796694353763 93170269256695041530645)
    ·
      refine ⟨4367356371407580071749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93170269256695041530645 4367356371407580071749)
      ·
        refine ⟨818879319638921263453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4367356371407580071749 818879319638921263453)
        ·
          rfl

theorem cell_1703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_1703 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1703 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1703 prefixEnd_1703 := by
    exact prefixLift 1703
  have htrace : WordTrace (prefixWord ++ tailWord_1703) baseStart_1703 baseEnd_1703 := by
    simpa [prefixWord, tailWord_1703, baseEnd_1703] using wordTrace_append hprefix tailTrace_1703
  have hstable : (prefixWord ++ tailWord_1703).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703).length < 2 ^ (prefixWord ++ tailWord_1703).sum := by decide
  have hdescent : baseEnd_1703 < baseStart_1703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716 : List Nat := [2, 5, 5]
def baseStart_1716 : Nat := 118140960795 + 1716 * 2 ^ 59
def prefixEnd_1716 : Nat := 4983230072969 + 3 ^ 40 * 1716 * 2
def baseEnd_1716 : Nat := 275043435603661733981

theorem tailTrace_1716 : CollatzResearch.WordTrace tailWord_1716 prefixEnd_1716 275043435603661733981 := by
  unfold tailWord_1716
  simp only [CollatzResearch.WordTrace]
  refine ⟨31293830895349957288501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41725107860466609718001 31293830895349957288501)
  ·
    refine ⟨2933796646439058495797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31293830895349957288501 2933796646439058495797)
    ·
      refine ⟨275043435603661733981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2933796646439058495797 275043435603661733981)
      ·
        rfl

theorem cell_1716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_1716 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1716 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1716 prefixEnd_1716 := by
    exact prefixLift 1716
  have htrace : WordTrace (prefixWord ++ tailWord_1716) baseStart_1716 baseEnd_1716 := by
    simpa [prefixWord, tailWord_1716, baseEnd_1716] using wordTrace_append hprefix tailTrace_1716
  have hstable : (prefixWord ++ tailWord_1716).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716).length < 2 ^ (prefixWord ++ tailWord_1716).sum := by decide
  have hdescent : baseEnd_1716 < baseStart_1716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1729 : List Nat := [1, 2, 6, 3]
def baseStart_1729 : Nat := 118140960795 + 1729 * 2 ^ 59
def prefixEnd_1729 : Nat := 4983230072969 + 3 ^ 40 * 1729 * 2
def baseEnd_1729 : Nat := 831381293983049140433

theorem tailTrace_1729 : CollatzResearch.WordTrace tailWord_1729 prefixEnd_1729 831381293983049140433 := by
  unfold tailWord_1729
  simp only [CollatzResearch.WordTrace]
  refine ⟨63061810743603134800241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42041207162402089866827 63061810743603134800241)
  ·
    refine ⟨47296358057702351100181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63061810743603134800241 47296358057702351100181)
    ·
      refine ⟨2217016783954797707821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47296358057702351100181 2217016783954797707821)
      ·
        refine ⟨831381293983049140433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2217016783954797707821 831381293983049140433)
        ·
          rfl

theorem cell_1729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_1729 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1729 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1729 prefixEnd_1729 := by
    exact prefixLift 1729
  have htrace : WordTrace (prefixWord ++ tailWord_1729) baseStart_1729 baseEnd_1729 := by
    simpa [prefixWord, tailWord_1729, baseEnd_1729] using wordTrace_append hprefix tailTrace_1729
  have hstable : (prefixWord ++ tailWord_1729).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1729).length < 2 ^ (prefixWord ++ tailWord_1729).sum := by decide
  have hdescent : baseEnd_1729 < baseStart_1729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749 : List Nat := [1, 3, 2, 6]
def baseStart_1749 : Nat := 118140960795 + 1749 * 2 ^ 59
def prefixEnd_1749 : Nat := 4983230072969 + 3 ^ 40 * 1749 * 2
def baseEnd_1749 : Nat := 840998197324685968879

theorem tailTrace_1749 : CollatzResearch.WordTrace tailWord_1749 prefixEnd_1749 840998197324685968879 := by
  unfold tailWord_1749
  simp only [CollatzResearch.WordTrace]
  refine ⟨63791270671146550528301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42527513780764367018867 63791270671146550528301)
  ·
    refine ⟨23921726501679956448113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63791270671146550528301 23921726501679956448113)
    ·
      refine ⟨17941294876259967336085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23921726501679956448113 17941294876259967336085)
      ·
        refine ⟨840998197324685968879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17941294876259967336085 840998197324685968879)
        ·
          rfl

theorem cell_1749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_1749 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1749 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1749 prefixEnd_1749 := by
    exact prefixLift 1749
  have htrace : WordTrace (prefixWord ++ tailWord_1749) baseStart_1749 baseEnd_1749 := by
    simpa [prefixWord, tailWord_1749, baseEnd_1749] using wordTrace_append hprefix tailTrace_1749
  have hstable : (prefixWord ++ tailWord_1749).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749).length < 2 ^ (prefixWord ++ tailWord_1749).sum := by decide
  have hdescent : baseEnd_1749 < baseStart_1749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758 : List Nat := [4, 6]
def baseStart_1758 : Nat := 118140960795 + 1758 * 2 ^ 59
def prefixEnd_1758 : Nat := 4983230072969 + 3 ^ 40 * 1758 * 2
def baseEnd_1758 : Nat := 375700357257076685191

theorem tailTrace_1758 : CollatzResearch.WordTrace tailWord_1758 prefixEnd_1758 375700357257076685191 := by
  unfold tailWord_1758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8014940954817635950741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42746351759027391737285 8014940954817635950741)
  ·
    refine ⟨375700357257076685191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8014940954817635950741 375700357257076685191)
    ·
      rfl

theorem cell_1758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_1758 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1758 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1758 prefixEnd_1758 := by
    exact prefixLift 1758
  have htrace : WordTrace (prefixWord ++ tailWord_1758) baseStart_1758 baseEnd_1758 := by
    simpa [prefixWord, tailWord_1758, baseEnd_1758] using wordTrace_append hprefix tailTrace_1758
  have hstable : (prefixWord ++ tailWord_1758).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758).length < 2 ^ (prefixWord ++ tailWord_1758).sum := by decide
  have hdescent : baseEnd_1758 < baseStart_1758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762 : List Nat := [3, 3, 6]
def baseStart_1762 : Nat := 118140960795 + 1762 * 2 ^ 59
def prefixEnd_1762 : Nat := 4983230072969 + 3 ^ 40 * 1762 * 2
def baseEnd_1762 : Nat := 282416394832249969123

theorem tailTrace_1762 : CollatzResearch.WordTrace tailWord_1762 prefixEnd_1762 282416394832249969123 := by
  unfold tailWord_1762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16066354906012442687885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42843613082699847167693 16066354906012442687885)
  ·
    refine ⟨6024883089754666007957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16066354906012442687885 6024883089754666007957)
    ·
      refine ⟨282416394832249969123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6024883089754666007957 282416394832249969123)
      ·
        rfl

theorem cell_1762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_1762 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1762 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1762 prefixEnd_1762 := by
    exact prefixLift 1762
  have htrace : WordTrace (prefixWord ++ tailWord_1762) baseStart_1762 baseEnd_1762 := by
    simpa [prefixWord, tailWord_1762, baseEnd_1762] using wordTrace_append hprefix tailTrace_1762
  have hstable : (prefixWord ++ tailWord_1762).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762).length < 2 ^ (prefixWord ++ tailWord_1762).sum := by decide
  have hdescent : baseEnd_1762 < baseStart_1762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766 : List Nat := [7]
def baseStart_1766 : Nat := 118140960795 + 1766 * 2 ^ 59
def prefixEnd_1766 : Nat := 4983230072969 + 3 ^ 40 * 1766 * 2
def baseEnd_1766 : Nat := 1006426743899350842143

theorem tailTrace_1766 : CollatzResearch.WordTrace tailWord_1766 prefixEnd_1766 1006426743899350842143 := by
  unfold tailWord_1766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1006426743899350842143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 42940874406372302598101 1006426743899350842143)
  ·
    rfl

theorem cell_1766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1766 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1766 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1766 prefixEnd_1766 := by
    exact prefixLift 1766
  have htrace : WordTrace (prefixWord ++ tailWord_1766) baseStart_1766 baseEnd_1766 := by
    simpa [prefixWord, tailWord_1766, baseEnd_1766] using wordTrace_append hprefix tailTrace_1766
  have hstable : (prefixWord ++ tailWord_1766).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766).length < 2 ^ (prefixWord ++ tailWord_1766).sum := by decide
  have hdescent : baseEnd_1766 < baseStart_1766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781 : List Nat := [1, 3, 6, 2]
def baseStart_1781 : Nat := 118140960795 + 1781 * 2 ^ 59
def prefixEnd_1781 : Nat := 4983230072969 + 3 ^ 40 * 1781 * 2
def baseEnd_1781 : Nat := 856385242671304894393

theorem tailTrace_1781 : CollatzResearch.WordTrace tailWord_1781 prefixEnd_1781 856385242671304894393 := by
  unfold tailWord_1781
  simp only [CollatzResearch.WordTrace]
  refine ⟨64958406555216015693197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43305604370144010462131 64958406555216015693197)
  ·
    refine ⟨24359402458206005884949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64958406555216015693197 24359402458206005884949)
    ·
      refine ⟨1141846990228406525857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24359402458206005884949 1141846990228406525857)
      ·
        refine ⟨856385242671304894393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1141846990228406525857 856385242671304894393)
        ·
          rfl

theorem cell_1781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_1781 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1781 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1781 prefixEnd_1781 := by
    exact prefixLift 1781
  have htrace : WordTrace (prefixWord ++ tailWord_1781) baseStart_1781 baseEnd_1781 := by
    simpa [prefixWord, tailWord_1781, baseEnd_1781] using wordTrace_append hprefix tailTrace_1781
  have hstable : (prefixWord ++ tailWord_1781).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781).length < 2 ^ (prefixWord ++ tailWord_1781).sum := by decide
  have hdescent : baseEnd_1781 < baseStart_1781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814 : List Nat := [5, 4]
def baseStart_1814 : Nat := 118140960795 + 1814 * 2 ^ 59
def prefixEnd_1814 : Nat := 4983230072969 + 3 ^ 40 * 1814 * 2
def baseEnd_1814 : Nat := 775336118386671698959

theorem tailTrace_1814 : CollatzResearch.WordTrace tailWord_1814 prefixEnd_1814 775336118386671698959 := by
  unfold tailWord_1814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4135125964728915727781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44108010290441767762997 4135125964728915727781)
  ·
    refine ⟨775336118386671698959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4135125964728915727781 775336118386671698959)
    ·
      rfl

theorem cell_1814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_1814 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1814 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1814 prefixEnd_1814 := by
    exact prefixLift 1814
  have htrace : WordTrace (prefixWord ++ tailWord_1814) baseStart_1814 baseEnd_1814 := by
    simpa [prefixWord, tailWord_1814, baseEnd_1814] using wordTrace_append hprefix tailTrace_1814
  have hstable : (prefixWord ++ tailWord_1814).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814).length < 2 ^ (prefixWord ++ tailWord_1814).sum := by decide
  have hdescent : baseEnd_1814 < baseStart_1814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821 : List Nat := [1, 4, 2, 5]
def baseStart_1821 : Nat := 118140960795 + 1821 * 2 ^ 59
def prefixEnd_1821 : Nat := 4983230072969 + 3 ^ 40 * 1821 * 2
def baseEnd_1821 : Nat := 875619049354578551285

theorem tailTrace_1821 : CollatzResearch.WordTrace tailWord_1821 prefixEnd_1821 875619049354578551285 := by
  unfold tailWord_1821
  simp only [CollatzResearch.WordTrace]
  refine ⟨66417326410302847149317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44278217606868564766211 66417326410302847149317)
  ·
    refine ⟨12453248701931783840497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66417326410302847149317 12453248701931783840497)
    ·
      refine ⟨9339936526448837880373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12453248701931783840497 9339936526448837880373)
      ·
        refine ⟨875619049354578551285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9339936526448837880373 875619049354578551285)
        ·
          rfl

theorem cell_1821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_1821 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1821 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1821 prefixEnd_1821 := by
    exact prefixLift 1821
  have htrace : WordTrace (prefixWord ++ tailWord_1821) baseStart_1821 baseEnd_1821 := by
    simpa [prefixWord, tailWord_1821, baseEnd_1821] using wordTrace_append hprefix tailTrace_1821
  have hstable : (prefixWord ++ tailWord_1821).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821).length < 2 ^ (prefixWord ++ tailWord_1821).sum := by decide
  have hdescent : baseEnd_1821 < baseStart_1821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830 : List Nat := [8]
def baseStart_1830 : Nat := 118140960795 + 1830 * 2 ^ 59
def prefixEnd_1830 : Nat := 4983230072969 + 3 ^ 40 * 1830 * 2
def baseEnd_1830 : Nat := 521449870138260814273

theorem tailTrace_1830 : CollatzResearch.WordTrace tailWord_1830 prefixEnd_1830 521449870138260814273 := by
  unfold tailWord_1830
  simp only [CollatzResearch.WordTrace]
  refine ⟨521449870138260814273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 44497055585131589484629 521449870138260814273)
  ·
    rfl

theorem cell_1830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1830 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1830 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1830 prefixEnd_1830 := by
    exact prefixLift 1830
  have htrace : WordTrace (prefixWord ++ tailWord_1830) baseStart_1830 baseEnd_1830 := by
    simpa [prefixWord, tailWord_1830, baseEnd_1830] using wordTrace_append hprefix tailTrace_1830
  have hstable : (prefixWord ++ tailWord_1830).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830).length < 2 ^ (prefixWord ++ tailWord_1830).sum := by decide
  have hdescent : baseEnd_1830 < baseStart_1830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834 : List Nat := [3, 1, 4, 4]
def baseStart_1834 : Nat := 118140960795 + 1834 * 2 ^ 59
def prefixEnd_1834 : Nat := 4983230072969 + 3 ^ 40 * 1834 * 2
def baseEnd_1834 : Nat := 881870036526642489775

theorem tailTrace_1834 : CollatzResearch.WordTrace tailWord_1834 prefixEnd_1834 881870036526642489775 := by
  unfold tailWord_1834
  simp only [CollatzResearch.WordTrace]
  refine ⟨16722868840801516843139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44594316908804044915037 16722868840801516843139)
  ·
    refine ⟨25084303261202275264709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16722868840801516843139 25084303261202275264709)
    ·
      refine ⟨4703306861475426612133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25084303261202275264709 4703306861475426612133)
      ·
        refine ⟨881870036526642489775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4703306861475426612133 881870036526642489775)
        ·
          rfl

theorem cell_1834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_1834 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1834 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1834 prefixEnd_1834 := by
    exact prefixLift 1834
  have htrace : WordTrace (prefixWord ++ tailWord_1834) baseStart_1834 baseEnd_1834 := by
    simpa [prefixWord, tailWord_1834, baseEnd_1834] using wordTrace_append hprefix tailTrace_1834
  have hstable : (prefixWord ++ tailWord_1834).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834).length < 2 ^ (prefixWord ++ tailWord_1834).sum := by decide
  have hdescent : baseEnd_1834 < baseStart_1834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858 : List Nat := [3, 7]
def baseStart_1858 : Nat := 118140960795 + 1858 * 2 ^ 59
def prefixEnd_1858 : Nat := 4983230072969 + 3 ^ 40 * 1858 * 2
def baseEnd_1858 : Nat := 397071253571825192849

theorem tailTrace_1858 : CollatzResearch.WordTrace tailWord_1858 prefixEnd_1858 397071253571825192849 := by
  unfold tailWord_1858
  simp only [CollatzResearch.WordTrace]
  refine ⟨16941706819064541561557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45177884850838777497485 16941706819064541561557)
  ·
    refine ⟨397071253571825192849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 16941706819064541561557 397071253571825192849)
    ·
      rfl

theorem cell_1858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_1858 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1858 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1858 prefixEnd_1858 := by
    exact prefixLift 1858
  have htrace : WordTrace (prefixWord ++ tailWord_1858) baseStart_1858 baseEnd_1858 := by
    simpa [prefixWord, tailWord_1858, baseEnd_1858] using wordTrace_append hprefix tailTrace_1858
  have hstable : (prefixWord ++ tailWord_1858).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858).length < 2 ^ (prefixWord ++ tailWord_1858).sum := by decide
  have hdescent : baseEnd_1858 < baseStart_1858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860 : List Nat := [2, 3, 4, 3]
def baseStart_1860 : Nat := 118140960795 + 1860 * 2 ^ 59
def prefixEnd_1860 : Nat := 4983230072969 + 3 ^ 40 * 1860 * 2
def baseEnd_1860 : Nat := 894372010870770366755

theorem tailTrace_1860 : CollatzResearch.WordTrace tailWord_1860 prefixEnd_1860 894372010870770366755 := by
  unfold tailWord_1860
  simp only [CollatzResearch.WordTrace]
  refine ⟨33919886634506253909517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45226515512675005212689 33919886634506253909517)
  ·
    refine ⟨12719957487939845216069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33919886634506253909517 12719957487939845216069)
    ·
      refine ⟨2384992028988720978013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12719957487939845216069 2384992028988720978013)
      ·
        refine ⟨894372010870770366755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2384992028988720978013 894372010870770366755)
        ·
          rfl

theorem cell_1860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_1860 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1860 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1860 prefixEnd_1860 := by
    exact prefixLift 1860
  have htrace : WordTrace (prefixWord ++ tailWord_1860) baseStart_1860 baseEnd_1860 := by
    simpa [prefixWord, tailWord_1860, baseEnd_1860] using wordTrace_append hprefix tailTrace_1860
  have hstable : (prefixWord ++ tailWord_1860).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860).length < 2 ^ (prefixWord ++ tailWord_1860).sum := by decide
  have hdescent : baseEnd_1860 < baseStart_1860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878 : List Nat := [5, 2, 4]
def baseStart_1878 : Nat := 118140960795 + 1878 * 2 ^ 59
def prefixEnd_1878 : Nat := 4983230072969 + 3 ^ 40 * 1878 * 2
def baseEnd_1878 : Nat := 602018149252162341571

theorem tailTrace_1878 : CollatzResearch.WordTrace tailWord_1878 prefixEnd_1878 602018149252162341571 := by
  unfold tailWord_1878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4281017950237598873393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45664191469201054649525 4281017950237598873393)
  ·
    refine ⟨3210763462678199155045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4281017950237598873393 3210763462678199155045)
    ·
      refine ⟨602018149252162341571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3210763462678199155045 602018149252162341571)
      ·
        rfl

theorem cell_1878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_1878 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1878 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1878 prefixEnd_1878 := by
    exact prefixLift 1878
  have htrace : WordTrace (prefixWord ++ tailWord_1878) baseStart_1878 baseEnd_1878 := by
    simpa [prefixWord, tailWord_1878, baseEnd_1878] using wordTrace_append hprefix tailTrace_1878
  have hstable : (prefixWord ++ tailWord_1878).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878).length < 2 ^ (prefixWord ++ tailWord_1878).sum := by decide
  have hdescent : baseEnd_1878 < baseStart_1878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885 : List Nat := [1, 4, 6]
def baseStart_1885 : Nat := 118140960795 + 1885 * 2 ^ 59
def prefixEnd_1885 : Nat := 4983230072969 + 3 ^ 40 * 1885 * 2
def baseEnd_1885 : Nat := 604262093365210934875

theorem tailTrace_1885 : CollatzResearch.WordTrace tailWord_1885 prefixEnd_1885 604262093365210934875 := by
  unfold tailWord_1885
  simp only [CollatzResearch.WordTrace]
  refine ⟨68751598178441777479109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45834398785627851652739 68751598178441777479109)
  ·
    refine ⟨12890924658457833277333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68751598178441777479109 12890924658457833277333)
    ·
      refine ⟨604262093365210934875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12890924658457833277333 604262093365210934875)
      ·
        rfl

theorem cell_1885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_1885 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1885 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1885 prefixEnd_1885 := by
    exact prefixLift 1885
  have htrace : WordTrace (prefixWord ++ tailWord_1885) baseStart_1885 baseEnd_1885 := by
    simpa [prefixWord, tailWord_1885, baseEnd_1885] using wordTrace_append hprefix tailTrace_1885
  have hstable : (prefixWord ++ tailWord_1885).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885).length < 2 ^ (prefixWord ++ tailWord_1885).sum := by decide
  have hdescent : baseEnd_1885 < baseStart_1885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886 : List Nat := [4, 4, 4]
def baseStart_1886 : Nat := 118140960795 + 1886 * 2 ^ 59
def prefixEnd_1886 : Nat := 4983230072969 + 3 ^ 40 * 1886 * 2
def baseEnd_1886 : Nat := 302291328404966081245

theorem tailTrace_1886 : CollatzResearch.WordTrace tailWord_1886 prefixEnd_1886 302291328404966081245 := by
  unfold tailWord_1886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8598508896852368533189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45858714116545965510341 8598508896852368533189)
  ·
    refine ⟨1612220418159819099973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8598508896852368533189 1612220418159819099973)
    ·
      refine ⟨302291328404966081245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1612220418159819099973 302291328404966081245)
      ·
        rfl

theorem cell_1886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_1886 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1886 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1886 prefixEnd_1886 := by
    exact prefixLift 1886
  have htrace : WordTrace (prefixWord ++ tailWord_1886) baseStart_1886 baseEnd_1886 := by
    simpa [prefixWord, tailWord_1886, baseEnd_1886] using wordTrace_append hprefix tailTrace_1886
  have hstable : (prefixWord ++ tailWord_1886).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886).length < 2 ^ (prefixWord ++ tailWord_1886).sum := by decide
  have hdescent : baseEnd_1886 < baseStart_1886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894 : List Nat := [7]
def baseStart_1894 : Nat := 118140960795 + 1894 * 2 ^ 59
def prefixEnd_1894 : Nat := 4983230072969 + 3 ^ 40 * 1894 * 2
def baseEnd_1894 : Nat := 1079372736653692414949

theorem tailTrace_1894 : CollatzResearch.WordTrace tailWord_1894 prefixEnd_1894 1079372736653692414949 := by
  unfold tailWord_1894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1079372736653692414949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 46053236763890876371157 1079372736653692414949)
  ·
    rfl

theorem cell_1894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1894 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1894 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1894 prefixEnd_1894 := by
    exact prefixLift 1894
  have htrace : WordTrace (prefixWord ++ tailWord_1894) baseStart_1894 baseEnd_1894 := by
    simpa [prefixWord, tailWord_1894, baseEnd_1894] using wordTrace_append hprefix tailTrace_1894
  have hstable : (prefixWord ++ tailWord_1894).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894).length < 2 ^ (prefixWord ++ tailWord_1894).sum := by decide
  have hdescent : baseEnd_1894 < baseStart_1894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908 : List Nat := [2, 9]
def baseStart_1908 : Nat := 118140960795 + 1908 * 2 ^ 59
def prefixEnd_1908 : Nat := 4983230072969 + 3 ^ 40 * 1908 * 2
def baseEnd_1908 : Nat := 203878350864599723339

theorem tailTrace_1908 : CollatzResearch.WordTrace tailWord_1908 prefixEnd_1908 203878350864599723339 := by
  unfold tailWord_1908
  simp only [CollatzResearch.WordTrace]
  refine ⟨34795238547558352783189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46393651396744470377585 34795238547558352783189)
  ·
    refine ⟨203878350864599723339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 9 34795238547558352783189 203878350864599723339)
    ·
      rfl

theorem cell_1908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_1908 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1908 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1908 prefixEnd_1908 := by
    exact prefixLift 1908
  have htrace : WordTrace (prefixWord ++ tailWord_1908) baseStart_1908 baseEnd_1908 := by
    simpa [prefixWord, tailWord_1908, baseEnd_1908] using wordTrace_append hprefix tailTrace_1908
  have hstable : (prefixWord ++ tailWord_1908).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908).length < 2 ^ (prefixWord ++ tailWord_1908).sum := by decide
  have hdescent : baseEnd_1908 < baseStart_1908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926 : List Nat := [6, 3]
def baseStart_1926 : Nat := 118140960795 + 1926 * 2 ^ 59
def prefixEnd_1926 : Nat := 4983230072969 + 3 ^ 40 * 1926 * 2
def baseEnd_1926 : Nat := 823206926131708356113

theorem tailTrace_1926 : CollatzResearch.WordTrace tailWord_1926 prefixEnd_1926 823206926131708356113 := by
  unfold tailWord_1926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2195218469684555616301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46831327353270519814421 2195218469684555616301)
  ·
    refine ⟨823206926131708356113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2195218469684555616301 823206926131708356113)
    ·
      rfl

theorem cell_1926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_1926 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1926 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1926 prefixEnd_1926 := by
    exact prefixLift 1926
  have htrace : WordTrace (prefixWord ++ tailWord_1926) baseStart_1926 baseEnd_1926 := by
    simpa [prefixWord, tailWord_1926, baseEnd_1926] using wordTrace_append hprefix tailTrace_1926
  have hstable : (prefixWord ++ tailWord_1926).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926).length < 2 ^ (prefixWord ++ tailWord_1926).sum := by decide
  have hdescent : baseEnd_1926 < baseStart_1926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933 : List Nat := [1, 8]
def baseStart_1933 : Nat := 118140960795 + 1933 * 2 ^ 59
def prefixEnd_1933 : Nat := 4983230072969 + 3 ^ 40 * 1933 * 2
def baseEnd_1933 : Nat := 826198851615773147185

theorem tailTrace_1933 : CollatzResearch.WordTrace tailWord_1933 prefixEnd_1933 826198851615773147185 := by
  unfold tailWord_1933
  simp only [CollatzResearch.WordTrace]
  refine ⟨70502302004545975226453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47001534669697316817635 70502302004545975226453)
  ·
    refine ⟨826198851615773147185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 70502302004545975226453 826198851615773147185)
    ·
      rfl

theorem cell_1933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_1933 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1933 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1933 prefixEnd_1933 := by
    exact prefixLift 1933
  have htrace : WordTrace (prefixWord ++ tailWord_1933) baseStart_1933 baseEnd_1933 := by
    simpa [prefixWord, tailWord_1933, baseEnd_1933] using wordTrace_append hprefix tailTrace_1933
  have hstable : (prefixWord ++ tailWord_1933).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933).length < 2 ^ (prefixWord ++ tailWord_1933).sum := by decide
  have hdescent : baseEnd_1933 < baseStart_1933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958 : List Nat := [10]
def baseStart_1958 : Nat := 118140960795 + 1958 * 2 ^ 59
def prefixEnd_1958 : Nat := 4983230072969 + 3 ^ 40 * 1958 * 2
def baseEnd_1958 : Nat := 139480716628857900169

theorem tailTrace_1958 : CollatzResearch.WordTrace tailWord_1958 prefixEnd_1958 139480716628857900169 := by
  unfold tailWord_1958
  simp only [CollatzResearch.WordTrace]
  refine ⟨139480716628857900169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 10 47609417942650163257685 139480716628857900169)
  ·
    rfl

theorem cell_1958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_1958 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1958 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1958 prefixEnd_1958 := by
    exact prefixLift 1958
  have htrace : WordTrace (prefixWord ++ tailWord_1958) baseStart_1958 baseEnd_1958 := by
    simpa [prefixWord, tailWord_1958, baseEnd_1958] using wordTrace_append hprefix tailTrace_1958
  have hstable : (prefixWord ++ tailWord_1958).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958).length < 2 ^ (prefixWord ++ tailWord_1958).sum := by decide
  have hdescent : baseEnd_1958 < baseStart_1958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965 : List Nat := [1, 5, 2, 4]
def baseStart_1965 : Nat := 118140960795 + 1965 * 2 ^ 59
def prefixEnd_1965 : Nat := 4983230072969 + 3 ^ 40 * 1965 * 2
def baseEnd_1965 : Nat := 944860753414363716097

theorem tailTrace_1965 : CollatzResearch.WordTrace tailWord_1965 prefixEnd_1965 944860753414363716097 := by
  unfold tailWord_1965
  simp only [CollatzResearch.WordTrace]
  refine ⟨71669437888615440391349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47779625259076960260899 71669437888615440391349)
  ·
    refine ⟨6719009802057697536689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71669437888615440391349 6719009802057697536689)
    ·
      refine ⟨5039257351543273152517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6719009802057697536689 5039257351543273152517)
      ·
        refine ⟨944860753414363716097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5039257351543273152517 944860753414363716097)
        ·
          rfl

theorem cell_1965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_1965 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1965 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1965 prefixEnd_1965 := by
    exact prefixLift 1965
  have htrace : WordTrace (prefixWord ++ tailWord_1965) baseStart_1965 baseEnd_1965 := by
    simpa [prefixWord, tailWord_1965, baseEnd_1965] using wordTrace_append hprefix tailTrace_1965
  have hstable : (prefixWord ++ tailWord_1965).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965).length < 2 ^ (prefixWord ++ tailWord_1965).sum := by decide
  have hdescent : baseEnd_1965 < baseStart_1965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985 : List Nat := [1, 2, 9]
def baseStart_1985 : Nat := 118140960795 + 1985 * 2 ^ 59
def prefixEnd_1985 : Nat := 4983230072969 + 3 ^ 40 * 1985 * 2
def baseEnd_1985 : Nat := 318159218918666848181

theorem tailTrace_1985 : CollatzResearch.WordTrace tailWord_1985 prefixEnd_1985 318159218918666848181 := by
  unfold tailWord_1985
  simp only [CollatzResearch.WordTrace]
  refine ⟨72398897816158856119409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48265931877439237412939 72398897816158856119409)
  ·
    refine ⟨54299173362119142089557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72398897816158856119409 54299173362119142089557)
    ·
      refine ⟨318159218918666848181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 9 54299173362119142089557 318159218918666848181)
      ·
        rfl

theorem cell_1985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_1985 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1985 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1985 prefixEnd_1985 := by
    exact prefixLift 1985
  have htrace : WordTrace (prefixWord ++ tailWord_1985) baseStart_1985 baseEnd_1985 := by
    simpa [prefixWord, tailWord_1985, baseEnd_1985] using wordTrace_append hprefix tailTrace_1985
  have hstable : (prefixWord ++ tailWord_1985).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985).length < 2 ^ (prefixWord ++ tailWord_1985).sum := by decide
  have hdescent : baseEnd_1985 < baseStart_1985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986 : List Nat := [3, 5, 3]
def baseStart_1986 : Nat := 118140960795 + 1986 * 2 ^ 59
def prefixEnd_1986 : Nat := 4983230072969 + 3 ^ 40 * 1986 * 2
def baseEnd_1986 : Nat := 636639001282054923977

theorem tailTrace_1986 : CollatzResearch.WordTrace tailWord_1986 prefixEnd_1986 636639001282054923977 := by
  unfold tailWord_1986
  simp only [CollatzResearch.WordTrace]
  refine ⟨18108842703134006726453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48290247208357351270541 18108842703134006726453)
  ·
    refine ⟨1697704003418813130605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18108842703134006726453 1697704003418813130605)
    ·
      refine ⟨636639001282054923977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1697704003418813130605 636639001282054923977)
      ·
        rfl

theorem cell_1986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_1986 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1986 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1986 prefixEnd_1986 := by
    exact prefixLift 1986
  have htrace : WordTrace (prefixWord ++ tailWord_1986) baseStart_1986 baseEnd_1986 := by
    simpa [prefixWord, tailWord_1986, baseEnd_1986] using wordTrace_append hprefix tailTrace_1986
  have hstable : (prefixWord ++ tailWord_1986).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986).length < 2 ^ (prefixWord ++ tailWord_1986).sum := by decide
  have hdescent : baseEnd_1986 < baseStart_1986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990 : List Nat := [6, 1, 3, 2]
def baseStart_1990 : Nat := 118140960795 + 1990 * 2 ^ 59
def prefixEnd_1990 : Nat := 4983230072969 + 3 ^ 40 * 1990 * 2
def baseEnd_1990 : Nat := 956881882591409751655

theorem tailTrace_1990 : CollatzResearch.WordTrace tailWord_1990 prefixEnd_1990 956881882591409751655 := by
  unfold tailWord_1990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2268164462438897189107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48387508532029806700949 2268164462438897189107)
  ·
    refine ⟨3402246693658345783661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2268164462438897189107 3402246693658345783661)
    ·
      refine ⟨1275842510121879668873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3402246693658345783661 1275842510121879668873)
      ·
        refine ⟨956881882591409751655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1275842510121879668873 956881882591409751655)
        ·
          rfl

theorem cell_1990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_1990 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1990 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1990 prefixEnd_1990 := by
    exact prefixLift 1990
  have htrace : WordTrace (prefixWord ++ tailWord_1990) baseStart_1990 baseEnd_1990 := by
    simpa [prefixWord, tailWord_1990, baseEnd_1990] using wordTrace_append hprefix tailTrace_1990
  have hstable : (prefixWord ++ tailWord_1990).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990).length < 2 ^ (prefixWord ++ tailWord_1990).sum := by decide
  have hdescent : baseEnd_1990 < baseStart_1990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997 : List Nat := [1, 6, 3, 2]
def baseStart_1997 : Nat := 118140960795 + 1997 * 2 ^ 59
def prefixEnd_1997 : Nat := 4983230072969 + 3 ^ 40 * 1997 * 2
def baseEnd_1997 : Nat := 960247798760982641611

theorem tailTrace_1997 : CollatzResearch.WordTrace tailWord_1997 prefixEnd_1997 960247798760982641611 := by
  unfold tailWord_1997
  simp only [CollatzResearch.WordTrace]
  refine ⟨72836573772684905556245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48557715848456603704163 72836573772684905556245)
  ·
    refine ⟨3414214395594604947949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72836573772684905556245 3414214395594604947949)
    ·
      refine ⟨1280330398347976855481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3414214395594604947949 1280330398347976855481)
      ·
        refine ⟨960247798760982641611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1280330398347976855481 960247798760982641611)
        ·
          rfl

theorem cell_1997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_1997 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_1997 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_1997 prefixEnd_1997 := by
    exact prefixLift 1997
  have htrace : WordTrace (prefixWord ++ tailWord_1997) baseStart_1997 baseEnd_1997 := by
    simpa [prefixWord, tailWord_1997, baseEnd_1997] using wordTrace_append hprefix tailTrace_1997
  have hstable : (prefixWord ++ tailWord_1997).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997).length < 2 ^ (prefixWord ++ tailWord_1997).sum := by decide
  have hdescent : baseEnd_1997 < baseStart_1997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014 : List Nat := [4, 5]
def baseStart_2014 : Nat := 118140960795 + 2014 * 2 ^ 59
def prefixEnd_2014 : Nat := 4983230072969 + 3 ^ 40 * 2014 * 2
def baseEnd_2014 : Nat := 860819703645665729591

theorem tailTrace_2014 : CollatzResearch.WordTrace tailWord_2014 prefixEnd_2014 860819703645665729591 := by
  unfold tailWord_2014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9182076838887101115637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48971076474064539283397 9182076838887101115637)
  ·
    refine ⟨860819703645665729591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9182076838887101115637 860819703645665729591)
    ·
      rfl

theorem cell_2014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_2014 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2014 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2014 prefixEnd_2014 := by
    exact prefixLift 2014
  have htrace : WordTrace (prefixWord ++ tailWord_2014) baseStart_2014 baseEnd_2014 := by
    simpa [prefixWord, tailWord_2014, baseEnd_2014] using wordTrace_append hprefix tailTrace_2014
  have hstable : (prefixWord ++ tailWord_2014).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014).length < 2 ^ (prefixWord ++ tailWord_2014).sum := by decide
  have hdescent : baseEnd_2014 < baseStart_2014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022 : List Nat := [7]
def baseStart_2022 : Nat := 118140960795 + 2022 * 2 ^ 59
def prefixEnd_2022 : Nat := 4983230072969 + 3 ^ 40 * 2022 * 2
def baseEnd_2022 : Nat := 1152318729408033987755

theorem tailTrace_2022 : CollatzResearch.WordTrace tailWord_2022 prefixEnd_2022 1152318729408033987755 := by
  unfold tailWord_2022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1152318729408033987755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 49165599121409450144213 1152318729408033987755)
  ·
    rfl

theorem cell_2022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2022 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2022 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2022 prefixEnd_2022 := by
    exact prefixLift 2022
  have htrace : WordTrace (prefixWord ++ tailWord_2022) baseStart_2022 baseEnd_2022 := by
    simpa [prefixWord, tailWord_2022, baseEnd_2022] using wordTrace_append hprefix tailTrace_2022
  have hstable : (prefixWord ++ tailWord_2022).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022).length < 2 ^ (prefixWord ++ tailWord_2022).sum := by decide
  have hdescent : baseEnd_2022 < baseStart_2022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036 : List Nat := [2, 6, 2, 2]
def baseStart_2036 : Nat := 118140960795 + 2036 * 2 ^ 59
def prefixEnd_2036 : Nat := 4983230072969 + 3 ^ 40 * 2036 * 2
def baseEnd_2036 : Nat := 979000760277174457081

theorem tailTrace_2036 : CollatzResearch.WordTrace tailWord_2036 prefixEnd_2036 979000760277174457081 := by
  unfold tailWord_2036
  simp only [CollatzResearch.WordTrace]
  refine ⟨37129510315697283112981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49506013754263044150641 37129510315697283112981)
  ·
    refine ⟨1740445796048310145921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37129510315697283112981 1740445796048310145921)
    ·
      refine ⟨1305334347036232609441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1740445796048310145921 1305334347036232609441)
      ·
        refine ⟨979000760277174457081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1305334347036232609441 979000760277174457081)
        ·
          rfl

theorem cell_2036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_2036 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2036 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2036 prefixEnd_2036 := by
    exact prefixLift 2036
  have htrace : WordTrace (prefixWord ++ tailWord_2036) baseStart_2036 baseEnd_2036 := by
    simpa [prefixWord, tailWord_2036, baseEnd_2036] using wordTrace_append hprefix tailTrace_2036
  have hstable : (prefixWord ++ tailWord_2036).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036).length < 2 ^ (prefixWord ++ tailWord_2036).sum := by decide
  have hdescent : baseEnd_2036 < baseStart_2036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037 : List Nat := [1, 3, 5, 3]
def baseStart_2037 : Nat := 118140960795 + 2037 * 2 ^ 59
def prefixEnd_2037 : Nat := 4983230072969 + 3 ^ 40 * 2037 * 2
def baseEnd_2037 : Nat := 979481605444256298503

theorem tailTrace_2037 : CollatzResearch.WordTrace tailWord_2037 prefixEnd_2037 979481605444256298503 := by
  unfold tailWord_2037
  simp only [CollatzResearch.WordTrace]
  refine ⟨74295493627771737012365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49530329085181158008243 74295493627771737012365)
  ·
    refine ⟨27860810110414401379637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74295493627771737012365 27860810110414401379637)
    ·
      refine ⟨2611950947851350129341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27860810110414401379637 2611950947851350129341)
      ·
        refine ⟨979481605444256298503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2611950947851350129341 979481605444256298503)
        ·
          rfl

theorem cell_2037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_2037 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2037 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2037 prefixEnd_2037 := by
    exact prefixLift 2037
  have htrace : WordTrace (prefixWord ++ tailWord_2037) baseStart_2037 baseEnd_2037 := by
    simpa [prefixWord, tailWord_2037, baseEnd_2037] using wordTrace_append hprefix tailTrace_2037
  have hstable : (prefixWord ++ tailWord_2037).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037).length < 2 ^ (prefixWord ++ tailWord_2037).sum := by decide
  have hdescent : baseEnd_2037 < baseStart_2037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050 : List Nat := [3, 4, 1, 4]
def baseStart_2050 : Nat := 118140960795 + 2050 * 2 ^ 59
def prefixEnd_2050 : Nat := 4983230072969 + 3 ^ 40 * 2050 * 2
def baseEnd_2050 : Nat := 985732592616320236993

theorem tailTrace_2050 : CollatzResearch.WordTrace tailWord_2050 prefixEnd_2050 985732592616320236993 := by
  unfold tailWord_2050
  simp only [CollatzResearch.WordTrace]
  refine ⟨18692410645168739308901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49846428387116638157069 18692410645168739308901)
  ·
    refine ⟨3504826995969138620419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18692410645168739308901 3504826995969138620419)
    ·
      refine ⟨5257240493953707930629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3504826995969138620419 5257240493953707930629)
      ·
        refine ⟨985732592616320236993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5257240493953707930629 985732592616320236993)
        ·
          rfl

theorem cell_2050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_2050 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2050 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2050 prefixEnd_2050 := by
    exact prefixLift 2050
  have htrace : WordTrace (prefixWord ++ tailWord_2050) baseStart_2050 baseEnd_2050 := by
    simpa [prefixWord, tailWord_2050, baseEnd_2050] using wordTrace_append hprefix tailTrace_2050
  have hstable : (prefixWord ++ tailWord_2050).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050).length < 2 ^ (prefixWord ++ tailWord_2050).sum := by decide
  have hdescent : baseEnd_2050 < baseStart_2050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070 : List Nat := [5, 7]
def baseStart_2070 : Nat := 118140960795 + 2070 * 2 ^ 59
def prefixEnd_2070 : Nat := 4983230072969 + 3 ^ 40 * 2070 * 2
def baseEnd_2070 : Nat := 110594388439773007271

theorem tailTrace_2070 : CollatzResearch.WordTrace tailWord_2070 prefixEnd_2070 110594388439773007271 := by
  unfold tailWord_2070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4718693906763648310229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50332735005478915309109 4718693906763648310229)
  ·
    refine ⟨110594388439773007271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 4718693906763648310229 110594388439773007271)
    ·
      rfl

theorem cell_2070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_2070 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2070 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2070 prefixEnd_2070 := by
    exact prefixLift 2070
  have htrace : WordTrace (prefixWord ++ tailWord_2070) baseStart_2070 baseEnd_2070 := by
    simpa [prefixWord, tailWord_2070, baseEnd_2070] using wordTrace_append hprefix tailTrace_2070
  have hstable : (prefixWord ++ tailWord_2070).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070).length < 2 ^ (prefixWord ++ tailWord_2070).sum := by decide
  have hdescent : baseEnd_2070 < baseStart_2070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2078 : List Nat := [4, 3, 4]
def baseStart_2078 : Nat := 118140960795 + 2078 * 2 ^ 59
def prefixEnd_2078 : Nat := 4983230072969 + 3 ^ 40 * 2078 * 2
def baseEnd_2078 : Nat := 666130838196407864545

theorem tailTrace_2078 : CollatzResearch.WordTrace tailWord_2078 prefixEnd_2078 666130838196407864545 := by
  unfold tailWord_2078
  simp only [CollatzResearch.WordTrace]
  refine ⟨9473860809904467406861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50527257652823826169925 9473860809904467406861)
  ·
    refine ⟨3552697803714175277573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9473860809904467406861 3552697803714175277573)
    ·
      refine ⟨666130838196407864545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3552697803714175277573 666130838196407864545)
      ·
        rfl

theorem cell_2078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_2078 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2078 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2078 prefixEnd_2078 := by
    exact prefixLift 2078
  have htrace : WordTrace (prefixWord ++ tailWord_2078) baseStart_2078 baseEnd_2078 := by
    simpa [prefixWord, tailWord_2078, baseEnd_2078] using wordTrace_append hprefix tailTrace_2078
  have hstable : (prefixWord ++ tailWord_2078).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2078).length < 2 ^ (prefixWord ++ tailWord_2078).sum := by decide
  have hdescent : baseEnd_2078 < baseStart_2078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086 : List Nat := [8]
def baseStart_2086 : Nat := 118140960795 + 2086 * 2 ^ 59
def prefixEnd_2086 : Nat := 4983230072969 + 3 ^ 40 * 2086 * 2
def baseEnd_2086 : Nat := 594395862892602387079

theorem tailTrace_2086 : CollatzResearch.WordTrace tailWord_2086 prefixEnd_2086 594395862892602387079 := by
  unfold tailWord_2086
  simp only [CollatzResearch.WordTrace]
  refine ⟨594395862892602387079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 50721780300168737030741 594395862892602387079)
  ·
    rfl

theorem cell_2086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_2086 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2086 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2086 prefixEnd_2086 := by
    exact prefixLift 2086
  have htrace : WordTrace (prefixWord ++ tailWord_2086) baseStart_2086 baseEnd_2086 := by
    simpa [prefixWord, tailWord_2086, baseEnd_2086] using wordTrace_append hprefix tailTrace_2086
  have hstable : (prefixWord ++ tailWord_2086).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086).length < 2 ^ (prefixWord ++ tailWord_2086).sum := by decide
  have hdescent : baseEnd_2086 < baseStart_2086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114 : List Nat := [3, 6]
def baseStart_2114 : Nat := 118140960795 + 2114 * 2 ^ 59
def prefixEnd_2114 : Nat := 4983230072969 + 3 ^ 40 * 2114 * 2
def baseEnd_2114 : Nat := 903561496275162744907

theorem tailTrace_2114 : CollatzResearch.WordTrace tailWord_2114 prefixEnd_2114 903561496275162744907 := by
  unfold tailWord_2114
  simp only [CollatzResearch.WordTrace]
  refine ⟨19275978587203471891349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51402609565875925043597 19275978587203471891349)
  ·
    refine ⟨903561496275162744907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19275978587203471891349 903561496275162744907)
    ·
      rfl

theorem cell_2114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_2114 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2114 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2114 prefixEnd_2114 := by
    exact prefixLift 2114
  have htrace : WordTrace (prefixWord ++ tailWord_2114) baseStart_2114 baseEnd_2114 := by
    simpa [prefixWord, tailWord_2114, baseEnd_2114] using wordTrace_append hprefix tailTrace_2114
  have hstable : (prefixWord ++ tailWord_2114).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114).length < 2 ^ (prefixWord ++ tailWord_2114).sum := by decide
  have hdescent : baseEnd_2114 < baseStart_2114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116 : List Nat := [2, 3, 7]
def baseStart_2116 : Nat := 118140960795 + 2116 * 2 ^ 59
def prefixEnd_2116 : Nat := 4983230072969 + 3 ^ 40 * 2116 * 2
def baseEnd_2116 : Nat := 339156124547907256955

theorem tailTrace_2116 : CollatzResearch.WordTrace tailWord_2116 prefixEnd_2116 339156124547907256955 := by
  unfold tailWord_2116
  simp only [CollatzResearch.WordTrace]
  refine ⟨38588430170784114569101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51451240227712152758801 38588430170784114569101)
  ·
    refine ⟨14470661314044042963413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38588430170784114569101 14470661314044042963413)
    ·
      refine ⟨339156124547907256955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 14470661314044042963413 339156124547907256955)
      ·
        rfl

theorem cell_2116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_2116 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2116 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2116 prefixEnd_2116 := by
    exact prefixLift 2116
  have htrace : WordTrace (prefixWord ++ tailWord_2116) baseStart_2116 baseEnd_2116 := by
    simpa [prefixWord, tailWord_2116, baseEnd_2116] using wordTrace_append hprefix tailTrace_2116
  have hstable : (prefixWord ++ tailWord_2116).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116).length < 2 ^ (prefixWord ++ tailWord_2116).sum := by decide
  have hdescent : baseEnd_2116 < baseStart_2116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150 : List Nat := [7]
def baseStart_2150 : Nat := 118140960795 + 2150 * 2 ^ 59
def prefixEnd_2150 : Nat := 4983230072969 + 3 ^ 40 * 2150 * 2
def baseEnd_2150 : Nat := 1225264722162375560561

theorem tailTrace_2150 : CollatzResearch.WordTrace tailWord_2150 prefixEnd_2150 1225264722162375560561 := by
  unfold tailWord_2150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225264722162375560561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 52277961478928023917269 1225264722162375560561)
  ·
    rfl

theorem cell_2150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2150 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2150 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2150 prefixEnd_2150 := by
    exact prefixLift 2150
  have htrace : WordTrace (prefixWord ++ tailWord_2150) baseStart_2150 baseEnd_2150 := by
    simpa [prefixWord, tailWord_2150, baseEnd_2150] using wordTrace_append hprefix tailTrace_2150
  have hstable : (prefixWord ++ tailWord_2150).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150).length < 2 ^ (prefixWord ++ tailWord_2150).sum := by decide
  have hdescent : baseEnd_2150 < baseStart_2150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164 : List Nat := [2, 7]
def baseStart_2164 : Nat := 118140960795 + 2164 * 2 ^ 59
def prefixEnd_2164 : Nat := 4983230072969 + 3 ^ 40 * 2164 * 2
def baseEnd_2164 : Nat := 924932392589911252565

theorem tailTrace_2164 : CollatzResearch.WordTrace tailWord_2164 prefixEnd_2164 924932392589911252565 := by
  unfold tailWord_2164
  simp only [CollatzResearch.WordTrace]
  refine ⟨39463782083836213442773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52618376111781617923697 39463782083836213442773)
  ·
    refine ⟨924932392589911252565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 39463782083836213442773 924932392589911252565)
    ·
      rfl

theorem cell_2164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_2164 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2164 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2164 prefixEnd_2164 := by
    exact prefixLift 2164
  have htrace : WordTrace (prefixWord ++ tailWord_2164) baseStart_2164 baseEnd_2164 := by
    simpa [prefixWord, tailWord_2164, baseEnd_2164] using wordTrace_append hprefix tailTrace_2164
  have hstable : (prefixWord ++ tailWord_2164).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164).length < 2 ^ (prefixWord ++ tailWord_2164).sum := by decide
  have hdescent : baseEnd_2164 < baseStart_2164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174 : List Nat := [4, 2, 4, 2]
def baseStart_2174 : Nat := 118140960795 + 2174 * 2 ^ 59
def prefixEnd_2174 : Nat := 4983230072969 + 3 ^ 40 * 2174 * 2
def baseEnd_2174 : Nat := 1045357393334468573359

theorem tailTrace_2174 : CollatzResearch.WordTrace tailWord_2174 prefixEnd_2174 1045357393334468573359 := by
  unfold tailWord_2174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9911536766430516843697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52861529420962756499717 9911536766430516843697)
  ·
    refine ⟨7433652574822887632773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9911536766430516843697 7433652574822887632773)
    ·
      refine ⟨1393809857779291431145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7433652574822887632773 1393809857779291431145)
      ·
        refine ⟨1045357393334468573359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1393809857779291431145 1045357393334468573359)
        ·
          rfl

theorem cell_2174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_2174 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2174 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2174 prefixEnd_2174 := by
    exact prefixLift 2174
  have htrace : WordTrace (prefixWord ++ tailWord_2174) baseStart_2174 baseEnd_2174 := by
    simpa [prefixWord, tailWord_2174, baseEnd_2174] using wordTrace_append hprefix tailTrace_2174
  have hstable : (prefixWord ++ tailWord_2174).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174).length < 2 ^ (prefixWord ++ tailWord_2174).sum := by decide
  have hdescent : baseEnd_2174 < baseStart_2174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182 : List Nat := [6, 4]
def baseStart_2182 : Nat := 118140960795 + 2182 * 2 ^ 59
def prefixEnd_2182 : Nat := 4983230072969 + 3 ^ 40 * 2182 * 2
def baseEnd_2182 : Nat := 466312957631610357661

theorem tailTrace_2182 : CollatzResearch.WordTrace tailWord_2182 prefixEnd_2182 466312957631610357661 := by
  unfold tailWord_2182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2487002440701921907525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53056052068307667360533 2487002440701921907525)
  ·
    refine ⟨466312957631610357661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2487002440701921907525 466312957631610357661)
    ·
      rfl

theorem cell_2182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_2182 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2182 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2182 prefixEnd_2182 := by
    exact prefixLift 2182
  have htrace : WordTrace (prefixWord ++ tailWord_2182) baseStart_2182 baseEnd_2182 := by
    simpa [prefixWord, tailWord_2182, baseEnd_2182] using wordTrace_append hprefix tailTrace_2182
  have hstable : (prefixWord ++ tailWord_2182).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182).length < 2 ^ (prefixWord ++ tailWord_2182).sum := by decide
  have hdescent : baseEnd_2182 < baseStart_2182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2189 : List Nat := [1, 9]
def baseStart_2189 : Nat := 118140960795 + 2189 * 2 ^ 59
def prefixEnd_2189 : Nat := 4983230072969 + 3 ^ 40 * 2189 * 2
def baseEnd_2189 : Nat := 467808920373642753197

theorem tailTrace_2189 : CollatzResearch.WordTrace tailWord_2189 prefixEnd_2189 467808920373642753197 := by
  unfold tailWord_2189
  simp only [CollatzResearch.WordTrace]
  refine ⟨79839389077101696545621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53226259384734464363747 79839389077101696545621)
  ·
    refine ⟨467808920373642753197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 9 79839389077101696545621 467808920373642753197)
    ·
      rfl

theorem cell_2189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_2189 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2189 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2189 prefixEnd_2189 := by
    exact prefixLift 2189
  have htrace : WordTrace (prefixWord ++ tailWord_2189) baseStart_2189 baseEnd_2189 := by
    simpa [prefixWord, tailWord_2189, baseEnd_2189] using wordTrace_append hprefix tailTrace_2189
  have hstable : (prefixWord ++ tailWord_2189).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2189).length < 2 ^ (prefixWord ++ tailWord_2189).sum := by decide
  have hdescent : baseEnd_2189 < baseStart_2189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214 : List Nat := [9]
def baseStart_2214 : Nat := 118140960795 + 2214 * 2 ^ 59
def prefixEnd_2214 : Nat := 4983230072969 + 3 ^ 40 * 2214 * 2
def baseEnd_2214 : Nat := 315434429634886586741

theorem tailTrace_2214 : CollatzResearch.WordTrace tailWord_2214 prefixEnd_2214 315434429634886586741 := by
  unfold tailWord_2214
  simp only [CollatzResearch.WordTrace]
  refine ⟨315434429634886586741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 9 53834142657687310803797 315434429634886586741)
  ·
    rfl

theorem cell_2214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_2214 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2214 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2214 prefixEnd_2214 := by
    exact prefixLift 2214
  have htrace : WordTrace (prefixWord ++ tailWord_2214) baseStart_2214 baseEnd_2214 := by
    simpa [prefixWord, tailWord_2214, baseEnd_2214] using wordTrace_append hprefix tailTrace_2214
  have hstable : (prefixWord ++ tailWord_2214).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214).length < 2 ^ (prefixWord ++ tailWord_2214).sum := by decide
  have hdescent : baseEnd_2214 < baseStart_2214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216 : List Nat := [2, 1, 8]
def baseStart_2216 : Nat := 118140960795 + 2216 * 2 ^ 59
def prefixEnd_2216 : Nat := 4983230072969 + 3 ^ 40 * 2216 * 2
def baseEnd_2216 : Nat := 710368593567937275397

theorem tailTrace_2216 : CollatzResearch.WordTrace tailWord_2216 prefixEnd_2216 710368593567937275397 := by
  unfold tailWord_2216
  simp only [CollatzResearch.WordTrace]
  refine ⟨40412079989642653889251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53882773319523538519001 40412079989642653889251)
  ·
    refine ⟨60618119984463980833877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40412079989642653889251 60618119984463980833877)
    ·
      refine ⟨710368593567937275397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 60618119984463980833877 710368593567937275397)
      ·
        rfl

theorem cell_2216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_2216 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2216 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2216 prefixEnd_2216 := by
    exact prefixLift 2216
  have htrace : WordTrace (prefixWord ++ tailWord_2216) baseStart_2216 baseEnd_2216 := by
    simpa [prefixWord, tailWord_2216, baseEnd_2216] using wordTrace_append hprefix tailTrace_2216
  have hstable : (prefixWord ++ tailWord_2216).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216).length < 2 ^ (prefixWord ++ tailWord_2216).sum := by decide
  have hdescent : baseEnd_2216 < baseStart_2216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246 : List Nat := [6, 1, 2, 3]
def baseStart_2246 : Nat := 118140960795 + 2246 * 2 ^ 59
def prefixEnd_2246 : Nat := 4983230072969 + 3 ^ 40 * 2246 * 2
def baseEnd_2246 : Nat := 1079978245364361155765

theorem tailTrace_2246 : CollatzResearch.WordTrace tailWord_2246 prefixEnd_2246 1079978245364361155765 := by
  unfold tailWord_2246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2559948433456263480331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54612233247066954247061 2559948433456263480331)
  ·
    refine ⟨3839922650184395220497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2559948433456263480331 3839922650184395220497)
    ·
      refine ⟨2879941987638296415373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3839922650184395220497 2879941987638296415373)
      ·
        refine ⟨1079978245364361155765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2879941987638296415373 1079978245364361155765)
        ·
          rfl

theorem cell_2246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_2246 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2246 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2246 prefixEnd_2246 := by
    exact prefixLift 2246
  have htrace : WordTrace (prefixWord ++ tailWord_2246) baseStart_2246 baseEnd_2246 := by
    simpa [prefixWord, tailWord_2246, baseEnd_2246] using wordTrace_append hprefix tailTrace_2246
  have hstable : (prefixWord ++ tailWord_2246).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246).length < 2 ^ (prefixWord ++ tailWord_2246).sum := by decide
  have hdescent : baseEnd_2246 < baseStart_2246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253 : List Nat := [1, 6, 2, 3]
def baseStart_2253 : Nat := 118140960795 + 2253 * 2 ^ 59
def prefixEnd_2253 : Nat := 4983230072969 + 3 ^ 40 * 2253 * 2
def baseEnd_2253 : Nat := 1083344161533934045721

theorem tailTrace_2253 : CollatzResearch.WordTrace tailWord_2253 prefixEnd_2253 1083344161533934045721 := by
  unfold tailWord_2253
  simp only [CollatzResearch.WordTrace]
  refine ⟨82173660845240626875413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54782440563493751250275 82173660845240626875413)
  ·
    refine ⟨3851890352120654384785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82173660845240626875413 3851890352120654384785)
    ·
      refine ⟨2888917764090490788589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3851890352120654384785 2888917764090490788589)
      ·
        refine ⟨1083344161533934045721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2888917764090490788589 1083344161533934045721)
        ·
          rfl

theorem cell_2253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_2253 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2253 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2253 prefixEnd_2253 := by
    exact prefixLift 2253
  have htrace : WordTrace (prefixWord ++ tailWord_2253) baseStart_2253 baseEnd_2253 := by
    simpa [prefixWord, tailWord_2253, baseEnd_2253] using wordTrace_append hprefix tailTrace_2253
  have hstable : (prefixWord ++ tailWord_2253).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253).length < 2 ^ (prefixWord ++ tailWord_2253).sum := by decide
  have hdescent : baseEnd_2253 < baseStart_2253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260 : List Nat := [2, 4, 1, 5]
def baseStart_2260 : Nat := 118140960795 + 2260 * 2 ^ 59
def prefixEnd_2260 : Nat := 4983230072969 + 3 ^ 40 * 2260 * 2
def baseEnd_2260 : Nat := 1086710077703506935677

theorem tailTrace_2260 : CollatzResearch.WordTrace tailWord_2260 prefixEnd_2260 1086710077703506935677 := by
  unfold tailWord_2260
  simp only [CollatzResearch.WordTrace]
  refine ⟨41214485909940411190117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54952647879920548253489 41214485909940411190117)
  ·
    refine ⟨7727716108113827098147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41214485909940411190117 7727716108113827098147)
    ·
      refine ⟨11591574162170740647221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7727716108113827098147 11591574162170740647221)
      ·
        refine ⟨1086710077703506935677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11591574162170740647221 1086710077703506935677)
        ·
          rfl

theorem cell_2260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_2260 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2260 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2260 prefixEnd_2260 := by
    exact prefixLift 2260
  have htrace : WordTrace (prefixWord ++ tailWord_2260) baseStart_2260 baseEnd_2260 := by
    simpa [prefixWord, tailWord_2260, baseEnd_2260] using wordTrace_append hprefix tailTrace_2260
  have hstable : (prefixWord ++ tailWord_2260).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260).length < 2 ^ (prefixWord ++ tailWord_2260).sum := by decide
  have hdescent : baseEnd_2260 < baseStart_2260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2278 : List Nat := [7]
def baseStart_2278 : Nat := 118140960795 + 2278 * 2 ^ 59
def prefixEnd_2278 : Nat := 4983230072969 + 3 ^ 40 * 2278 * 2
def baseEnd_2278 : Nat := 1298210714916717133367

theorem tailTrace_2278 : CollatzResearch.WordTrace tailWord_2278 prefixEnd_2278 1298210714916717133367 := by
  unfold tailWord_2278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1298210714916717133367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 55390323836446597690325 1298210714916717133367)
  ·
    rfl

theorem cell_2278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2278 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2278 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2278 prefixEnd_2278 := by
    exact prefixLift 2278
  have htrace : WordTrace (prefixWord ++ tailWord_2278) baseStart_2278 baseEnd_2278 := by
    simpa [prefixWord, tailWord_2278, baseEnd_2278] using wordTrace_append hprefix tailTrace_2278
  have hstable : (prefixWord ++ tailWord_2278).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2278).length < 2 ^ (prefixWord ++ tailWord_2278).sum := by decide
  have hdescent : baseEnd_2278 < baseStart_2278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292 : List Nat := [2, 6, 1, 3]
def baseStart_2292 : Nat := 118140960795 + 2292 * 2 ^ 59
def prefixEnd_2292 : Nat := 4983230072969 + 3 ^ 40 * 2292 * 2
def baseEnd_2292 : Nat := 1102097123050125861191

theorem tailTrace_2292 : CollatzResearch.WordTrace tailWord_2292 prefixEnd_2292 1102097123050125861191 := by
  unfold tailWord_2292
  simp only [CollatzResearch.WordTrace]
  refine ⟨41798053851975143772565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55730738469300191696753 41798053851975143772565)
  ·
    refine ⟨1959283774311334864339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41798053851975143772565 1959283774311334864339)
    ·
      refine ⟨2938925661467002296509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1959283774311334864339 2938925661467002296509)
      ·
        refine ⟨1102097123050125861191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2938925661467002296509 1102097123050125861191)
        ·
          rfl

theorem cell_2292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_2292 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2292 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2292 prefixEnd_2292 := by
    exact prefixLift 2292
  have htrace : WordTrace (prefixWord ++ tailWord_2292) baseStart_2292 baseEnd_2292 := by
    simpa [prefixWord, tailWord_2292, baseEnd_2292] using wordTrace_append hprefix tailTrace_2292
  have hstable : (prefixWord ++ tailWord_2292).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292).length < 2 ^ (prefixWord ++ tailWord_2292).sum := by decide
  have hdescent : baseEnd_2292 < baseStart_2292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293 : List Nat := [1, 3, 8]
def baseStart_2293 : Nat := 118140960795 + 2293 * 2 ^ 59
def prefixEnd_2293 : Nat := 4983230072969 + 3 ^ 40 * 2293 * 2
def baseEnd_2293 : Nat := 367525989405735900871

theorem tailTrace_2293 : CollatzResearch.WordTrace tailWord_2293 prefixEnd_2293 367525989405735900871 := by
  unfold tailWord_2293
  simp only [CollatzResearch.WordTrace]
  refine ⟨83632580700327458331533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55755053800218305554355 83632580700327458331533)
  ·
    refine ⟨31362217762622796874325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83632580700327458331533 31362217762622796874325)
    ·
      refine ⟨367525989405735900871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 31362217762622796874325 367525989405735900871)
      ·
        rfl

theorem cell_2293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_2293 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2293 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2293 prefixEnd_2293 := by
    exact prefixLift 2293
  have htrace : WordTrace (prefixWord ++ tailWord_2293) baseStart_2293 baseEnd_2293 := by
    simpa [prefixWord, tailWord_2293, baseEnd_2293] using wordTrace_append hprefix tailTrace_2293
  have hstable : (prefixWord ++ tailWord_2293).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293).length < 2 ^ (prefixWord ++ tailWord_2293).sum := by decide
  have hdescent : baseEnd_2293 < baseStart_2293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310 : List Nat := [6, 2, 3]
def baseStart_2310 : Nat := 118140960795 + 2310 * 2 ^ 59
def prefixEnd_2310 : Nat := 4983230072969 + 3 ^ 40 * 2310 * 2
def baseEnd_2310 : Nat := 740501557371732671195

theorem tailTrace_2310 : CollatzResearch.WordTrace tailWord_2310 prefixEnd_2310 740501557371732671195 := by
  unfold tailWord_2310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2632894426210605053137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56168414425826241133589 2632894426210605053137)
  ·
    refine ⟨1974670819657953789853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2632894426210605053137 1974670819657953789853)
    ·
      refine ⟨740501557371732671195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1974670819657953789853 740501557371732671195)
      ·
        rfl

theorem cell_2310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_2310 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2310 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2310 prefixEnd_2310 := by
    exact prefixLift 2310
  have htrace : WordTrace (prefixWord ++ tailWord_2310) baseStart_2310 baseEnd_2310 := by
    simpa [prefixWord, tailWord_2310, baseEnd_2310] using wordTrace_append hprefix tailTrace_2310
  have hstable : (prefixWord ++ tailWord_2310).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310).length < 2 ^ (prefixWord ++ tailWord_2310).sum := by decide
  have hdescent : baseEnd_2310 < baseStart_2310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317 : List Nat := [1, 7, 3]
def baseStart_2317 : Nat := 118140960795 + 2317 * 2 ^ 59
def prefixEnd_2317 : Nat := 4983230072969 + 3 ^ 40 * 2317 * 2
def baseEnd_2317 : Nat := 742745501484781264499

theorem tailTrace_2317 : CollatzResearch.WordTrace tailWord_2317 prefixEnd_2317 742745501484781264499 := by
  unfold tailWord_2317
  simp only [CollatzResearch.WordTrace]
  refine ⟨84507932613379557205205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56338621742253038136803 84507932613379557205205)
  ·
    refine ⟨1980654670626083371997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 84507932613379557205205 1980654670626083371997)
    ·
      refine ⟨742745501484781264499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1980654670626083371997 742745501484781264499)
      ·
        rfl

theorem cell_2317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_2317 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2317 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2317 prefixEnd_2317 := by
    exact prefixLift 2317
  have htrace : WordTrace (prefixWord ++ tailWord_2317) baseStart_2317 baseEnd_2317 := by
    simpa [prefixWord, tailWord_2317, baseEnd_2317] using wordTrace_append hprefix tailTrace_2317
  have hstable : (prefixWord ++ tailWord_2317).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317).length < 2 ^ (prefixWord ++ tailWord_2317).sum := by decide
  have hdescent : baseEnd_2317 < baseStart_2317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324 : List Nat := [2, 4, 5]
def baseStart_2324 : Nat := 118140960795 + 2324 * 2 ^ 59
def prefixEnd_2324 : Nat := 4983230072969 + 3 ^ 40 * 2324 * 2
def baseEnd_2324 : Nat := 744989445597829857803

theorem tailTrace_2324 : CollatzResearch.WordTrace tailWord_2324 prefixEnd_2324 744989445597829857803 := by
  unfold tailWord_2324
  simp only [CollatzResearch.WordTrace]
  refine ⟨42381621794009876355013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56508829058679835140017 42381621794009876355013)
  ·
    refine ⟨7946554086376851816565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42381621794009876355013 7946554086376851816565)
    ·
      refine ⟨744989445597829857803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7946554086376851816565 744989445597829857803)
      ·
        rfl

theorem cell_2324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_2324 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2324 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2324 prefixEnd_2324 := by
    exact prefixLift 2324
  have htrace : WordTrace (prefixWord ++ tailWord_2324) baseStart_2324 baseEnd_2324 := by
    simpa [prefixWord, tailWord_2324, baseEnd_2324] using wordTrace_append hprefix tailTrace_2324
  have hstable : (prefixWord ++ tailWord_2324).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324).length < 2 ^ (prefixWord ++ tailWord_2324).sum := by decide
  have hdescent : baseEnd_2324 < baseStart_2324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326 : List Nat := [5, 4]
def baseStart_2326 : Nat := 118140960795 + 2326 * 2 ^ 59
def prefixEnd_2326 : Nat := 4983230072969 + 3 ^ 40 * 2326 * 2
def baseEnd_2326 : Nat := 994174096649696417377

theorem tailTrace_2326 : CollatzResearch.WordTrace tailWord_2326 prefixEnd_2326 994174096649696417377 := by
  unfold tailWord_2326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5302261848798380892677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56557459720516062855221 5302261848798380892677)
  ·
    refine ⟨994174096649696417377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5302261848798380892677 994174096649696417377)
    ·
      rfl

theorem cell_2326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_2326 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2326 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2326 prefixEnd_2326 := by
    exact prefixLift 2326
  have htrace : WordTrace (prefixWord ++ tailWord_2326) baseStart_2326 baseEnd_2326 := by
    simpa [prefixWord, tailWord_2326, baseEnd_2326] using wordTrace_append hprefix tailTrace_2326
  have hstable : (prefixWord ++ tailWord_2326).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326).length < 2 ^ (prefixWord ++ tailWord_2326).sum := by decide
  have hdescent : baseEnd_2326 < baseStart_2326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342 : List Nat := [8]
def baseStart_2342 : Nat := 118140960795 + 2342 * 2 ^ 59
def prefixEnd_2342 : Nat := 4983230072969 + 3 ^ 40 * 2342 * 2
def baseEnd_2342 : Nat := 667341855646943959885

theorem tailTrace_2342 : CollatzResearch.WordTrace tailWord_2342 prefixEnd_2342 667341855646943959885 := by
  unfold tailWord_2342
  simp only [CollatzResearch.WordTrace]
  refine ⟨667341855646943959885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 56946505015205884576853 667341855646943959885)
  ·
    rfl

theorem cell_2342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_2342 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2342 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2342 prefixEnd_2342 := by
    exact prefixLift 2342
  have htrace : WordTrace (prefixWord ++ tailWord_2342) baseStart_2342 baseEnd_2342 := by
    simpa [prefixWord, tailWord_2342, baseEnd_2342] using wordTrace_append hprefix tailTrace_2342
  have hstable : (prefixWord ++ tailWord_2342).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342).length < 2 ^ (prefixWord ++ tailWord_2342).sum := by decide
  have hdescent : baseEnd_2342 < baseStart_2342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358 : List Nat := [5, 1, 2, 4]
def baseStart_2358 : Nat := 118140960795 + 2358 * 2 ^ 59
def prefixEnd_2358 : Nat := 4983230072969 + 3 ^ 40 * 2358 * 2
def baseEnd_2358 : Nat := 1133832904077527395063

theorem tailTrace_2358 : CollatzResearch.WordTrace tailWord_2358 prefixEnd_2358 1133832904077527395063 := by
  unfold tailWord_2358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5375207841552722465483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57335550309895706298485 5375207841552722465483)
  ·
    refine ⟨8062811762329083698225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5375207841552722465483 8062811762329083698225)
    ·
      refine ⟨6047108821746812773669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8062811762329083698225 6047108821746812773669)
      ·
        refine ⟨1133832904077527395063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6047108821746812773669 1133832904077527395063)
        ·
          rfl

theorem cell_2358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_2358 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2358 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2358 prefixEnd_2358 := by
    exact prefixLift 2358
  have htrace : WordTrace (prefixWord ++ tailWord_2358) baseStart_2358 baseEnd_2358 := by
    simpa [prefixWord, tailWord_2358, baseEnd_2358] using wordTrace_append hprefix tailTrace_2358
  have hstable : (prefixWord ++ tailWord_2358).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358).length < 2 ^ (prefixWord ++ tailWord_2358).sum := by decide
  have hdescent : baseEnd_2358 < baseStart_2358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365 : List Nat := [1, 4, 1, 6]
def baseStart_2365 : Nat := 118140960795 + 2365 * 2 ^ 59
def prefixEnd_2365 : Nat := 4983230072969 + 3 ^ 40 * 2365 * 2
def baseEnd_2365 : Nat := 1137198820247100285019

theorem tailTrace_2365 : CollatzResearch.WordTrace tailWord_2365 prefixEnd_2365 1137198820247100285019 := by
  unfold tailWord_2365
  simp only [CollatzResearch.WordTrace]
  refine ⟨86258636439483754952549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57505757626322503301699 86258636439483754952549)
  ·
    refine ⟨16173494332403204053603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86258636439483754952549 16173494332403204053603)
    ·
      refine ⟨24260241498604806080405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16173494332403204053603 24260241498604806080405)
      ·
        refine ⟨1137198820247100285019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24260241498604806080405 1137198820247100285019)
        ·
          rfl

theorem cell_2365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_2365 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2365 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2365 prefixEnd_2365 := by
    exact prefixLift 2365
  have htrace : WordTrace (prefixWord ++ tailWord_2365) baseStart_2365 baseEnd_2365 := by
    simpa [prefixWord, tailWord_2365, baseEnd_2365] using wordTrace_append hprefix tailTrace_2365
  have hstable : (prefixWord ++ tailWord_2365).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365).length < 2 ^ (prefixWord ++ tailWord_2365).sum := by decide
  have hdescent : baseEnd_2365 < baseStart_2365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370 : List Nat := [3, 8]
def baseStart_2370 : Nat := 118140960795 + 2370 * 2 ^ 59
def prefixEnd_2370 : Nat := 4983230072969 + 3 ^ 40 * 2370 * 2
def baseEnd_2370 : Nat := 253245121351668776029

theorem tailTrace_2370 : CollatzResearch.WordTrace tailWord_2370 prefixEnd_2370 253245121351668776029 := by
  unfold tailWord_2370
  simp only [CollatzResearch.WordTrace]
  refine ⟨21610250355342402221141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57627334280913072589709 21610250355342402221141)
  ·
    refine ⟨253245121351668776029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 21610250355342402221141 253245121351668776029)
    ·
      rfl

theorem cell_2370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_2370 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2370 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2370 prefixEnd_2370 := by
    exact prefixLift 2370
  have htrace : WordTrace (prefixWord ++ tailWord_2370) baseStart_2370 baseEnd_2370 := by
    simpa [prefixWord, tailWord_2370, baseEnd_2370] using wordTrace_append hprefix tailTrace_2370
  have hstable : (prefixWord ++ tailWord_2370).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370).length < 2 ^ (prefixWord ++ tailWord_2370).sum := by decide
  have hdescent : baseEnd_2370 < baseStart_2370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2390 : List Nat := [5, 2, 3, 2]
def baseStart_2390 : Nat := 118140960795 + 2390 * 2 ^ 59
def prefixEnd_2390 : Nat := 4983230072969 + 3 ^ 40 * 2390 * 2
def baseEnd_2390 : Nat := 1149219949424146320577

theorem tailTrace_2390 : CollatzResearch.WordTrace tailWord_2390 prefixEnd_2390 1149219949424146320577 := by
  unfold tailWord_2390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5448153834307064038289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58113640899275349741749 5448153834307064038289)
  ·
    refine ⟨4086115375730298028717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5448153834307064038289 4086115375730298028717)
    ·
      refine ⟨1532293265898861760769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4086115375730298028717 1532293265898861760769)
      ·
        refine ⟨1149219949424146320577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1532293265898861760769 1149219949424146320577)
        ·
          rfl

theorem cell_2390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_2390 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2390 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2390 prefixEnd_2390 := by
    exact prefixLift 2390
  have htrace : WordTrace (prefixWord ++ tailWord_2390) baseStart_2390 baseEnd_2390 := by
    simpa [prefixWord, tailWord_2390, baseEnd_2390] using wordTrace_append hprefix tailTrace_2390
  have hstable : (prefixWord ++ tailWord_2390).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2390).length < 2 ^ (prefixWord ++ tailWord_2390).sum := by decide
  have hdescent : baseEnd_2390 < baseStart_2390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2397 : List Nat := [1, 4, 5, 2]
def baseStart_2397 : Nat := 118140960795 + 2397 * 2 ^ 59
def prefixEnd_2397 : Nat := 4983230072969 + 3 ^ 40 * 2397 * 2
def baseEnd_2397 : Nat := 1152585865593719210533

theorem tailTrace_2397 : CollatzResearch.WordTrace tailWord_2397 prefixEnd_2397 1152585865593719210533 := by
  unfold tailWord_2397
  simp only [CollatzResearch.WordTrace]
  refine ⟨87425772323553220117445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58283848215702146744963 87425772323553220117445)
  ·
    refine ⟨16392332310666228772021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87425772323553220117445 16392332310666228772021)
    ·
      refine ⟨1536781154124958947377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16392332310666228772021 1536781154124958947377)
      ·
        refine ⟨1152585865593719210533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1536781154124958947377 1152585865593719210533)
        ·
          rfl

theorem cell_2397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_2397 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2397 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2397 prefixEnd_2397 := by
    exact prefixLift 2397
  have htrace : WordTrace (prefixWord ++ tailWord_2397) baseStart_2397 baseEnd_2397 := by
    simpa [prefixWord, tailWord_2397, baseEnd_2397] using wordTrace_append hprefix tailTrace_2397
  have hstable : (prefixWord ++ tailWord_2397).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2397).length < 2 ^ (prefixWord ++ tailWord_2397).sum := by decide
  have hdescent : baseEnd_2397 < baseStart_2397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406 : List Nat := [7]
def baseStart_2406 : Nat := 118140960795 + 2406 * 2 ^ 59
def prefixEnd_2406 : Nat := 4983230072969 + 3 ^ 40 * 2406 * 2
def baseEnd_2406 : Nat := 1371156707671058706173

theorem tailTrace_2406 : CollatzResearch.WordTrace tailWord_2406 prefixEnd_2406 1371156707671058706173 := by
  unfold tailWord_2406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1371156707671058706173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 58502686193965171463381 1371156707671058706173)
  ·
    rfl

theorem cell_2406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2406 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2406 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2406 prefixEnd_2406 := by
    exact prefixLift 2406
  have htrace : WordTrace (prefixWord ++ tailWord_2406) baseStart_2406 baseEnd_2406 := by
    simpa [prefixWord, tailWord_2406, baseEnd_2406] using wordTrace_append hprefix tailTrace_2406
  have hstable : (prefixWord ++ tailWord_2406).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406).length < 2 ^ (prefixWord ++ tailWord_2406).sum := by decide
  have hdescent : baseEnd_2406 < baseStart_2406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420 : List Nat := [2, 8]
def baseStart_2420 : Nat := 118140960795 + 2420 * 2 ^ 59
def prefixEnd_2420 : Nat := 4983230072969 + 3 ^ 40 * 2420 * 2
def baseEnd_2420 : Nat := 517175690860711805887

theorem tailTrace_2420 : CollatzResearch.WordTrace tailWord_2420 prefixEnd_2420 517175690860711805887 := by
  unfold tailWord_2420
  simp only [CollatzResearch.WordTrace]
  refine ⟨44132325620114074102357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58843100826818765469809 44132325620114074102357)
  ·
    refine ⟨517175690860711805887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 44132325620114074102357 517175690860711805887)
    ·
      rfl

theorem cell_2420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_2420 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2420 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2420 prefixEnd_2420 := by
    exact prefixLift 2420
  have htrace : WordTrace (prefixWord ++ tailWord_2420) baseStart_2420 baseEnd_2420 := by
    simpa [prefixWord, tailWord_2420, baseEnd_2420] using wordTrace_append hprefix tailTrace_2420
  have hstable : (prefixWord ++ tailWord_2420).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420).length < 2 ^ (prefixWord ++ tailWord_2420).sum := by decide
  have hdescent : baseEnd_2420 < baseStart_2420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430 : List Nat := [4, 2, 3, 3]
def baseStart_2430 : Nat := 118140960795 + 2430 * 2 ^ 59
def prefixEnd_2430 : Nat := 4983230072969 + 3 ^ 40 * 2430 * 2
def baseEnd_2430 : Nat := 1168453756107419977469

theorem tailTrace_2430 : CollatzResearch.WordTrace tailWord_2430 prefixEnd_2430 1168453756107419977469 := by
  unfold tailWord_2430
  simp only [CollatzResearch.WordTrace]
  refine ⟨11078672650499982008593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59086254135999904045829 11078672650499982008593)
  ·
    refine ⟨8309004487874986506445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11078672650499982008593 8309004487874986506445)
    ·
      refine ⟨3115876682953119939917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8309004487874986506445 3115876682953119939917)
      ·
        refine ⟨1168453756107419977469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3115876682953119939917 1168453756107419977469)
        ·
          rfl

theorem cell_2430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_2430 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2430 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2430 prefixEnd_2430 := by
    exact prefixLift 2430
  have htrace : WordTrace (prefixWord ++ tailWord_2430) baseStart_2430 baseEnd_2430 := by
    simpa [prefixWord, tailWord_2430, baseEnd_2430] using wordTrace_append hprefix tailTrace_2430
  have hstable : (prefixWord ++ tailWord_2430).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430).length < 2 ^ (prefixWord ++ tailWord_2430).sum := by decide
  have hdescent : baseEnd_2430 < baseStart_2430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438 : List Nat := [6, 3]
def baseStart_2438 : Nat := 118140960795 + 2438 * 2 ^ 59
def prefixEnd_2438 : Nat := 4983230072969 + 3 ^ 40 * 2438 * 2
def baseEnd_2438 : Nat := 1042044904394733074531

theorem tailTrace_2438 : CollatzResearch.WordTrace tailWord_2438 prefixEnd_2438 1042044904394733074531 := by
  unfold tailWord_2438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2778786411719288198749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59280776783344814906645 2778786411719288198749)
  ·
    refine ⟨1042044904394733074531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2778786411719288198749 1042044904394733074531)
    ·
      rfl

theorem cell_2438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_2438 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2438 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2438 prefixEnd_2438 := by
    exact prefixLift 2438
  have htrace : WordTrace (prefixWord ++ tailWord_2438) baseStart_2438 baseEnd_2438 := by
    simpa [prefixWord, tailWord_2438, baseEnd_2438] using wordTrace_append hprefix tailTrace_2438
  have hstable : (prefixWord ++ tailWord_2438).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438).length < 2 ^ (prefixWord ++ tailWord_2438).sum := by decide
  have hdescent : baseEnd_2438 < baseStart_2438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445 : List Nat := [1, 8]
def baseStart_2445 : Nat := 118140960795 + 2445 * 2 ^ 59
def prefixEnd_2445 : Nat := 4983230072969 + 3 ^ 40 * 2445 * 2
def baseEnd_2445 : Nat := 1045036829878797865603

theorem tailTrace_2445 : CollatzResearch.WordTrace tailWord_2445 prefixEnd_2445 1045036829878797865603 := by
  unfold tailWord_2445
  simp only [CollatzResearch.WordTrace]
  refine ⟨89176476149657417864789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59450984099771611909859 89176476149657417864789)
  ·
    refine ⟨1045036829878797865603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 89176476149657417864789 1045036829878797865603)
    ·
      rfl

theorem cell_2445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_2445 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2445 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2445 prefixEnd_2445 := by
    exact prefixLift 2445
  have htrace : WordTrace (prefixWord ++ tailWord_2445) baseStart_2445 baseEnd_2445 := by
    simpa [prefixWord, tailWord_2445, baseEnd_2445] using wordTrace_append hprefix tailTrace_2445
  have hstable : (prefixWord ++ tailWord_2445).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445).length < 2 ^ (prefixWord ++ tailWord_2445).sum := by decide
  have hdescent : baseEnd_2445 < baseStart_2445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450 : List Nat := [3, 2, 3, 4]
def baseStart_2450 : Nat := 118140960795 + 2450 * 2 ^ 59
def prefixEnd_2450 : Nat := 4983230072969 + 3 ^ 40 * 2450 * 2
def baseEnd_2450 : Nat := 1178070659449056805915

theorem tailTrace_2450 : CollatzResearch.WordTrace tailWord_2450 prefixEnd_2450 1178070659449056805915 := by
  unfold tailWord_2450
  simp only [CollatzResearch.WordTrace]
  refine ⟨22339710282885817949201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59572560754362181197869 22339710282885817949201)
  ·
    refine ⟨16754782712164363461901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22339710282885817949201 16754782712164363461901)
    ·
      refine ⟨6283043517061636298213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16754782712164363461901 6283043517061636298213)
      ·
        refine ⟨1178070659449056805915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6283043517061636298213 1178070659449056805915)
        ·
          rfl

theorem cell_2450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_2450 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2450 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2450 prefixEnd_2450 := by
    exact prefixLift 2450
  have htrace : WordTrace (prefixWord ++ tailWord_2450) baseStart_2450 baseEnd_2450 := by
    simpa [prefixWord, tailWord_2450, baseEnd_2450] using wordTrace_append hprefix tailTrace_2450
  have hstable : (prefixWord ++ tailWord_2450).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450).length < 2 ^ (prefixWord ++ tailWord_2450).sum := by decide
  have hdescent : baseEnd_2450 < baseStart_2450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470 : List Nat := [12]
def baseStart_2470 : Nat := 118140960795 + 2470 * 2 ^ 59
def prefixEnd_2470 : Nat := 4983230072969 + 3 ^ 40 * 2470 * 2
def baseEnd_2470 : Nat := 43988428251507171643

theorem tailTrace_2470 : CollatzResearch.WordTrace tailWord_2470 prefixEnd_2470 43988428251507171643 := by
  unfold tailWord_2470
  simp only [CollatzResearch.WordTrace]
  refine ⟨43988428251507171643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 12 60058867372724458349909 43988428251507171643)
  ·
    rfl

theorem cell_2470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 12].length) (baseStart_2470 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2470 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2470 prefixEnd_2470 := by
    exact prefixLift 2470
  have htrace : WordTrace (prefixWord ++ tailWord_2470) baseStart_2470 baseEnd_2470 := by
    simpa [prefixWord, tailWord_2470, baseEnd_2470] using wordTrace_append hprefix tailTrace_2470
  have hstable : (prefixWord ++ tailWord_2470).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470).length < 2 ^ (prefixWord ++ tailWord_2470).sum := by decide
  have hdescent : baseEnd_2470 < baseStart_2470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2478 : List Nat := [4, 1, 6]
def baseStart_2478 : Nat := 118140960795 + 2478 * 2 ^ 59
def prefixEnd_2478 : Nat := 4983230072969 + 3 ^ 40 * 2478 * 2
def baseEnd_2478 : Nat := 794356216084898910493

theorem tailTrace_2478 : CollatzResearch.WordTrace tailWord_2478 prefixEnd_2478 794356216084898910493 := by
  unfold tailWord_2478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11297510628763006727011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60253390020069369210725 11297510628763006727011)
  ·
    refine ⟨16946265943144510090517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11297510628763006727011 16946265943144510090517)
    ·
      refine ⟨794356216084898910493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16946265943144510090517 794356216084898910493)
      ·
        rfl

theorem cell_2478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_2478 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2478 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2478 prefixEnd_2478 := by
    exact prefixLift 2478
  have htrace : WordTrace (prefixWord ++ tailWord_2478) baseStart_2478 baseEnd_2478 := by
    simpa [prefixWord, tailWord_2478, baseEnd_2478] using wordTrace_append hprefix tailTrace_2478
  have hstable : (prefixWord ++ tailWord_2478).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2478).length < 2 ^ (prefixWord ++ tailWord_2478).sum := by decide
  have hdescent : baseEnd_2478 < baseStart_2478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502 : List Nat := [6, 1, 5]
def baseStart_2502 : Nat := 118140960795 + 2502 * 2 ^ 59
def prefixEnd_2502 : Nat := 4983230072969 + 3 ^ 40 * 2502 * 2
def baseEnd_2502 : Nat := 401024869379104186625

theorem tailTrace_2502 : CollatzResearch.WordTrace tailWord_2502 prefixEnd_2502 401024869379104186625 := by
  unfold tailWord_2502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2851732404473629771555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60836957962104101793173 2851732404473629771555)
  ·
    refine ⟨4277598606710444657333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2851732404473629771555 4277598606710444657333)
    ·
      refine ⟨401024869379104186625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4277598606710444657333 401024869379104186625)
      ·
        rfl

theorem cell_2502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_2502 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2502 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2502 prefixEnd_2502 := by
    exact prefixLift 2502
  have htrace : WordTrace (prefixWord ++ tailWord_2502) baseStart_2502 baseEnd_2502 := by
    simpa [prefixWord, tailWord_2502, baseEnd_2502] using wordTrace_append hprefix tailTrace_2502
  have hstable : (prefixWord ++ tailWord_2502).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502).length < 2 ^ (prefixWord ++ tailWord_2502).sum := by decide
  have hdescent : baseEnd_2502 < baseStart_2502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509 : List Nat := [1, 6, 5]
def baseStart_2509 : Nat := 118140960795 + 2509 * 2 ^ 59
def prefixEnd_2509 : Nat := 4983230072969 + 3 ^ 40 * 2509 * 2
def baseEnd_2509 : Nat := 402146841435628483277

theorem tailTrace_2509 : CollatzResearch.WordTrace tailWord_2509 prefixEnd_2509 402146841435628483277 := by
  unfold tailWord_2509
  simp only [CollatzResearch.WordTrace]
  refine ⟨91510747917796348194581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61007165278530898796387 91510747917796348194581)
  ·
    refine ⟨4289566308646703821621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91510747917796348194581 4289566308646703821621)
    ·
      refine ⟨402146841435628483277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4289566308646703821621 402146841435628483277)
      ·
        rfl

theorem cell_2509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_2509 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2509 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2509 prefixEnd_2509 := by
    exact prefixLift 2509
  have htrace : WordTrace (prefixWord ++ tailWord_2509) baseStart_2509 baseEnd_2509 := by
    simpa [prefixWord, tailWord_2509, baseEnd_2509] using wordTrace_append hprefix tailTrace_2509
  have hstable : (prefixWord ++ tailWord_2509).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509).length < 2 ^ (prefixWord ++ tailWord_2509).sum := by decide
  have hdescent : baseEnd_2509 < baseStart_2509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524 : List Nat := [2, 2, 7]
def baseStart_2524 : Nat := 118140960795 + 2524 * 2 ^ 59
def prefixEnd_2524 : Nat := 4983230072969 + 3 ^ 40 * 2524 * 2
def baseEnd_2524 : Nat := 809102134542075380777

theorem tailTrace_2524 : CollatzResearch.WordTrace tailWord_2524 prefixEnd_2524 809102134542075380777 := by
  unfold tailWord_2524
  simp only [CollatzResearch.WordTrace]
  refine ⟨46028921431726954995313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61371895242302606660417 46028921431726954995313)
  ·
    refine ⟨34521691073795216246485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46028921431726954995313 34521691073795216246485)
    ·
      refine ⟨809102134542075380777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 34521691073795216246485 809102134542075380777)
      ·
        rfl

theorem cell_2524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_2524 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2524 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2524 prefixEnd_2524 := by
    exact prefixLift 2524
  have htrace : WordTrace (prefixWord ++ tailWord_2524) baseStart_2524 baseEnd_2524 := by
    simpa [prefixWord, tailWord_2524, baseEnd_2524] using wordTrace_append hprefix tailTrace_2524
  have hstable : (prefixWord ++ tailWord_2524).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524).length < 2 ^ (prefixWord ++ tailWord_2524).sum := by decide
  have hdescent : baseEnd_2524 < baseStart_2524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526 : List Nat := [4, 5]
def baseStart_2526 : Nat := 118140960795 + 2526 * 2 ^ 59
def prefixEnd_2526 : Nat := 4983230072969 + 3 ^ 40 * 2526 * 2
def baseEnd_2526 : Nat := 1079657681908690448009

theorem tailTrace_2526 : CollatzResearch.WordTrace tailWord_2526 prefixEnd_2526 1079657681908690448009 := by
  unfold tailWord_2526
  simp only [CollatzResearch.WordTrace]
  refine ⟨11516348607026031445429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61420525904138834375621 11516348607026031445429)
  ·
    refine ⟨1079657681908690448009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11516348607026031445429 1079657681908690448009)
    ·
      rfl

theorem cell_2526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_2526 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2526 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2526 prefixEnd_2526 := by
    exact prefixLift 2526
  have htrace : WordTrace (prefixWord ++ tailWord_2526) baseStart_2526 baseEnd_2526 := by
    simpa [prefixWord, tailWord_2526, baseEnd_2526] using wordTrace_append hprefix tailTrace_2526
  have hstable : (prefixWord ++ tailWord_2526).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526).length < 2 ^ (prefixWord ++ tailWord_2526).sum := by decide
  have hdescent : baseEnd_2526 < baseStart_2526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534 : List Nat := [7]
def baseStart_2534 : Nat := 118140960795 + 2534 * 2 ^ 59
def prefixEnd_2534 : Nat := 4983230072969 + 3 ^ 40 * 2534 * 2
def baseEnd_2534 : Nat := 1444102700425400278979

theorem tailTrace_2534 : CollatzResearch.WordTrace tailWord_2534 prefixEnd_2534 1444102700425400278979 := by
  unfold tailWord_2534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1444102700425400278979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 61615048551483745236437 1444102700425400278979)
  ·
    rfl

theorem cell_2534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2534 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2534 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2534 prefixEnd_2534 := by
    exact prefixLift 2534
  have htrace : WordTrace (prefixWord ++ tailWord_2534) baseStart_2534 baseEnd_2534 := by
    simpa [prefixWord, tailWord_2534, baseEnd_2534] using wordTrace_append hprefix tailTrace_2534
  have hstable : (prefixWord ++ tailWord_2534).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534).length < 2 ^ (prefixWord ++ tailWord_2534).sum := by decide
  have hdescent : baseEnd_2534 < baseStart_2534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548 : List Nat := [2, 6, 4]
def baseStart_2548 : Nat := 118140960795 + 2548 * 2 ^ 59
def prefixEnd_2548 : Nat := 4983230072969 + 3 ^ 40 * 2548 * 2
def baseEnd_2548 : Nat := 408397828607692421767

theorem tailTrace_2548 : CollatzResearch.WordTrace tailWord_2548 prefixEnd_2548 408397828607692421767 := by
  unfold tailWord_2548
  simp only [CollatzResearch.WordTrace]
  refine ⟨46466597388253004432149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61955463184337339242865 46466597388253004432149)
  ·
    refine ⟨2178121752574359582757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46466597388253004432149 2178121752574359582757)
    ·
      refine ⟨408397828607692421767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2178121752574359582757 408397828607692421767)
      ·
        rfl

theorem cell_2548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_2548 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2548 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2548 prefixEnd_2548 := by
    exact prefixLift 2548
  have htrace : WordTrace (prefixWord ++ tailWord_2548) baseStart_2548 baseEnd_2548 := by
    simpa [prefixWord, tailWord_2548, baseEnd_2548] using wordTrace_append hprefix tailTrace_2548
  have hstable : (prefixWord ++ tailWord_2548).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548).length < 2 ^ (prefixWord ++ tailWord_2548).sum := by decide
  have hdescent : baseEnd_2548 < baseStart_2548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2582 : List Nat := [5, 5]
def baseStart_2582 : Nat := 118140960795 + 2582 * 2 ^ 59
def prefixEnd_2582 : Nat := 4983230072969 + 3 ^ 40 * 2582 * 2
def baseEnd_2582 : Nat := 551796542890604388293

theorem tailTrace_2582 : CollatzResearch.WordTrace tailWord_2582 prefixEnd_2582 551796542890604388293 := by
  unfold tailWord_2582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5885829790833113475125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62782184435553210401333 5885829790833113475125)
  ·
    refine ⟨551796542890604388293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5885829790833113475125 551796542890604388293)
    ·
      rfl

theorem cell_2582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_2582 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2582 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2582 prefixEnd_2582 := by
    exact prefixLift 2582
  have htrace : WordTrace (prefixWord ++ tailWord_2582) baseStart_2582 baseEnd_2582 := by
    simpa [prefixWord, tailWord_2582, baseEnd_2582] using wordTrace_append hprefix tailTrace_2582
  have hstable : (prefixWord ++ tailWord_2582).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2582).length < 2 ^ (prefixWord ++ tailWord_2582).sum := by decide
  have hdescent : baseEnd_2582 < baseStart_2582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2598 : List Nat := [8]
def baseStart_2598 : Nat := 118140960795 + 2598 * 2 ^ 59
def prefixEnd_2598 : Nat := 4983230072969 + 3 ^ 40 * 2598 * 2
def baseEnd_2598 : Nat := 740287848401285532691

theorem tailTrace_2598 : CollatzResearch.WordTrace tailWord_2598 prefixEnd_2598 740287848401285532691 := by
  unfold tailWord_2598
  simp only [CollatzResearch.WordTrace]
  refine ⟨740287848401285532691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 63171229730243032122965 740287848401285532691)
  ·
    rfl

theorem cell_2598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_2598 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2598 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2598 prefixEnd_2598 := by
    exact prefixLift 2598
  have htrace : WordTrace (prefixWord ++ tailWord_2598) baseStart_2598 baseEnd_2598 := by
    simpa [prefixWord, tailWord_2598, baseEnd_2598] using wordTrace_append hprefix tailTrace_2598
  have hstable : (prefixWord ++ tailWord_2598).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2598).length < 2 ^ (prefixWord ++ tailWord_2598).sum := by decide
  have hdescent : baseEnd_2598 < baseStart_2598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626 : List Nat := [3, 6]
def baseStart_2626 : Nat := 118140960795 + 2626 * 2 ^ 59
def prefixEnd_2626 : Nat := 4983230072969 + 3 ^ 40 * 2626 * 2
def baseEnd_2626 : Nat := 1122399474538187463325

theorem tailTrace_2626 : CollatzResearch.WordTrace tailWord_2626 prefixEnd_2626 1122399474538187463325 := by
  unfold tailWord_2626
  simp only [CollatzResearch.WordTrace]
  refine ⟨23944522123481332550933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63852058995950220135821 23944522123481332550933)
  ·
    refine ⟨1122399474538187463325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23944522123481332550933 1122399474538187463325)
    ·
      rfl

theorem cell_2626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_2626 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2626 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2626 prefixEnd_2626 := by
    exact prefixLift 2626
  have htrace : WordTrace (prefixWord ++ tailWord_2626) baseStart_2626 baseEnd_2626 := by
    simpa [prefixWord, tailWord_2626, baseEnd_2626] using wordTrace_append hprefix tailTrace_2626
  have hstable : (prefixWord ++ tailWord_2626).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626).length < 2 ^ (prefixWord ++ tailWord_2626).sum := by decide
  have hdescent : baseEnd_2626 < baseStart_2626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646 : List Nat := [5, 2, 2, 3]
def baseStart_2646 : Nat := 118140960795 + 2646 * 2 ^ 59
def prefixEnd_2646 : Nat := 4983230072969 + 3 ^ 40 * 2646 * 2
def baseEnd_2646 : Nat := 1272316312197097724687

theorem tailTrace_2646 : CollatzResearch.WordTrace tailWord_2646 prefixEnd_2646 1272316312197097724687 := by
  unfold tailWord_2646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6031721776341796620737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64338365614312497287861 6031721776341796620737)
  ·
    refine ⟨4523791332256347465553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6031721776341796620737 4523791332256347465553)
    ·
      refine ⟨3392843499192260599165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4523791332256347465553 3392843499192260599165)
      ·
        refine ⟨1272316312197097724687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3392843499192260599165 1272316312197097724687)
        ·
          rfl

theorem cell_2646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_2646 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2646 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2646 prefixEnd_2646 := by
    exact prefixLift 2646
  have htrace : WordTrace (prefixWord ++ tailWord_2646) baseStart_2646 baseEnd_2646 := by
    simpa [prefixWord, tailWord_2646, baseEnd_2646] using wordTrace_append hprefix tailTrace_2646
  have hstable : (prefixWord ++ tailWord_2646).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646).length < 2 ^ (prefixWord ++ tailWord_2646).sum := by decide
  have hdescent : baseEnd_2646 < baseStart_2646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653 : List Nat := [1, 4, 4, 3]
def baseStart_2653 : Nat := 118140960795 + 2653 * 2 ^ 59
def prefixEnd_2653 : Nat := 4983230072969 + 3 ^ 40 * 2653 * 2
def baseEnd_2653 : Nat := 1275682228366670614643

theorem tailTrace_2653 : CollatzResearch.WordTrace tailWord_2653 prefixEnd_2653 1275682228366670614643 := by
  unfold tailWord_2653
  simp only [CollatzResearch.WordTrace]
  refine ⟨96762859396108941436613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64508572930739294291075 96762859396108941436613)
  ·
    refine ⟨18143036136770426519365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96762859396108941436613 18143036136770426519365)
    ·
      refine ⟨3401819275644454972381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18143036136770426519365 3401819275644454972381)
      ·
        refine ⟨1275682228366670614643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3401819275644454972381 1275682228366670614643)
        ·
          rfl

theorem cell_2653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_2653 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2653 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2653 prefixEnd_2653 := by
    exact prefixLift 2653
  have htrace : WordTrace (prefixWord ++ tailWord_2653) baseStart_2653 baseEnd_2653 := by
    simpa [prefixWord, tailWord_2653, baseEnd_2653] using wordTrace_append hprefix tailTrace_2653
  have hstable : (prefixWord ++ tailWord_2653).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653).length < 2 ^ (prefixWord ++ tailWord_2653).sum := by decide
  have hdescent : baseEnd_2653 < baseStart_2653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2662 : List Nat := [7]
def baseStart_2662 : Nat := 118140960795 + 2662 * 2 ^ 59
def prefixEnd_2662 : Nat := 4983230072969 + 3 ^ 40 * 2662 * 2
def baseEnd_2662 : Nat := 1517048693179741851785

theorem tailTrace_2662 : CollatzResearch.WordTrace tailWord_2662 prefixEnd_2662 1517048693179741851785 := by
  unfold tailWord_2662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1517048693179741851785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 64727410909002319009493 1517048693179741851785)
  ·
    rfl

theorem cell_2662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2662 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2662 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2662 prefixEnd_2662 := by
    exact prefixLift 2662
  have htrace : WordTrace (prefixWord ++ tailWord_2662) baseStart_2662 baseEnd_2662 := by
    simpa [prefixWord, tailWord_2662, baseEnd_2662] using wordTrace_append hprefix tailTrace_2662
  have hstable : (prefixWord ++ tailWord_2662).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2662).length < 2 ^ (prefixWord ++ tailWord_2662).sum := by decide
  have hdescent : baseEnd_2662 < baseStart_2662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2676 : List Nat := [2, 7]
def baseStart_2676 : Nat := 118140960795 + 2676 * 2 ^ 59
def prefixEnd_2676 : Nat := 4983230072969 + 3 ^ 40 * 2676 * 2
def baseEnd_2676 : Nat := 1143770370852935970983

theorem tailTrace_2676 : CollatzResearch.WordTrace tailWord_2676 prefixEnd_2676 1143770370852935970983 := by
  unfold tailWord_2676
  simp only [CollatzResearch.WordTrace]
  refine ⟨48800869156391934761941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65067825541855913015921 48800869156391934761941)
  ·
    refine ⟨1143770370852935970983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 48800869156391934761941 1143770370852935970983)
    ·
      rfl

theorem cell_2676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_2676 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2676 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2676 prefixEnd_2676 := by
    exact prefixLift 2676
  have htrace : WordTrace (prefixWord ++ tailWord_2676) baseStart_2676 baseEnd_2676 := by
    simpa [prefixWord, tailWord_2676, baseEnd_2676] using wordTrace_append hprefix tailTrace_2676
  have hstable : (prefixWord ++ tailWord_2676).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2676).length < 2 ^ (prefixWord ++ tailWord_2676).sum := by decide
  have hdescent : baseEnd_2676 < baseStart_2676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686 : List Nat := [4, 2, 6]
def baseStart_2686 : Nat := 118140960795 + 2686 * 2 ^ 59
def prefixEnd_2686 : Nat := 4983230072969 + 3 ^ 40 * 2686 * 2
def baseEnd_2686 : Nat := 430516706293457127193

theorem tailTrace_2686 : CollatzResearch.WordTrace tailWord_2686 prefixEnd_2686 430516706293457127193 := by
  unfold tailWord_2686
  simp only [CollatzResearch.WordTrace]
  refine ⟨12245808534569447173489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65310978851037051591941 12245808534569447173489)
  ·
    refine ⟨9184356400927085380117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12245808534569447173489 9184356400927085380117)
    ·
      refine ⟨430516706293457127193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9184356400927085380117 430516706293457127193)
      ·
        rfl

theorem cell_2686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_2686 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2686 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2686 prefixEnd_2686 := by
    exact prefixLift 2686
  have htrace : WordTrace (prefixWord ++ tailWord_2686) baseStart_2686 baseEnd_2686 := by
    simpa [prefixWord, tailWord_2686, baseEnd_2686] using wordTrace_append hprefix tailTrace_2686
  have hstable : (prefixWord ++ tailWord_2686).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686).length < 2 ^ (prefixWord ++ tailWord_2686).sum := by decide
  have hdescent : baseEnd_2686 < baseStart_2686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2694 : List Nat := [6, 5]
def baseStart_2694 : Nat := 118140960795 + 2694 * 2 ^ 59
def prefixEnd_2694 : Nat := 4983230072969 + 3 ^ 40 * 2694 * 2
def baseEnd_2694 : Nat := 287865973381561358435

theorem tailTrace_2694 : CollatzResearch.WordTrace tailWord_2694 prefixEnd_2694 287865973381561358435 := by
  unfold tailWord_2694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3070570382736654489973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65505501498381962452757 3070570382736654489973)
  ·
    refine ⟨287865973381561358435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3070570382736654489973 287865973381561358435)
    ·
      rfl

theorem cell_2694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_2694 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2694 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2694 prefixEnd_2694 := by
    exact prefixLift 2694
  have htrace : WordTrace (prefixWord ++ tailWord_2694) baseStart_2694 baseEnd_2694 := by
    simpa [prefixWord, tailWord_2694, baseEnd_2694] using wordTrace_append hprefix tailTrace_2694
  have hstable : (prefixWord ++ tailWord_2694).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2694).length < 2 ^ (prefixWord ++ tailWord_2694).sum := by decide
  have hdescent : baseEnd_2694 < baseStart_2694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701 : List Nat := [1, 10]
def baseStart_2701 : Nat := 118140960795 + 2701 * 2 ^ 59
def prefixEnd_2701 : Nat := 4983230072969 + 3 ^ 40 * 2701 * 2
def baseEnd_2701 : Nat := 288613954752577556203

theorem tailTrace_2701 : CollatzResearch.WordTrace tailWord_2701 prefixEnd_2701 288613954752577556203 := by
  unfold tailWord_2701
  simp only [CollatzResearch.WordTrace]
  refine ⟨98513563222213139183957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65675708814808759455971 98513563222213139183957)
  ·
    refine ⟨288613954752577556203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 10 98513563222213139183957 288613954752577556203)
    ·
      rfl

theorem cell_2701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_2701 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2701 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2701 prefixEnd_2701 := by
    exact prefixLift 2701
  have htrace : WordTrace (prefixWord ++ tailWord_2701) baseStart_2701 baseEnd_2701 := by
    simpa [prefixWord, tailWord_2701, baseEnd_2701] using wordTrace_append hprefix tailTrace_2701
  have hstable : (prefixWord ++ tailWord_2701).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701).length < 2 ^ (prefixWord ++ tailWord_2701).sum := by decide
  have hdescent : baseEnd_2701 < baseStart_2701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710 : List Nat := [5, 3, 3]
def baseStart_2710 : Nat := 118140960795 + 2710 * 2 ^ 59
def prefixEnd_2710 : Nat := 4983230072969 + 3 ^ 40 * 2710 * 2
def baseEnd_2710 : Nat := 868726935260223717143

theorem tailTrace_2710 : CollatzResearch.WordTrace tailWord_2710 prefixEnd_2710 868726935260223717143 := by
  unfold tailWord_2710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6177613761850479766349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65894546793071784174389 6177613761850479766349)
  ·
    refine ⟨2316605160693929912381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6177613761850479766349 2316605160693929912381)
    ·
      refine ⟨868726935260223717143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2316605160693929912381 868726935260223717143)
      ·
        rfl

theorem cell_2710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_2710 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2710 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2710 prefixEnd_2710 := by
    exact prefixLift 2710
  have htrace : WordTrace (prefixWord ++ tailWord_2710) baseStart_2710 baseEnd_2710 := by
    simpa [prefixWord, tailWord_2710, baseEnd_2710] using wordTrace_append hprefix tailTrace_2710
  have hstable : (prefixWord ++ tailWord_2710).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710).length < 2 ^ (prefixWord ++ tailWord_2710).sum := by decide
  have hdescent : baseEnd_2710 < baseStart_2710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719 : List Nat := [1, 1, 2, 8]
def baseStart_2719 : Nat := 118140960795 + 2719 * 2 ^ 59
def prefixEnd_2719 : Nat := 4983230072969 + 3 ^ 40 * 2719 * 2
def baseEnd_2719 : Nat := 1307418009394072148515

theorem tailTrace_2719 : CollatzResearch.WordTrace tailWord_2719 prefixEnd_2719 1307418009394072148515 := by
  unfold tailWord_2719
  simp only [CollatzResearch.WordTrace]
  refine ⟨99170077157002213339211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66113384771334808892807 99170077157002213339211)
  ·
    refine ⟨148755115735503320008817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99170077157002213339211 148755115735503320008817)
    ·
      refine ⟨111566336801627490006613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148755115735503320008817 111566336801627490006613)
      ·
        refine ⟨1307418009394072148515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 111566336801627490006613 1307418009394072148515)
        ·
          rfl

theorem cell_2719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_2719 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2719 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2719 prefixEnd_2719 := by
    exact prefixLift 2719
  have htrace : WordTrace (prefixWord ++ tailWord_2719) baseStart_2719 baseEnd_2719 := by
    simpa [prefixWord, tailWord_2719, baseEnd_2719] using wordTrace_append hprefix tailTrace_2719
  have hstable : (prefixWord ++ tailWord_2719).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719).length < 2 ^ (prefixWord ++ tailWord_2719).sum := by decide
  have hdescent : baseEnd_2719 < baseStart_2719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726 : List Nat := [9]
def baseStart_2726 : Nat := 118140960795 + 2726 * 2 ^ 59
def prefixEnd_2726 : Nat := 4983230072969 + 3 ^ 40 * 2726 * 2
def baseEnd_2726 : Nat := 388380422389228159547

theorem tailTrace_2726 : CollatzResearch.WordTrace tailWord_2726 prefixEnd_2726 388380422389228159547 := by
  unfold tailWord_2726
  simp only [CollatzResearch.WordTrace]
  refine ⟨388380422389228159547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 9 66283592087761605896021 388380422389228159547)
  ·
    rfl

theorem cell_2726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_2726 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2726 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2726 prefixEnd_2726 := by
    exact prefixLift 2726
  have htrace : WordTrace (prefixWord ++ tailWord_2726) baseStart_2726 baseEnd_2726 := by
    simpa [prefixWord, tailWord_2726, baseEnd_2726] using wordTrace_append hprefix tailTrace_2726
  have hstable : (prefixWord ++ tailWord_2726).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726).length < 2 ^ (prefixWord ++ tailWord_2726).sum := by decide
  have hdescent : baseEnd_2726 < baseStart_2726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740 : List Nat := [2, 5, 4]
def baseStart_2740 : Nat := 118140960795 + 2740 * 2 ^ 59
def prefixEnd_2740 : Nat := 4983230072969 + 3 ^ 40 * 2740 * 2
def baseEnd_2740 : Nat := 878343838601860545589

theorem tailTrace_2740 : CollatzResearch.WordTrace tailWord_2740 prefixEnd_2740 878343838601860545589 := by
  unfold tailWord_2740
  simp only [CollatzResearch.WordTrace]
  refine ⟨49968005040461399926837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66624006720615199902449 49968005040461399926837)
  ·
    refine ⟨4684500472543256243141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49968005040461399926837 4684500472543256243141)
    ·
      refine ⟨878343838601860545589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4684500472543256243141 878343838601860545589)
      ·
        rfl

theorem cell_2740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_2740 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2740 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2740 prefixEnd_2740 := by
    exact prefixLift 2740
  have htrace : WordTrace (prefixWord ++ tailWord_2740) baseStart_2740 baseEnd_2740 := by
    simpa [prefixWord, tailWord_2740, baseEnd_2740] using wordTrace_append hprefix tailTrace_2740
  have hstable : (prefixWord ++ tailWord_2740).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740).length < 2 ^ (prefixWord ++ tailWord_2740).sum := by decide
  have hdescent : baseEnd_2740 < baseStart_2740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782 : List Nat := [4, 6]
def baseStart_2782 : Nat := 118140960795 + 2782 * 2 ^ 59
def prefixEnd_2782 : Nat := 4983230072969 + 3 ^ 40 * 2782 * 2
def baseEnd_2782 : Nat := 594538335520101403609

theorem tailTrace_2782 : CollatzResearch.WordTrace tailWord_2782 prefixEnd_2782 594538335520101403609 := by
  unfold tailWord_2782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12683484491095496610325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67645250619175981921733 12683484491095496610325)
  ·
    refine ⟨594538335520101403609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12683484491095496610325 594538335520101403609)
    ·
      rfl

theorem cell_2782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_2782 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2782 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2782 prefixEnd_2782 := by
    exact prefixLift 2782
  have htrace : WordTrace (prefixWord ++ tailWord_2782) baseStart_2782 baseEnd_2782 := by
    simpa [prefixWord, tailWord_2782, baseEnd_2782] using wordTrace_append hprefix tailTrace_2782
  have hstable : (prefixWord ++ tailWord_2782).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782).length < 2 ^ (prefixWord ++ tailWord_2782).sum := by decide
  have hdescent : baseEnd_2782 < baseStart_2782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786 : List Nat := [3, 3, 5]
def baseStart_2786 : Nat := 118140960795 + 2786 * 2 ^ 59
def prefixEnd_2786 : Nat := 4983230072969 + 3 ^ 40 * 2786 * 2
def baseEnd_2786 : Nat := 893089757059037015873

theorem tailTrace_2786 : CollatzResearch.WordTrace tailWord_2786 prefixEnd_2786 893089757059037015873 := by
  unfold tailWord_2786
  simp only [CollatzResearch.WordTrace]
  refine ⟨25403441978568164007053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67742511942848437352141 25403441978568164007053)
  ·
    refine ⟨9526290741963061502645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25403441978568164007053 9526290741963061502645)
    ·
      refine ⟨893089757059037015873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9526290741963061502645 893089757059037015873)
      ·
        rfl

theorem cell_2786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_2786 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2786 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2786 prefixEnd_2786 := by
    exact prefixLift 2786
  have htrace : WordTrace (prefixWord ++ tailWord_2786) baseStart_2786 baseEnd_2786 := by
    simpa [prefixWord, tailWord_2786, baseEnd_2786] using wordTrace_append hprefix tailTrace_2786
  have hstable : (prefixWord ++ tailWord_2786).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786).length < 2 ^ (prefixWord ++ tailWord_2786).sum := by decide
  have hdescent : baseEnd_2786 < baseStart_2786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790 : List Nat := [7]
def baseStart_2790 : Nat := 118140960795 + 2790 * 2 ^ 59
def prefixEnd_2790 : Nat := 4983230072969 + 3 ^ 40 * 2790 * 2
def baseEnd_2790 : Nat := 1589994685934083424591

theorem tailTrace_2790 : CollatzResearch.WordTrace tailWord_2790 prefixEnd_2790 1589994685934083424591 := by
  unfold tailWord_2790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1589994685934083424591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 67839773266520892782549 1589994685934083424591)
  ·
    rfl

theorem cell_2790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2790 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2790 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2790 prefixEnd_2790 := by
    exact prefixLift 2790
  have htrace : WordTrace (prefixWord ++ tailWord_2790) baseStart_2790 baseEnd_2790 := by
    simpa [prefixWord, tailWord_2790, baseEnd_2790] using wordTrace_append hprefix tailTrace_2790
  have hstable : (prefixWord ++ tailWord_2790).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790).length < 2 ^ (prefixWord ++ tailWord_2790).sum := by decide
  have hdescent : baseEnd_2790 < baseStart_2790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791 : List Nat := [1, 1, 5, 5]
def baseStart_2791 : Nat := 118140960795 + 2791 * 2 ^ 59
def prefixEnd_2791 : Nat := 4983230072969 + 3 ^ 40 * 2791 * 2
def baseEnd_2791 : Nat := 1342038861423964730921

theorem tailTrace_2791 : CollatzResearch.WordTrace tailWord_2791 prefixEnd_2791 1342038861423964730921 := by
  unfold tailWord_2791
  simp only [CollatzResearch.WordTrace]
  refine ⟨101796132896158509960227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67864088597439006640151 101796132896158509960227)
  ·
    refine ⟨152694199344237764940341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101796132896158509960227 152694199344237764940341)
    ·
      refine ⟨14315081188522290463157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152694199344237764940341 14315081188522290463157)
      ·
        refine ⟨1342038861423964730921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14315081188522290463157 1342038861423964730921)
        ·
          rfl

theorem cell_2791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_2791 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2791 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2791 prefixEnd_2791 := by
    exact prefixLift 2791
  have htrace : WordTrace (prefixWord ++ tailWord_2791) baseStart_2791 baseEnd_2791 := by
    simpa [prefixWord, tailWord_2791, baseEnd_2791] using wordTrace_append hprefix tailTrace_2791
  have hstable : (prefixWord ++ tailWord_2791).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791).length < 2 ^ (prefixWord ++ tailWord_2791).sum := by decide
  have hdescent : baseEnd_2791 < baseStart_2791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822 : List Nat := [6, 2, 2, 2]
def baseStart_2822 : Nat := 118140960795 + 2822 * 2 ^ 59
def prefixEnd_2822 : Nat := 4983230072969 + 3 ^ 40 * 2822 * 2
def baseEnd_2822 : Nat := 1356945061603501815013

theorem tailTrace_2822 : CollatzResearch.WordTrace tailWord_2822 prefixEnd_2822 1356945061603501815013 := by
  unfold tailWord_2822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3216462368245337635585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68617863855900536225813 3216462368245337635585)
  ·
    refine ⟨2412346776184003226689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3216462368245337635585 2412346776184003226689)
    ·
      refine ⟨1809260082138002420017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2412346776184003226689 1809260082138002420017)
      ·
        refine ⟨1356945061603501815013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1809260082138002420017 1356945061603501815013)
        ·
          rfl

theorem cell_2822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_2822 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2822 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2822 prefixEnd_2822 := by
    exact prefixLift 2822
  have htrace : WordTrace (prefixWord ++ tailWord_2822) baseStart_2822 baseEnd_2822 := by
    simpa [prefixWord, tailWord_2822, baseEnd_2822] using wordTrace_append hprefix tailTrace_2822
  have hstable : (prefixWord ++ tailWord_2822).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822).length < 2 ^ (prefixWord ++ tailWord_2822).sum := by decide
  have hdescent : baseEnd_2822 < baseStart_2822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829 : List Nat := [1, 7, 2, 2]
def baseStart_2829 : Nat := 118140960795 + 2829 * 2 ^ 59
def prefixEnd_2829 : Nat := 4983230072969 + 3 ^ 40 * 2829 * 2
def baseEnd_2829 : Nat := 1360310977773074704969

theorem tailTrace_2829 : CollatzResearch.WordTrace tailWord_2829 prefixEnd_2829 1360310977773074704969 := by
  unfold tailWord_2829
  simp only [CollatzResearch.WordTrace]
  refine ⟨103182106758490999843541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68788071172327333229027 103182106758490999843541)
  ·
    refine ⟨2418330627152132808833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 103182106758490999843541 2418330627152132808833)
    ·
      refine ⟨1813747970364099606625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2418330627152132808833 1813747970364099606625)
      ·
        refine ⟨1360310977773074704969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1813747970364099606625 1360310977773074704969)
        ·
          rfl

theorem cell_2829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_2829 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2829 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2829 prefixEnd_2829 := by
    exact prefixLift 2829
  have htrace : WordTrace (prefixWord ++ tailWord_2829) baseStart_2829 baseEnd_2829 := by
    simpa [prefixWord, tailWord_2829, baseEnd_2829] using wordTrace_append hprefix tailTrace_2829
  have hstable : (prefixWord ++ tailWord_2829).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829).length < 2 ^ (prefixWord ++ tailWord_2829).sum := by decide
  have hdescent : baseEnd_2829 < baseStart_2829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836 : List Nat := [2, 4, 4, 2]
def baseStart_2836 : Nat := 118140960795 + 2836 * 2 ^ 59
def prefixEnd_2836 : Nat := 4983230072969 + 3 ^ 40 * 2836 * 2
def baseEnd_2836 : Nat := 1363676893942647594925

theorem tailTrace_2836 : CollatzResearch.WordTrace tailWord_2836 prefixEnd_2836 1363676893942647594925 := by
  unfold tailWord_2836
  simp only [CollatzResearch.WordTrace]
  refine ⟨51718708866565597674181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68958278488754130232241 51718708866565597674181)
  ·
    refine ⟨9697257912481049563909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51718708866565597674181 9697257912481049563909)
    ·
      refine ⟨1818235858590196793233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9697257912481049563909 1818235858590196793233)
      ·
        refine ⟨1363676893942647594925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1818235858590196793233 1363676893942647594925)
        ·
          rfl

theorem cell_2836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_2836 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2836 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2836 prefixEnd_2836 := by
    exact prefixLift 2836
  have htrace : WordTrace (prefixWord ++ tailWord_2836) baseStart_2836 baseEnd_2836 := by
    simpa [prefixWord, tailWord_2836, baseEnd_2836] using wordTrace_append hprefix tailTrace_2836
  have hstable : (prefixWord ++ tailWord_2836).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836).length < 2 ^ (prefixWord ++ tailWord_2836).sum := by decide
  have hdescent : baseEnd_2836 < baseStart_2836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838 : List Nat := [5, 4]
def baseStart_2838 : Nat := 118140960795 + 2838 * 2 ^ 59
def prefixEnd_2838 : Nat := 4983230072969 + 3 ^ 40 * 2838 * 2
def baseEnd_2838 : Nat := 1213012074912721135795

theorem tailTrace_2838 : CollatzResearch.WordTrace tailWord_2838 prefixEnd_2838 1213012074912721135795 := by
  unfold tailWord_2838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6469397732867846057573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69006909150590357947445 6469397732867846057573)
  ·
    refine ⟨1213012074912721135795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6469397732867846057573 1213012074912721135795)
    ·
      rfl

theorem cell_2838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_2838 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2838 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2838 prefixEnd_2838 := by
    exact prefixLift 2838
  have htrace : WordTrace (prefixWord ++ tailWord_2838) baseStart_2838 baseEnd_2838 := by
    simpa [prefixWord, tailWord_2838, baseEnd_2838] using wordTrace_append hprefix tailTrace_2838
  have hstable : (prefixWord ++ tailWord_2838).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838).length < 2 ^ (prefixWord ++ tailWord_2838).sum := by decide
  have hdescent : baseEnd_2838 < baseStart_2838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854 : List Nat := [8]
def baseStart_2854 : Nat := 118140960795 + 2854 * 2 ^ 59
def prefixEnd_2854 : Nat := 4983230072969 + 3 ^ 40 * 2854 * 2
def baseEnd_2854 : Nat := 813233841155627105497

theorem tailTrace_2854 : CollatzResearch.WordTrace tailWord_2854 prefixEnd_2854 813233841155627105497 := by
  unfold tailWord_2854
  simp only [CollatzResearch.WordTrace]
  refine ⟨813233841155627105497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 69395954445280179669077 813233841155627105497)
  ·
    rfl

theorem cell_2854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_2854 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2854 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2854 prefixEnd_2854 := by
    exact prefixLift 2854
  have htrace : WordTrace (prefixWord ++ tailWord_2854) baseStart_2854 baseEnd_2854 := by
    simpa [prefixWord, tailWord_2854, baseEnd_2854] using wordTrace_append hprefix tailTrace_2854
  have hstable : (prefixWord ++ tailWord_2854).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854).length < 2 ^ (prefixWord ++ tailWord_2854).sum := by decide
  have hdescent : baseEnd_2854 < baseStart_2854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855 : List Nat := [1, 1, 9]
def baseStart_2855 : Nat := 118140960795 + 2855 * 2 ^ 59
def prefixEnd_2855 : Nat := 4983230072969 + 3 ^ 40 * 2855 * 2
def baseEnd_2855 : Nat := 915208634744801721299

theorem tailTrace_2855 : CollatzResearch.WordTrace tailWord_2855 prefixEnd_2855 915208634744801721299 := by
  unfold tailWord_2855
  simp only [CollatzResearch.WordTrace]
  refine ⟨104130404664297440290019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69420269776198293526679 104130404664297440290019)
  ·
    refine ⟨156195606996446160435029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104130404664297440290019 156195606996446160435029)
    ·
      refine ⟨915208634744801721299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 9 156195606996446160435029 915208634744801721299)
      ·
        rfl

theorem cell_2855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_2855 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2855 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2855 prefixEnd_2855 := by
    exact prefixLift 2855
  have htrace : WordTrace (prefixWord ++ tailWord_2855) baseStart_2855 baseEnd_2855 := by
    simpa [prefixWord, tailWord_2855, baseEnd_2855] using wordTrace_append hprefix tailTrace_2855
  have hstable : (prefixWord ++ tailWord_2855).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855).length < 2 ^ (prefixWord ++ tailWord_2855).sum := by decide
  have hdescent : baseEnd_2855 < baseStart_2855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882 : List Nat := [3, 7]
def baseStart_2882 : Nat := 118140960795 + 2882 * 2 ^ 59
def prefixEnd_2882 : Nat := 4983230072969 + 3 ^ 40 * 2882 * 2
def baseEnd_2882 : Nat := 615909231834849911267

theorem tailTrace_2882 : CollatzResearch.WordTrace tailWord_2882 prefixEnd_2882 615909231834849911267 := by
  unfold tailWord_2882
  simp only [CollatzResearch.WordTrace]
  refine ⟨26278793891620262880725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70076783710987367681933 26278793891620262880725)
  ·
    refine ⟨615909231834849911267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 26278793891620262880725 615909231834849911267)
    ·
      rfl

theorem cell_2882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_2882 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2882 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2882 prefixEnd_2882 := by
    exact prefixLift 2882
  have htrace : WordTrace (prefixWord ++ tailWord_2882) baseStart_2882 baseEnd_2882 := by
    simpa [prefixWord, tailWord_2882, baseEnd_2882] using wordTrace_append hprefix tailTrace_2882
  have hstable : (prefixWord ++ tailWord_2882).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882).length < 2 ^ (prefixWord ++ tailWord_2882).sum := by decide
  have hdescent : baseEnd_2882 < baseStart_2882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902 : List Nat := [5, 2, 5]
def baseStart_2902 : Nat := 118140960795 + 2902 * 2 ^ 59
def prefixEnd_2902 : Nat := 4983230072969 + 3 ^ 40 * 2902 * 2
def baseEnd_2902 : Nat := 465137558323349709599

theorem tailTrace_2902 : CollatzResearch.WordTrace tailWord_2902 prefixEnd_2902 465137558323349709599 := by
  unfold tailWord_2902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6615289718376529203185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70563090329349644833973 6615289718376529203185)
  ·
    refine ⟨4961467288782396902389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6615289718376529203185 4961467288782396902389)
    ·
      refine ⟨465137558323349709599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4961467288782396902389 465137558323349709599)
      ·
        rfl

theorem cell_2902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_2902 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2902 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2902 prefixEnd_2902 := by
    exact prefixLift 2902
  have htrace : WordTrace (prefixWord ++ tailWord_2902) baseStart_2902 baseEnd_2902 := by
    simpa [prefixWord, tailWord_2902, baseEnd_2902] using wordTrace_append hprefix tailTrace_2902
  have hstable : (prefixWord ++ tailWord_2902).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902).length < 2 ^ (prefixWord ++ tailWord_2902).sum := by decide
  have hdescent : baseEnd_2902 < baseStart_2902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909 : List Nat := [1, 4, 7]
def baseStart_2909 : Nat := 118140960795 + 2909 * 2 ^ 59
def prefixEnd_2909 : Nat := 4983230072969 + 3 ^ 40 * 2909 * 2
def baseEnd_2909 : Nat := 466259530379874006251

theorem tailTrace_2909 : CollatzResearch.WordTrace tailWord_2909 prefixEnd_2909 466259530379874006251 := by
  unfold tailWord_2909
  simp only [CollatzResearch.WordTrace]
  refine ⟨106099946468664662755781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70733297645776441837187 106099946468664662755781)
  ·
    refine ⟨19893739962874624266709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106099946468664662755781 19893739962874624266709)
    ·
      refine ⟨466259530379874006251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 19893739962874624266709 466259530379874006251)
      ·
        rfl

theorem cell_2909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_2909 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2909 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2909 prefixEnd_2909 := by
    exact prefixLift 2909
  have htrace : WordTrace (prefixWord ++ tailWord_2909) baseStart_2909 baseEnd_2909 := by
    simpa [prefixWord, tailWord_2909, baseEnd_2909] using wordTrace_append hprefix tailTrace_2909
  have hstable : (prefixWord ++ tailWord_2909).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909).length < 2 ^ (prefixWord ++ tailWord_2909).sum := by decide
  have hdescent : baseEnd_2909 < baseStart_2909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910 : List Nat := [4, 4, 3]
def baseStart_2910 : Nat := 118140960795 + 2910 * 2 ^ 59
def prefixEnd_2910 : Nat := 4983230072969 + 3 ^ 40 * 2910 * 2
def baseEnd_2910 : Nat := 932839624204469240117

theorem tailTrace_2910 : CollatzResearch.WordTrace tailWord_2910 prefixEnd_2910 932839624204469240117 := by
  unfold tailWord_2910
  simp only [CollatzResearch.WordTrace]
  refine ⟨13267052433130229192773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70757612976694555694789 13267052433130229192773)
  ·
    refine ⟨2487572331211917973645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13267052433130229192773 2487572331211917973645)
    ·
      refine ⟨932839624204469240117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2487572331211917973645 932839624204469240117)
      ·
        rfl

theorem cell_2910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_2910 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2910 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2910 prefixEnd_2910 := by
    exact prefixLift 2910
  have htrace : WordTrace (prefixWord ++ tailWord_2910) baseStart_2910 baseEnd_2910 := by
    simpa [prefixWord, tailWord_2910, baseEnd_2910] using wordTrace_append hprefix tailTrace_2910
  have hstable : (prefixWord ++ tailWord_2910).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910).length < 2 ^ (prefixWord ++ tailWord_2910).sum := by decide
  have hdescent : baseEnd_2910 < baseStart_2910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918 : List Nat := [7]
def baseStart_2918 : Nat := 118140960795 + 2918 * 2 ^ 59
def prefixEnd_2918 : Nat := 4983230072969 + 3 ^ 40 * 2918 * 2
def baseEnd_2918 : Nat := 1662940678688424997397

theorem tailTrace_2918 : CollatzResearch.WordTrace tailWord_2918 prefixEnd_2918 1662940678688424997397 := by
  unfold tailWord_2918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662940678688424997397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 70952135624039466555605 1662940678688424997397)
  ·
    rfl

theorem cell_2918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2918 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2918 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2918 prefixEnd_2918 := by
    exact prefixLift 2918
  have htrace : WordTrace (prefixWord ++ tailWord_2918) baseStart_2918 baseEnd_2918 := by
    simpa [prefixWord, tailWord_2918, baseEnd_2918] using wordTrace_append hprefix tailTrace_2918
  have hstable : (prefixWord ++ tailWord_2918).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918).length < 2 ^ (prefixWord ++ tailWord_2918).sum := by decide
  have hdescent : baseEnd_2918 < baseStart_2918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922 : List Nat := [3, 1, 3, 5]
def baseStart_2922 : Nat := 118140960795 + 2922 * 2 ^ 59
def prefixEnd_2922 : Nat := 4983230072969 + 3 ^ 40 * 2922 * 2
def baseEnd_2922 : Nat := 1405029578311685957243

theorem tailTrace_2922 : CollatzResearch.WordTrace tailWord_2922 prefixEnd_2922 1405029578311685957243 := by
  unfold tailWord_2922
  simp only [CollatzResearch.WordTrace]
  refine ⟨26643523855391970744755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71049396947711921986013 26643523855391970744755)
  ·
    refine ⟨39965285783087956117133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26643523855391970744755 39965285783087956117133)
    ·
      refine ⟨14986982168657983543925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39965285783087956117133 14986982168657983543925)
      ·
        refine ⟨1405029578311685957243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14986982168657983543925 1405029578311685957243)
        ·
          rfl

theorem cell_2922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_2922 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2922 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2922 prefixEnd_2922 := by
    exact prefixLift 2922
  have htrace : WordTrace (prefixWord ++ tailWord_2922) baseStart_2922 baseEnd_2922 := by
    simpa [prefixWord, tailWord_2922, baseEnd_2922] using wordTrace_append hprefix tailTrace_2922
  have hstable : (prefixWord ++ tailWord_2922).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922).length < 2 ^ (prefixWord ++ tailWord_2922).sum := by decide
  have hdescent : baseEnd_2922 < baseStart_2922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950 : List Nat := [6, 3]
def baseStart_2950 : Nat := 118140960795 + 2950 * 2 ^ 59
def prefixEnd_2950 : Nat := 4983230072969 + 3 ^ 40 * 2950 * 2
def baseEnd_2950 : Nat := 1260882882657757792949

theorem tailTrace_2950 : CollatzResearch.WordTrace tailWord_2950 prefixEnd_2950 1260882882657757792949 := by
  unfold tailWord_2950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362354353754020781197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71730226213419109998869 3362354353754020781197)
  ·
    refine ⟨1260882882657757792949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3362354353754020781197 1260882882657757792949)
    ·
      rfl

theorem cell_2950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_2950 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2950 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2950 prefixEnd_2950 := by
    exact prefixLift 2950
  have htrace : WordTrace (prefixWord ++ tailWord_2950) baseStart_2950 baseEnd_2950 := by
    simpa [prefixWord, tailWord_2950, baseEnd_2950] using wordTrace_append hprefix tailTrace_2950
  have hstable : (prefixWord ++ tailWord_2950).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950).length < 2 ^ (prefixWord ++ tailWord_2950).sum := by decide
  have hdescent : baseEnd_2950 < baseStart_2950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957 : List Nat := [1, 8]
def baseStart_2957 : Nat := 118140960795 + 2957 * 2 ^ 59
def prefixEnd_2957 : Nat := 4983230072969 + 3 ^ 40 * 2957 * 2
def baseEnd_2957 : Nat := 1263874808141822584021

theorem tailTrace_2957 : CollatzResearch.WordTrace tailWord_2957 prefixEnd_2957 1263874808141822584021 := by
  unfold tailWord_2957
  simp only [CollatzResearch.WordTrace]
  refine ⟨107850650294768860503125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71900433529845907002083 107850650294768860503125)
  ·
    refine ⟨1263874808141822584021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 107850650294768860503125 1263874808141822584021)
    ·
      rfl

theorem cell_2957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_2957 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2957 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2957 prefixEnd_2957 := by
    exact prefixLift 2957
  have htrace : WordTrace (prefixWord ++ tailWord_2957) baseStart_2957 baseEnd_2957 := by
    simpa [prefixWord, tailWord_2957, baseEnd_2957] using wordTrace_append hprefix tailTrace_2957
  have hstable : (prefixWord ++ tailWord_2957).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957).length < 2 ^ (prefixWord ++ tailWord_2957).sum := by decide
  have hdescent : baseEnd_2957 < baseStart_2957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968 : List Nat := [2, 1, 2, 7]
def baseStart_2968 : Nat := 118140960795 + 2968 * 2 ^ 59
def prefixEnd_2968 : Nat := 4983230072969 + 3 ^ 40 * 2968 * 2
def baseEnd_2968 : Nat := 1427148455997450662669

theorem tailTrace_2968 : CollatzResearch.WordTrace tailWord_2968 prefixEnd_2968 1427148455997450662669 := by
  unfold tailWord_2968
  simp only [CollatzResearch.WordTrace]
  refine ⟨54125926627458869576779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72167902169945159435705 54125926627458869576779)
  ·
    refine ⟨81188889941188304365169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54125926627458869576779 81188889941188304365169)
    ·
      refine ⟨60891667455891228273877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81188889941188304365169 60891667455891228273877)
      ·
        refine ⟨1427148455997450662669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 60891667455891228273877 1427148455997450662669)
        ·
          rfl

theorem cell_2968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_2968 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2968 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2968 prefixEnd_2968 := by
    exact prefixLift 2968
  have htrace : WordTrace (prefixWord ++ tailWord_2968) baseStart_2968 baseEnd_2968 := by
    simpa [prefixWord, tailWord_2968, baseEnd_2968] using wordTrace_append hprefix tailTrace_2968
  have hstable : (prefixWord ++ tailWord_2968).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968).length < 2 ^ (prefixWord ++ tailWord_2968).sum := by decide
  have hdescent : baseEnd_2968 < baseStart_2968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974 : List Nat := [4, 3, 1, 4]
def baseStart_2974 : Nat := 118140960795 + 2974 * 2 ^ 59
def prefixEnd_2974 : Nat := 4983230072969 + 3 ^ 40 * 2974 * 2
def baseEnd_2974 : Nat := 1430033526999941711203

theorem tailTrace_2974 : CollatzResearch.WordTrace tailWord_2974 prefixEnd_2974 1430033526999941711203 := by
  unfold tailWord_2974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13558836404147595483997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72313794155453842581317 13558836404147595483997)
  ·
    refine ⟨5084563651555348306499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13558836404147595483997 5084563651555348306499)
    ·
      refine ⟨7626845477333022459749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5084563651555348306499 7626845477333022459749)
      ·
        refine ⟨1430033526999941711203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7626845477333022459749 1430033526999941711203)
        ·
          rfl

theorem cell_2974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_2974 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2974 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2974 prefixEnd_2974 := by
    exact prefixLift 2974
  have htrace : WordTrace (prefixWord ++ tailWord_2974) baseStart_2974 baseEnd_2974 := by
    simpa [prefixWord, tailWord_2974, baseEnd_2974] using wordTrace_append hprefix tailTrace_2974
  have hstable : (prefixWord ++ tailWord_2974).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974).length < 2 ^ (prefixWord ++ tailWord_2974).sum := by decide
  have hdescent : baseEnd_2974 < baseStart_2974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982 : List Nat := [10]
def baseStart_2982 : Nat := 118140960795 + 2982 * 2 ^ 59
def prefixEnd_2982 : Nat := 4983230072969 + 3 ^ 40 * 2982 * 2
def baseEnd_2982 : Nat := 212426709383199472975

theorem tailTrace_2982 : CollatzResearch.WordTrace tailWord_2982 prefixEnd_2982 212426709383199472975 := by
  unfold tailWord_2982
  simp only [CollatzResearch.WordTrace]
  refine ⟨212426709383199472975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 10 72508316802798753442133 212426709383199472975)
  ·
    rfl

theorem cell_2982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_2982 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2982 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2982 prefixEnd_2982 := by
    exact prefixLift 2982
  have htrace : WordTrace (prefixWord ++ tailWord_2982) baseStart_2982 baseEnd_2982 := by
    simpa [prefixWord, tailWord_2982, baseEnd_2982] using wordTrace_append hprefix tailTrace_2982
  have hstable : (prefixWord ++ tailWord_2982).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982).length < 2 ^ (prefixWord ++ tailWord_2982).sum := by decide
  have hdescent : baseEnd_2982 < baseStart_2982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986 : List Nat := [3, 1, 7]
def baseStart_2986 : Nat := 118140960795 + 2986 * 2 ^ 59
def prefixEnd_2986 : Nat := 4983230072969 + 3 ^ 40 * 2986 * 2
def baseEnd_2986 : Nat := 957202446003282538847

theorem tailTrace_2986 : CollatzResearch.WordTrace tailWord_2986 prefixEnd_2986 957202446003282538847 := by
  unfold tailWord_2986
  simp only [CollatzResearch.WordTrace]
  refine ⟨27227091797426703327203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72605578126471208872541 27227091797426703327203)
  ·
    refine ⟨40840637696140054990805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27227091797426703327203 40840637696140054990805)
    ·
      refine ⟨957202446003282538847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 40840637696140054990805 957202446003282538847)
      ·
        rfl

theorem cell_2986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_2986 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_2986 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_2986 prefixEnd_2986 := by
    exact prefixLift 2986
  have htrace : WordTrace (prefixWord ++ tailWord_2986) baseStart_2986 baseEnd_2986 := by
    simpa [prefixWord, tailWord_2986, baseEnd_2986] using wordTrace_append hprefix tailTrace_2986
  have hstable : (prefixWord ++ tailWord_2986).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986).length < 2 ^ (prefixWord ++ tailWord_2986).sum := by decide
  have hdescent : baseEnd_2986 < baseStart_2986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009 : List Nat := [1, 2, 8]
def baseStart_3009 : Nat := 118140960795 + 3009 * 2 ^ 59
def prefixEnd_3009 : Nat := 4983230072969 + 3 ^ 40 * 3009 * 2
def baseEnd_3009 : Nat := 964575405231870773989

theorem tailTrace_3009 : CollatzResearch.WordTrace tailWord_3009 prefixEnd_3009 964575405231870773989 := by
  unfold tailWord_3009
  simp only [CollatzResearch.WordTrace]
  refine ⟨109747246106381741396081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73164830737587827597387 109747246106381741396081)
  ·
    refine ⟨82310434579786306047061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109747246106381741396081 82310434579786306047061)
    ·
      refine ⟨964575405231870773989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 82310434579786306047061 964575405231870773989)
      ·
        rfl

theorem cell_3009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_3009 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3009 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3009 prefixEnd_3009 := by
    exact prefixLift 3009
  have htrace : WordTrace (prefixWord ++ tailWord_3009) baseStart_3009 baseEnd_3009 := by
    simpa [prefixWord, tailWord_3009, baseEnd_3009] using wordTrace_append hprefix tailTrace_3009
  have hstable : (prefixWord ++ tailWord_3009).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009).length < 2 ^ (prefixWord ++ tailWord_3009).sum := by decide
  have hdescent : baseEnd_3009 < baseStart_3009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3038 : List Nat := [4, 5]
def baseStart_3038 : Nat := 118140960795 + 3038 * 2 ^ 59
def prefixEnd_3038 : Nat := 4983230072969 + 3 ^ 40 * 3038 * 2
def baseEnd_3038 : Nat := 1298495660171715166427

theorem tailTrace_3038 : CollatzResearch.WordTrace tailWord_3038 prefixEnd_3038 1298495660171715166427 := by
  unfold tailWord_3038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13850620375164961775221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73869975334213129467845 13850620375164961775221)
  ·
    refine ⟨1298495660171715166427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13850620375164961775221 1298495660171715166427)
    ·
      rfl

theorem cell_3038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_3038 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3038 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3038 prefixEnd_3038 := by
    exact prefixLift 3038
  have htrace : WordTrace (prefixWord ++ tailWord_3038) baseStart_3038 baseEnd_3038 := by
    simpa [prefixWord, tailWord_3038, baseEnd_3038] using wordTrace_append hprefix tailTrace_3038
  have hstable : (prefixWord ++ tailWord_3038).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3038).length < 2 ^ (prefixWord ++ tailWord_3038).sum := by decide
  have hdescent : baseEnd_3038 < baseStart_3038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046 : List Nat := [7]
def baseStart_3046 : Nat := 118140960795 + 3046 * 2 ^ 59
def prefixEnd_3046 : Nat := 4983230072969 + 3 ^ 40 * 3046 * 2
def baseEnd_3046 : Nat := 1735886671442766570203

theorem tailTrace_3046 : CollatzResearch.WordTrace tailWord_3046 prefixEnd_3046 1735886671442766570203 := by
  unfold tailWord_3046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735886671442766570203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 74064497981558040328661 1735886671442766570203)
  ·
    rfl

theorem cell_3046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3046 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3046 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3046 prefixEnd_3046 := by
    exact prefixLift 3046
  have htrace : WordTrace (prefixWord ++ tailWord_3046) baseStart_3046 baseEnd_3046 := by
    simpa [prefixWord, tailWord_3046, baseEnd_3046] using wordTrace_append hprefix tailTrace_3046
  have hstable : (prefixWord ++ tailWord_3046).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046).length < 2 ^ (prefixWord ++ tailWord_3046).sum := by decide
  have hdescent : baseEnd_3046 < baseStart_3046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3053 : List Nat := [1, 5, 1, 5]
def baseStart_3053 : Nat := 118140960795 + 3053 * 2 ^ 59
def prefixEnd_3053 : Nat := 4983230072969 + 3 ^ 40 * 3053 * 2
def baseEnd_3053 : Nat := 1468020295199407183565

theorem tailTrace_3053 : CollatzResearch.WordTrace tailWord_3053 prefixEnd_3053 1468020295199407183565 := by
  unfold tailWord_3053
  simp only [CollatzResearch.WordTrace]
  refine ⟨111352057946977255997813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74234705297984837331875 111352057946977255997813)
  ·
    refine ⟨10439255432529117749795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111352057946977255997813 10439255432529117749795)
    ·
      refine ⟨15658883148793676624693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10439255432529117749795 15658883148793676624693)
      ·
        refine ⟨1468020295199407183565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15658883148793676624693 1468020295199407183565)
        ·
          rfl

theorem cell_3053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_3053 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3053 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3053 prefixEnd_3053 := by
    exact prefixLift 3053
  have htrace : WordTrace (prefixWord ++ tailWord_3053) baseStart_3053 baseEnd_3053 := by
    simpa [prefixWord, tailWord_3053, baseEnd_3053] using wordTrace_append hprefix tailTrace_3053
  have hstable : (prefixWord ++ tailWord_3053).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3053).length < 2 ^ (prefixWord ++ tailWord_3053).sum := by decide
  have hdescent : baseEnd_3053 < baseStart_3053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078 : List Nat := [6, 2, 1, 3]
def baseStart_3078 : Nat := 118140960795 + 3078 * 2 ^ 59
def prefixEnd_3078 : Nat := 4983230072969 + 3 ^ 40 * 3078 * 2
def baseEnd_3078 : Nat := 1480041424376453219123

theorem tailTrace_3078 : CollatzResearch.WordTrace tailWord_3078 prefixEnd_3078 1480041424376453219123 := by
  unfold tailWord_3078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3508246339262703926809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74842588570937683771925 3508246339262703926809)
  ·
    refine ⟨2631184754447027945107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3508246339262703926809 2631184754447027945107)
    ·
      refine ⟨3946777131670541917661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2631184754447027945107 3946777131670541917661)
      ·
        refine ⟨1480041424376453219123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3946777131670541917661 1480041424376453219123)
        ·
          rfl

theorem cell_3078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_3078 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3078 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3078 prefixEnd_3078 := by
    exact prefixLift 3078
  have htrace : WordTrace (prefixWord ++ tailWord_3078) baseStart_3078 baseEnd_3078 := by
    simpa [prefixWord, tailWord_3078, baseEnd_3078] using wordTrace_append hprefix tailTrace_3078
  have hstable : (prefixWord ++ tailWord_3078).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078).length < 2 ^ (prefixWord ++ tailWord_3078).sum := by decide
  have hdescent : baseEnd_3078 < baseStart_3078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085 : List Nat := [1, 7, 1, 3]
def baseStart_3085 : Nat := 118140960795 + 3085 * 2 ^ 59
def prefixEnd_3085 : Nat := 4983230072969 + 3 ^ 40 * 3085 * 2
def baseEnd_3085 : Nat := 1483407340546026109079

theorem tailTrace_3085 : CollatzResearch.WordTrace tailWord_3085 prefixEnd_3085 1483407340546026109079 := by
  unfold tailWord_3085
  simp only [CollatzResearch.WordTrace]
  refine ⟨112519193831046721162709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75012795887364480775139 112519193831046721162709)
  ·
    refine ⟨2637168605415157527251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 112519193831046721162709 2637168605415157527251)
    ·
      refine ⟨3955752908122736290877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2637168605415157527251 3955752908122736290877)
      ·
        refine ⟨1483407340546026109079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3955752908122736290877 1483407340546026109079)
        ·
          rfl

theorem cell_3085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_3085 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3085 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3085 prefixEnd_3085 := by
    exact prefixLift 3085
  have htrace : WordTrace (prefixWord ++ tailWord_3085) baseStart_3085 baseEnd_3085 := by
    simpa [prefixWord, tailWord_3085, baseEnd_3085] using wordTrace_append hprefix tailTrace_3085
  have hstable : (prefixWord ++ tailWord_3085).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085).length < 2 ^ (prefixWord ++ tailWord_3085).sum := by decide
  have hdescent : baseEnd_3085 < baseStart_3085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092 : List Nat := [2, 4, 3, 3]
def baseStart_3092 : Nat := 118140960795 + 3092 * 2 ^ 59
def prefixEnd_3092 : Nat := 4983230072969 + 3 ^ 40 * 3092 * 2
def baseEnd_3092 : Nat := 1486773256715598999035

theorem tailTrace_3092 : CollatzResearch.WordTrace tailWord_3092 prefixEnd_3092 1486773256715598999035 := by
  unfold tailWord_3092
  simp only [CollatzResearch.WordTrace]
  refine ⟨56387252402843458333765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75183003203791277778353 56387252402843458333765)
  ·
    refine ⟨10572609825533148437581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56387252402843458333765 10572609825533148437581)
    ·
      refine ⟨3964728684574930664093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10572609825533148437581 3964728684574930664093)
      ·
        refine ⟨1486773256715598999035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3964728684574930664093 1486773256715598999035)
        ·
          rfl

theorem cell_3092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_3092 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3092 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3092 prefixEnd_3092 := by
    exact prefixLift 3092
  have htrace : WordTrace (prefixWord ++ tailWord_3092) baseStart_3092 baseEnd_3092 := by
    simpa [prefixWord, tailWord_3092, baseEnd_3092] using wordTrace_append hprefix tailTrace_3092
  have hstable : (prefixWord ++ tailWord_3092).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092).length < 2 ^ (prefixWord ++ tailWord_3092).sum := by decide
  have hdescent : baseEnd_3092 < baseStart_3092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094 : List Nat := [5, 6]
def baseStart_3094 : Nat := 118140960795 + 3094 * 2 ^ 59
def prefixEnd_3094 : Nat := 4983230072969 + 3 ^ 40 * 3094 * 2
def baseEnd_3094 : Nat := 330607766011058373751

theorem tailTrace_3094 : CollatzResearch.WordTrace tailWord_3094 prefixEnd_3094 330607766011058373751 := by
  unfold tailWord_3094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7052965674902578640021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75231633865627505493557 7052965674902578640021)
  ·
    refine ⟨330607766011058373751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7052965674902578640021 330607766011058373751)
    ·
      rfl

theorem cell_3094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_3094 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3094 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3094 prefixEnd_3094 := by
    exact prefixLift 3094
  have htrace : WordTrace (prefixWord ++ tailWord_3094) baseStart_3094 baseEnd_3094 := by
    simpa [prefixWord, tailWord_3094, baseEnd_3094] using wordTrace_append hprefix tailTrace_3094
  have hstable : (prefixWord ++ tailWord_3094).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094).length < 2 ^ (prefixWord ++ tailWord_3094).sum := by decide
  have hdescent : baseEnd_3094 < baseStart_3094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3110 : List Nat := [8]
def baseStart_3110 : Nat := 118140960795 + 3110 * 2 ^ 59
def prefixEnd_3110 : Nat := 4983230072969 + 3 ^ 40 * 3110 * 2
def baseEnd_3110 : Nat := 886179833909968678303

theorem tailTrace_3110 : CollatzResearch.WordTrace tailWord_3110 prefixEnd_3110 886179833909968678303 := by
  unfold tailWord_3110
  simp only [CollatzResearch.WordTrace]
  refine ⟨886179833909968678303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 75620679160317327215189 886179833909968678303)
  ·
    rfl

theorem cell_3110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_3110 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3110 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3110 prefixEnd_3110 := by
    exact prefixLift 3110
  have htrace : WordTrace (prefixWord ++ tailWord_3110) baseStart_3110 baseEnd_3110 := by
    simpa [prefixWord, tailWord_3110, baseEnd_3110] using wordTrace_append hprefix tailTrace_3110
  have hstable : (prefixWord ++ tailWord_3110).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3110).length < 2 ^ (prefixWord ++ tailWord_3110).sum := by decide
  have hdescent : baseEnd_3110 < baseStart_3110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112 : List Nat := [2, 1, 5, 4]
def baseStart_3112 : Nat := 118140960795 + 3112 * 2 ^ 59
def prefixEnd_3112 : Nat := 4983230072969 + 3 ^ 40 * 3112 * 2
def baseEnd_3112 : Nat := 1496390160057235827481

theorem tailTrace_3112 : CollatzResearch.WordTrace tailWord_3112 prefixEnd_3112 1496390160057235827481 := by
  unfold tailWord_3112
  simp only [CollatzResearch.WordTrace]
  refine ⟨56751982366615166197795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75669309822153554930393 56751982366615166197795)
  ·
    refine ⟨85127973549922749296693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56751982366615166197795 85127973549922749296693)
    ·
      refine ⟨7980747520305257746565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85127973549922749296693 7980747520305257746565)
      ·
        refine ⟨1496390160057235827481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7980747520305257746565 1496390160057235827481)
        ·
          rfl

theorem cell_3112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_3112 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3112 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3112 prefixEnd_3112 := by
    exact prefixLift 3112
  have htrace : WordTrace (prefixWord ++ tailWord_3112) baseStart_3112 baseEnd_3112 := by
    simpa [prefixWord, tailWord_3112, baseEnd_3112] using wordTrace_append hprefix tailTrace_3112
  have hstable : (prefixWord ++ tailWord_3112).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112).length < 2 ^ (prefixWord ++ tailWord_3112).sum := by decide
  have hdescent : baseEnd_3112 < baseStart_3112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117 : List Nat := [1, 5, 5]
def baseStart_3117 : Nat := 118140960795 + 3117 * 2 ^ 59
def prefixEnd_3117 : Nat := 4983230072969 + 3 ^ 40 * 3117 * 2
def baseEnd_3117 : Nat := 999196257261763356395

theorem tailTrace_3117 : CollatzResearch.WordTrace tailWord_3117 prefixEnd_3117 999196257261763356395 := by
  unfold tailWord_3117
  simp only [CollatzResearch.WordTrace]
  refine ⟨113686329715116186327605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75790886476744124218403 113686329715116186327605)
  ·
    refine ⟨10658093410792142468213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113686329715116186327605 10658093410792142468213)
    ·
      refine ⟨999196257261763356395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10658093410792142468213 999196257261763356395)
      ·
        rfl

theorem cell_3117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_3117 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3117 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3117 prefixEnd_3117 := by
    exact prefixLift 3117
  have htrace : WordTrace (prefixWord ++ tailWord_3117) baseStart_3117 baseEnd_3117 := by
    simpa [prefixWord, tailWord_3117, baseEnd_3117] using wordTrace_append hprefix tailTrace_3117
  have hstable : (prefixWord ++ tailWord_3117).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117).length < 2 ^ (prefixWord ++ tailWord_3117).sum := by decide
  have hdescent : baseEnd_3117 < baseStart_3117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138 : List Nat := [3, 6]
def baseStart_3138 : Nat := 118140960795 + 3138 * 2 ^ 59
def prefixEnd_3138 : Nat := 4983230072969 + 3 ^ 40 * 3138 * 2
def baseEnd_3138 : Nat := 1341237452801212181743

theorem tailTrace_3138 : CollatzResearch.WordTrace tailWord_3138 prefixEnd_3138 1341237452801212181743 := by
  unfold tailWord_3138
  simp only [CollatzResearch.WordTrace]
  refine ⟨28613065659759193210517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76301508426024515228045 28613065659759193210517)
  ·
    refine ⟨1341237452801212181743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28613065659759193210517 1341237452801212181743)
    ·
      rfl

theorem cell_3138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_3138 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3138 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3138 prefixEnd_3138 := by
    exact prefixLift 3138
  have htrace : WordTrace (prefixWord ++ tailWord_3138) baseStart_3138 baseEnd_3138 := by
    simpa [prefixWord, tailWord_3138, baseEnd_3138] using wordTrace_append hprefix tailTrace_3138
  have hstable : (prefixWord ++ tailWord_3138).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138).length < 2 ^ (prefixWord ++ tailWord_3138).sum := by decide
  have hdescent : baseEnd_3138 < baseStart_3138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3140 : List Nat := [2, 3, 6]
def baseStart_3140 : Nat := 118140960795 + 3140 * 2 ^ 59
def prefixEnd_3140 : Nat := 4983230072969 + 3 ^ 40 * 3140 * 2
def baseEnd_3140 : Nat := 1006569216490351591537

theorem tailTrace_3140 : CollatzResearch.WordTrace tailWord_3140 prefixEnd_3140 1006569216490351591537 := by
  unfold tailWord_3140
  simp only [CollatzResearch.WordTrace]
  refine ⟨57262604315895557207437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76350139087860742943249 57262604315895557207437)
  ·
    refine ⟨21473476618460833952789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57262604315895557207437 21473476618460833952789)
    ·
      refine ⟨1006569216490351591537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21473476618460833952789 1006569216490351591537)
      ·
        rfl

theorem cell_3140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_3140 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3140 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3140 prefixEnd_3140 := by
    exact prefixLift 3140
  have htrace : WordTrace (prefixWord ++ tailWord_3140) baseStart_3140 baseEnd_3140 := by
    simpa [prefixWord, tailWord_3140, baseEnd_3140] using wordTrace_append hprefix tailTrace_3140
  have hstable : (prefixWord ++ tailWord_3140).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3140).length < 2 ^ (prefixWord ++ tailWord_3140).sum := by decide
  have hdescent : baseEnd_3140 < baseStart_3140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174 : List Nat := [7]
def baseStart_3174 : Nat := 118140960795 + 3174 * 2 ^ 59
def prefixEnd_3174 : Nat := 4983230072969 + 3 ^ 40 * 3174 * 2
def baseEnd_3174 : Nat := 1808832664197108143009

theorem tailTrace_3174 : CollatzResearch.WordTrace tailWord_3174 prefixEnd_3174 1808832664197108143009 := by
  unfold tailWord_3174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1808832664197108143009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 77176860339076614101717 1808832664197108143009)
  ·
    rfl

theorem cell_3174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3174 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3174 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3174 prefixEnd_3174 := by
    exact prefixLift 3174
  have htrace : WordTrace (prefixWord ++ tailWord_3174) baseStart_3174 baseEnd_3174 := by
    simpa [prefixWord, tailWord_3174, baseEnd_3174] using wordTrace_append hprefix tailTrace_3174
  have hstable : (prefixWord ++ tailWord_3174).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174).length < 2 ^ (prefixWord ++ tailWord_3174).sum := by decide
  have hdescent : baseEnd_3174 < baseStart_3174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188 : List Nat := [2, 7]
def baseStart_3188 : Nat := 118140960795 + 3188 * 2 ^ 59
def prefixEnd_3188 : Nat := 4983230072969 + 3 ^ 40 * 3188 * 2
def baseEnd_3188 : Nat := 1362608349115960689401

theorem tailTrace_3188 : CollatzResearch.WordTrace tailWord_3188 prefixEnd_3188 1362608349115960689401 := by
  unfold tailWord_3188
  simp only [CollatzResearch.WordTrace]
  refine ⟨58137956228947656081109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77517274971930208108145 58137956228947656081109)
  ·
    refine ⟨1362608349115960689401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 58137956228947656081109 1362608349115960689401)
    ·
      rfl

theorem cell_3188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_3188 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3188 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3188 prefixEnd_3188 := by
    exact prefixLift 3188
  have htrace : WordTrace (prefixWord ++ tailWord_3188) baseStart_3188 baseEnd_3188 := by
    simpa [prefixWord, tailWord_3188, baseEnd_3188] using wordTrace_append hprefix tailTrace_3188
  have hstable : (prefixWord ++ tailWord_3188).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188).length < 2 ^ (prefixWord ++ tailWord_3188).sum := by decide
  have hdescent : baseEnd_3188 < baseStart_3188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202 : List Nat := [3, 4, 4]
def baseStart_3202 : Nat := 118140960795 + 3202 * 2 ^ 59
def prefixEnd_3202 : Nat := 4983230072969 + 3 ^ 40 * 3202 * 2
def baseEnd_3202 : Nat := 1026444150063067703659

theorem tailTrace_3202 : CollatzResearch.WordTrace tailWord_3202 prefixEnd_3202 1026444150063067703659 := by
  unfold tailWord_3202
  simp only [CollatzResearch.WordTrace]
  refine ⟨29196633601793925792965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77857689604783802114573 29196633601793925792965)
  ·
    refine ⟨5474368800336361086181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29196633601793925792965 5474368800336361086181)
    ·
      refine ⟨1026444150063067703659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5474368800336361086181 1026444150063067703659)
      ·
        rfl

theorem cell_3202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_3202 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3202 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3202 prefixEnd_3202 := by
    exact prefixLift 3202
  have htrace : WordTrace (prefixWord ++ tailWord_3202) baseStart_3202 baseEnd_3202 := by
    simpa [prefixWord, tailWord_3202, baseEnd_3202] using wordTrace_append hprefix tailTrace_3202
  have hstable : (prefixWord ++ tailWord_3202).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202).length < 2 ^ (prefixWord ++ tailWord_3202).sum := by decide
  have hdescent : baseEnd_3202 < baseStart_3202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206 : List Nat := [6, 4]
def baseStart_3206 : Nat := 118140960795 + 3206 * 2 ^ 59
def prefixEnd_3206 : Nat := 4983230072969 + 3 ^ 40 * 3206 * 2
def baseEnd_3206 : Nat := 685150935894635076079

theorem tailTrace_3206 : CollatzResearch.WordTrace tailWord_3206 prefixEnd_3206 685150935894635076079 := by
  unfold tailWord_3206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3654138324771387072421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77954950928456257544981 3654138324771387072421)
  ·
    refine ⟨685150935894635076079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3654138324771387072421 685150935894635076079)
    ·
      rfl

theorem cell_3206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_3206 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3206 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3206 prefixEnd_3206 := by
    exact prefixLift 3206
  have htrace : WordTrace (prefixWord ++ tailWord_3206) baseStart_3206 baseEnd_3206 := by
    simpa [prefixWord, tailWord_3206, baseEnd_3206] using wordTrace_append hprefix tailTrace_3206
  have hstable : (prefixWord ++ tailWord_3206).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206).length < 2 ^ (prefixWord ++ tailWord_3206).sum := by decide
  have hdescent : baseEnd_3206 < baseStart_3206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213 : List Nat := [1, 9]
def baseStart_3213 : Nat := 118140960795 + 3213 * 2 ^ 59
def prefixEnd_3213 : Nat := 4983230072969 + 3 ^ 40 * 3213 * 2
def baseEnd_3213 : Nat := 686646898636667471615

theorem tailTrace_3213 : CollatzResearch.WordTrace tailWord_3213 prefixEnd_3213 686646898636667471615 := by
  unfold tailWord_3213
  simp only [CollatzResearch.WordTrace]
  refine ⟨117187737367324581822293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78125158244883054548195 117187737367324581822293)
  ·
    refine ⟨686646898636667471615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 9 117187737367324581822293 686646898636667471615)
    ·
      rfl

theorem cell_3213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_3213 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3213 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3213 prefixEnd_3213 := by
    exact prefixLift 3213
  have htrace : WordTrace (prefixWord ++ tailWord_3213) baseStart_3213 baseEnd_3213 := by
    simpa [prefixWord, tailWord_3213, baseEnd_3213] using wordTrace_append hprefix tailTrace_3213
  have hstable : (prefixWord ++ tailWord_3213).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213).length < 2 ^ (prefixWord ++ tailWord_3213).sum := by decide
  have hdescent : baseEnd_3213 < baseStart_3213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222 : List Nat := [5, 3, 2, 2]
def baseStart_3222 : Nat := 118140960795 + 3222 * 2 ^ 59
def prefixEnd_3222 : Nat := 4983230072969 + 3 ^ 40 * 3222 * 2
def baseEnd_3222 : Nat := 1549283128436238383935

theorem tailTrace_3222 : CollatzResearch.WordTrace tailWord_3222 prefixEnd_3222 1549283128436238383935 := by
  unfold tailWord_3222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7344749645919944931245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78343996223146079266613 7344749645919944931245)
  ·
    refine ⟨2754281117219979349217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7344749645919944931245 2754281117219979349217)
    ·
      refine ⟨2065710837914984511913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2754281117219979349217 2065710837914984511913)
      ·
        refine ⟨1549283128436238383935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2065710837914984511913 1549283128436238383935)
        ·
          rfl

theorem cell_3222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_3222 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3222 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3222 prefixEnd_3222 := by
    exact prefixLift 3222
  have htrace : WordTrace (prefixWord ++ tailWord_3222) baseStart_3222 baseEnd_3222 := by
    simpa [prefixWord, tailWord_3222, baseEnd_3222] using wordTrace_append hprefix tailTrace_3222
  have hstable : (prefixWord ++ tailWord_3222).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222).length < 2 ^ (prefixWord ++ tailWord_3222).sum := by decide
  have hdescent : baseEnd_3222 < baseStart_3222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238 : List Nat := [9]
def baseStart_3238 : Nat := 118140960795 + 3238 * 2 ^ 59
def prefixEnd_3238 : Nat := 4983230072969 + 3 ^ 40 * 3238 * 2
def baseEnd_3238 : Nat := 461326415143569732353

theorem tailTrace_3238 : CollatzResearch.WordTrace tailWord_3238 prefixEnd_3238 461326415143569732353 := by
  unfold tailWord_3238
  simp only [CollatzResearch.WordTrace]
  refine ⟨461326415143569732353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 9 78733041517835900988245 461326415143569732353)
  ·
    rfl

theorem cell_3238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_3238 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3238 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3238 prefixEnd_3238 := by
    exact prefixLift 3238
  have htrace : WordTrace (prefixWord ++ tailWord_3238) baseStart_3238 baseEnd_3238 := by
    simpa [prefixWord, tailWord_3238, baseEnd_3238] using wordTrace_append hprefix tailTrace_3238
  have hstable : (prefixWord ++ tailWord_3238).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238).length < 2 ^ (prefixWord ++ tailWord_3238).sum := by decide
  have hdescent : baseEnd_3238 < baseStart_3238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276 : List Nat := [2, 2, 1, 7]
def baseStart_3276 : Nat := 118140960795 + 3276 * 2 ^ 59
def prefixEnd_3276 : Nat := 4983230072969 + 3 ^ 40 * 3276 * 2
def baseEnd_3276 : Nat := 1575248767458657820739

theorem tailTrace_3276 : CollatzResearch.WordTrace tailWord_3276 prefixEnd_3276 1575248767458657820739 := by
  unfold tailWord_3276
  simp only [CollatzResearch.WordTrace]
  refine ⟨59742768069543170682841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79657024092724227577121 59742768069543170682841)
  ·
    refine ⟨44807076052157378012131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59742768069543170682841 44807076052157378012131)
    ·
      refine ⟨67210614078236067018197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44807076052157378012131 67210614078236067018197)
      ·
        refine ⟨1575248767458657820739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 67210614078236067018197 1575248767458657820739)
        ·
          rfl

theorem cell_3276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_3276 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3276 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3276 prefixEnd_3276 := by
    exact prefixLift 3276
  have htrace : WordTrace (prefixWord ++ tailWord_3276) baseStart_3276 baseEnd_3276 := by
    simpa [prefixWord, tailWord_3276, baseEnd_3276] using wordTrace_append hprefix tailTrace_3276
  have hstable : (prefixWord ++ tailWord_3276).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276).length < 2 ^ (prefixWord ++ tailWord_3276).sum := by decide
  have hdescent : baseEnd_3276 < baseStart_3276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294 : List Nat := [4, 7]
def baseStart_3294 : Nat := 118140960795 + 3294 * 2 ^ 59
def prefixEnd_3294 : Nat := 4983230072969 + 3 ^ 40 * 3294 * 2
def baseEnd_3294 : Nat := 351978662325806881409

theorem tailTrace_3294 : CollatzResearch.WordTrace tailWord_3294 prefixEnd_3294 351978662325806881409 := by
  unfold tailWord_3294
  simp only [CollatzResearch.WordTrace]
  refine ⟨15017756259234426940117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80094700049250277013957 15017756259234426940117)
  ·
    refine ⟨351978662325806881409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 15017756259234426940117 351978662325806881409)
    ·
      rfl

theorem cell_3294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_3294 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3294 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3294 prefixEnd_3294 := by
    exact prefixLift 3294
  have htrace : WordTrace (prefixWord ++ tailWord_3294) baseStart_3294 baseEnd_3294 := by
    simpa [prefixWord, tailWord_3294, baseEnd_3294] using wordTrace_append hprefix tailTrace_3294
  have hstable : (prefixWord ++ tailWord_3294).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294).length < 2 ^ (prefixWord ++ tailWord_3294).sum := by decide
  have hdescent : baseEnd_3294 < baseStart_3294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302 : List Nat := [7]
def baseStart_3302 : Nat := 118140960795 + 3302 * 2 ^ 59
def prefixEnd_3302 : Nat := 4983230072969 + 3 ^ 40 * 3302 * 2
def baseEnd_3302 : Nat := 1881778656951449715815

theorem tailTrace_3302 : CollatzResearch.WordTrace tailWord_3302 prefixEnd_3302 1881778656951449715815 := by
  unfold tailWord_3302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1881778656951449715815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 80289222696595187874773 1881778656951449715815)
  ·
    rfl

theorem cell_3302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3302 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3302 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3302 prefixEnd_3302 := by
    exact prefixLift 3302
  have htrace : WordTrace (prefixWord ++ tailWord_3302) baseStart_3302 baseEnd_3302 := by
    simpa [prefixWord, tailWord_3302, baseEnd_3302] using wordTrace_append hprefix tailTrace_3302
  have hstable : (prefixWord ++ tailWord_3302).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302).length < 2 ^ (prefixWord ++ tailWord_3302).sum := by decide
  have hdescent : baseEnd_3302 < baseStart_3302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317 : List Nat := [1, 3, 7]
def baseStart_3317 : Nat := 118140960795 + 3317 * 2 ^ 59
def prefixEnd_3317 : Nat := 4983230072969 + 3 ^ 40 * 3317 * 2
def baseEnd_3317 : Nat := 1063308946206008879369

theorem tailTrace_3317 : CollatzResearch.WordTrace tailWord_3317 prefixEnd_3317 1063308946206008879369 := by
  unfold tailWord_3317
  simp only [CollatzResearch.WordTrace]
  refine ⟨120980928990550343608205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80653952660366895738803 120980928990550343608205)
  ·
    refine ⟨45367848371456378853077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120980928990550343608205 45367848371456378853077)
    ·
      refine ⟨1063308946206008879369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 45367848371456378853077 1063308946206008879369)
      ·
        rfl

theorem cell_3317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_3317 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3317 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3317 prefixEnd_3317 := by
    exact prefixLift 3317
  have htrace : WordTrace (prefixWord ++ tailWord_3317) baseStart_3317 baseEnd_3317 := by
    simpa [prefixWord, tailWord_3317, baseEnd_3317] using wordTrace_append hprefix tailTrace_3317
  have hstable : (prefixWord ++ tailWord_3317).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317).length < 2 ^ (prefixWord ++ tailWord_3317).sum := by decide
  have hdescent : baseEnd_3317 < baseStart_3317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334 : List Nat := [6, 2, 4]
def baseStart_3334 : Nat := 118140960795 + 3334 * 2 ^ 59
def prefixEnd_3334 : Nat := 4983230072969 + 3 ^ 40 * 3334 * 2
def baseEnd_3334 : Nat := 534379262383134874411

theorem tailTrace_3334 : CollatzResearch.WordTrace tailWord_3334 prefixEnd_3334 534379262383134874411 := by
  unfold tailWord_3334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3800030310280070218033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81067313285974831318037 3800030310280070218033)
  ·
    refine ⟨2850022732710052663525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3800030310280070218033 2850022732710052663525)
    ·
      refine ⟨534379262383134874411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2850022732710052663525 534379262383134874411)
      ·
        rfl

theorem cell_3334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_3334 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3334 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3334 prefixEnd_3334 := by
    exact prefixLift 3334
  have htrace : WordTrace (prefixWord ++ tailWord_3334) baseStart_3334 baseEnd_3334 := by
    simpa [prefixWord, tailWord_3334, baseEnd_3334] using wordTrace_append hprefix tailTrace_3334
  have hstable : (prefixWord ++ tailWord_3334).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334).length < 2 ^ (prefixWord ++ tailWord_3334).sum := by decide
  have hdescent : baseEnd_3334 < baseStart_3334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335 : List Nat := [1, 1, 4, 6]
def baseStart_3335 : Nat := 118140960795 + 3335 * 2 ^ 59
def prefixEnd_3335 : Nat := 4983230072969 + 3 ^ 40 * 3335 * 2
def baseEnd_3335 : Nat := 1603618632316486464655

theorem tailTrace_3335 : CollatzResearch.WordTrace tailWord_3335 prefixEnd_3335 1603618632316486464655 := by
  unfold tailWord_3335
  simp only [CollatzResearch.WordTrace]
  refine ⟨121637442925339417763459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81091628616892945175639 121637442925339417763459)
  ·
    refine ⟨182456164388009126645189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121637442925339417763459 182456164388009126645189)
    ·
      refine ⟨34210530822751711245973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182456164388009126645189 34210530822751711245973)
      ·
        refine ⟨1603618632316486464655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34210530822751711245973 1603618632316486464655)
        ·
          rfl

theorem cell_3335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_3335 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3335 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3335 prefixEnd_3335 := by
    exact prefixLift 3335
  have htrace : WordTrace (prefixWord ++ tailWord_3335) baseStart_3335 baseEnd_3335 := by
    simpa [prefixWord, tailWord_3335, baseEnd_3335] using wordTrace_append hprefix tailTrace_3335
  have hstable : (prefixWord ++ tailWord_3335).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335).length < 2 ^ (prefixWord ++ tailWord_3335).sum := by decide
  have hdescent : baseEnd_3335 < baseStart_3335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3341 : List Nat := [1, 7, 4]
def baseStart_3341 : Nat := 118140960795 + 3341 * 2 ^ 59
def prefixEnd_3341 : Nat := 4983230072969 + 3 ^ 40 * 3341 * 2
def baseEnd_3341 : Nat := 535501234439659171063

theorem tailTrace_3341 : CollatzResearch.WordTrace tailWord_3341 prefixEnd_3341 535501234439659171063 := by
  unfold tailWord_3341
  simp only [CollatzResearch.WordTrace]
  refine ⟨121856280903602442481877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81237520602401628321251 121856280903602442481877)
  ·
    refine ⟨2856006583678182245669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 121856280903602442481877 2856006583678182245669)
    ·
      refine ⟨535501234439659171063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2856006583678182245669 535501234439659171063)
      ·
        rfl

theorem cell_3341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_3341 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3341 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3341 prefixEnd_3341 := by
    exact prefixLift 3341
  have htrace : WordTrace (prefixWord ++ tailWord_3341) baseStart_3341 baseEnd_3341 := by
    simpa [prefixWord, tailWord_3341, baseEnd_3341] using wordTrace_append hprefix tailTrace_3341
  have hstable : (prefixWord ++ tailWord_3341).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3341).length < 2 ^ (prefixWord ++ tailWord_3341).sum := by decide
  have hdescent : baseEnd_3341 < baseStart_3341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348 : List Nat := [2, 4, 6]
def baseStart_3348 : Nat := 118140960795 + 3348 * 2 ^ 59
def prefixEnd_3348 : Nat := 4983230072969 + 3 ^ 40 * 3348 * 2
def baseEnd_3348 : Nat := 536623206496183467715

theorem tailTrace_3348 : CollatzResearch.WordTrace tailWord_3348 prefixEnd_3348 536623206496183467715 := by
  unfold tailWord_3348
  simp only [CollatzResearch.WordTrace]
  refine ⟨61055795939121318993349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81407727918828425324465 61055795939121318993349)
  ·
    refine ⟨11447961738585247311253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61055795939121318993349 11447961738585247311253)
    ·
      refine ⟨536623206496183467715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11447961738585247311253 536623206496183467715)
      ·
        rfl

theorem cell_3348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_3348 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3348 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3348 prefixEnd_3348 := by
    exact prefixLift 3348
  have htrace : WordTrace (prefixWord ++ tailWord_3348) baseStart_3348 baseEnd_3348 := by
    simpa [prefixWord, tailWord_3348, baseEnd_3348] using wordTrace_append hprefix tailTrace_3348
  have hstable : (prefixWord ++ tailWord_3348).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348).length < 2 ^ (prefixWord ++ tailWord_3348).sum := by decide
  have hdescent : baseEnd_3348 < baseStart_3348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350 : List Nat := [5, 4]
def baseStart_3350 : Nat := 118140960795 + 3350 * 2 ^ 59
def prefixEnd_3350 : Nat := 4983230072969 + 3 ^ 40 * 3350 * 2
def baseEnd_3350 : Nat := 1431850053175745854213

theorem tailTrace_3350 : CollatzResearch.WordTrace tailWord_3350 prefixEnd_3350 1431850053175745854213 := by
  unfold tailWord_3350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7636533616937311222469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81456358580664653039669 7636533616937311222469)
  ·
    refine ⟨1431850053175745854213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7636533616937311222469 1431850053175745854213)
    ·
      rfl

theorem cell_3350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_3350 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3350 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3350 prefixEnd_3350 := by
    exact prefixLift 3350
  have htrace : WordTrace (prefixWord ++ tailWord_3350) baseStart_3350 baseEnd_3350 := by
    simpa [prefixWord, tailWord_3350, baseEnd_3350] using wordTrace_append hprefix tailTrace_3350
  have hstable : (prefixWord ++ tailWord_3350).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350).length < 2 ^ (prefixWord ++ tailWord_3350).sum := by decide
  have hdescent : baseEnd_3350 < baseStart_3350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366 : List Nat := [8]
def baseStart_3366 : Nat := 118140960795 + 3366 * 2 ^ 59
def prefixEnd_3366 : Nat := 4983230072969 + 3 ^ 40 * 3366 * 2
def baseEnd_3366 : Nat := 959125826664310251109

theorem tailTrace_3366 : CollatzResearch.WordTrace tailWord_3366 prefixEnd_3366 959125826664310251109 := by
  unfold tailWord_3366
  simp only [CollatzResearch.WordTrace]
  refine ⟨959125826664310251109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 81845403875354474761301 959125826664310251109)
  ·
    rfl

theorem cell_3366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_3366 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3366 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3366 prefixEnd_3366 := by
    exact prefixLift 3366
  have htrace : WordTrace (prefixWord ++ tailWord_3366) baseStart_3366 baseEnd_3366 := by
    simpa [prefixWord, tailWord_3366, baseEnd_3366] using wordTrace_append hprefix tailTrace_3366
  have hstable : (prefixWord ++ tailWord_3366).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366).length < 2 ^ (prefixWord ++ tailWord_3366).sum := by decide
  have hdescent : baseEnd_3366 < baseStart_3366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367 : List Nat := [1, 1, 8, 2]
def baseStart_3367 : Nat := 118140960795 + 3367 * 2 ^ 59
def prefixEnd_3367 : Nat := 4983230072969 + 3 ^ 40 * 3367 * 2
def baseEnd_3367 : Nat := 1619005677663105390169

theorem tailTrace_3367 : CollatzResearch.WordTrace tailWord_3367 prefixEnd_3367 1619005677663105390169 := by
  unfold tailWord_3367
  simp only [CollatzResearch.WordTrace]
  refine ⟨122804578809408882928355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81869719206272588618903 122804578809408882928355)
  ·
    refine ⟨184206868214113324392533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122804578809408882928355 184206868214113324392533)
    ·
      refine ⟨2158674236884140520225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 184206868214113324392533 2158674236884140520225)
      ·
        refine ⟨1619005677663105390169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2158674236884140520225 1619005677663105390169)
        ·
          rfl

theorem cell_3367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_3367 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3367 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3367 prefixEnd_3367 := by
    exact prefixLift 3367
  have htrace : WordTrace (prefixWord ++ tailWord_3367) baseStart_3367 baseEnd_3367 := by
    simpa [prefixWord, tailWord_3367, baseEnd_3367] using wordTrace_append hprefix tailTrace_3367
  have hstable : (prefixWord ++ tailWord_3367).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367).length < 2 ^ (prefixWord ++ tailWord_3367).sum := by decide
  have hdescent : baseEnd_3367 < baseStart_3367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374 : List Nat := [4, 1, 3, 4]
def baseStart_3374 : Nat := 118140960795 + 3374 * 2 ^ 59
def prefixEnd_3374 : Nat := 4983230072969 + 3 ^ 40 * 3374 * 2
def baseEnd_3374 : Nat := 1622371593832678280125

theorem tailTrace_3374 : CollatzResearch.WordTrace tailWord_3374 prefixEnd_3374 1622371593832678280125 := by
  unfold tailWord_3374
  simp only [CollatzResearch.WordTrace]
  refine ⟨15382486223006134804147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82039926522699385622117 15382486223006134804147)
  ·
    refine ⟨23073729334509202206221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15382486223006134804147 23073729334509202206221)
    ·
      refine ⟨8652648500440950827333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23073729334509202206221 8652648500440950827333)
      ·
        refine ⟨1622371593832678280125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8652648500440950827333 1622371593832678280125)
        ·
          rfl

theorem cell_3374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_3374 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3374 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3374 prefixEnd_3374 := by
    exact prefixLift 3374
  have htrace : WordTrace (prefixWord ++ tailWord_3374) baseStart_3374 baseEnd_3374 := by
    simpa [prefixWord, tailWord_3374, baseEnd_3374] using wordTrace_append hprefix tailTrace_3374
  have hstable : (prefixWord ++ tailWord_3374).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374).length < 2 ^ (prefixWord ++ tailWord_3374).sum := by decide
  have hdescent : baseEnd_3374 < baseStart_3374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394 : List Nat := [3, 9]
def baseStart_3394 : Nat := 118140960795 + 3394 * 2 ^ 59
def prefixEnd_3394 : Nat := 4983230072969 + 3 ^ 40 * 3394 * 2
def baseEnd_3394 : Nat := 181332055241590567619

theorem tailTrace_3394 : CollatzResearch.WordTrace tailWord_3394 prefixEnd_3394 181332055241590567619 := by
  unfold tailWord_3394
  simp only [CollatzResearch.WordTrace]
  refine ⟨30947337427898123540309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82526233141061662774157 30947337427898123540309)
  ·
    refine ⟨181332055241590567619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 9 30947337427898123540309 181332055241590567619)
    ·
      rfl

theorem cell_3394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_3394 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3394 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3394 prefixEnd_3394 := by
    exact prefixLift 3394
  have htrace : WordTrace (prefixWord ++ tailWord_3394) baseStart_3394 baseEnd_3394 := by
    simpa [prefixWord, tailWord_3394, baseEnd_3394] using wordTrace_append hprefix tailTrace_3394
  have hstable : (prefixWord ++ tailWord_3394).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394).length < 2 ^ (prefixWord ++ tailWord_3394).sum := by decide
  have hdescent : baseEnd_3394 < baseStart_3394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420 : List Nat := [2, 2, 4, 4]
def baseStart_3420 : Nat := 118140960795 + 3420 * 2 ^ 59
def prefixEnd_3420 : Nat := 4983230072969 + 3 ^ 40 * 3420 * 2
def baseEnd_3420 : Nat := 1644490471518442985551

theorem tailTrace_3420 : CollatzResearch.WordTrace tailWord_3420 prefixEnd_3420 1644490471518442985551 := by
  unfold tailWord_3420
  simp only [CollatzResearch.WordTrace]
  refine ⟨62368823808699467303857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83158431744932623071809 62368823808699467303857)
  ·
    refine ⟨46776617856524600477893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62368823808699467303857 46776617856524600477893)
    ·
      refine ⟨8770615848098362589605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46776617856524600477893 8770615848098362589605)
      ·
        refine ⟨1644490471518442985551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8770615848098362589605 1644490471518442985551)
        ·
          rfl

theorem cell_3420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_3420 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3420 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3420 prefixEnd_3420 := by
    exact prefixLift 3420
  have htrace : WordTrace (prefixWord ++ tailWord_3420) baseStart_3420 baseEnd_3420 := by
    simpa [prefixWord, tailWord_3420, baseEnd_3420] using wordTrace_append hprefix tailTrace_3420
  have hstable : (prefixWord ++ tailWord_3420).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420).length < 2 ^ (prefixWord ++ tailWord_3420).sum := by decide
  have hdescent : baseEnd_3420 < baseStart_3420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430 : List Nat := [7]
def baseStart_3430 : Nat := 118140960795 + 3430 * 2 ^ 59
def prefixEnd_3430 : Nat := 4983230072969 + 3 ^ 40 * 3430 * 2
def baseEnd_3430 : Nat := 1954724649705791288621

theorem tailTrace_3430 : CollatzResearch.WordTrace tailWord_3430 prefixEnd_3430 1954724649705791288621 := by
  unfold tailWord_3430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1954724649705791288621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 83401585054113761647829 1954724649705791288621)
  ·
    rfl

theorem cell_3430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3430 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3430 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3430 prefixEnd_3430 := by
    exact prefixLift 3430
  have htrace : WordTrace (prefixWord ++ tailWord_3430) baseStart_3430 baseEnd_3430 := by
    simpa [prefixWord, tailWord_3430, baseEnd_3430] using wordTrace_append hprefix tailTrace_3430
  have hstable : (prefixWord ++ tailWord_3430).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430).length < 2 ^ (prefixWord ++ tailWord_3430).sum := by decide
  have hdescent : baseEnd_3430 < baseStart_3430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444 : List Nat := [2, 8]
def baseStart_3444 : Nat := 118140960795 + 3444 * 2 ^ 59
def prefixEnd_3444 : Nat := 4983230072969 + 3 ^ 40 * 3444 * 2
def baseEnd_3444 : Nat := 736013669123736524305

theorem tailTrace_3444 : CollatzResearch.WordTrace tailWord_3444 prefixEnd_3444 736013669123736524305 := by
  unfold tailWord_3444
  simp only [CollatzResearch.WordTrace]
  refine ⟨62806499765225516740693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83741999686967355654257 62806499765225516740693)
  ·
    refine ⟨736013669123736524305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 62806499765225516740693 736013669123736524305)
    ·
      rfl

theorem cell_3444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_3444 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3444 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3444 prefixEnd_3444 := by
    exact prefixLift 3444
  have htrace : WordTrace (prefixWord ++ tailWord_3444) baseStart_3444 baseEnd_3444 := by
    simpa [prefixWord, tailWord_3444, baseEnd_3444] using wordTrace_append hprefix tailTrace_3444
  have hstable : (prefixWord ++ tailWord_3444).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444).length < 2 ^ (prefixWord ++ tailWord_3444).sum := by decide
  have hdescent : baseEnd_3444 < baseStart_3444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446 : List Nat := [5, 1, 1, 5]
def baseStart_3446 : Nat := 118140960795 + 3446 * 2 ^ 59
def prefixEnd_3446 : Nat := 4983230072969 + 3 ^ 40 * 3446 * 2
def baseEnd_3446 : Nat := 1656992445862570862531

theorem tailTrace_3446 : CollatzResearch.WordTrace tailWord_3446 prefixEnd_3446 1656992445862570862531 := by
  unfold tailWord_3446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7855371595200335940887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83790630348803583369461 7855371595200335940887)
  ·
    refine ⟨11783057392800503911331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7855371595200335940887 11783057392800503911331)
    ·
      refine ⟨17674586089200755866997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11783057392800503911331 17674586089200755866997)
      ·
        refine ⟨1656992445862570862531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17674586089200755866997 1656992445862570862531)
        ·
          rfl

theorem cell_3446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_3446 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3446 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3446 prefixEnd_3446 := by
    exact prefixLift 3446
  have htrace : WordTrace (prefixWord ++ tailWord_3446) baseStart_3446 baseEnd_3446 := by
    simpa [prefixWord, tailWord_3446, baseEnd_3446] using wordTrace_append hprefix tailTrace_3446
  have hstable : (prefixWord ++ tailWord_3446).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446).length < 2 ^ (prefixWord ++ tailWord_3446).sum := by decide
  have hdescent : baseEnd_3446 < baseStart_3446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462 : List Nat := [6, 3]
def baseStart_3462 : Nat := 118140960795 + 3462 * 2 ^ 59
def prefixEnd_3462 : Nat := 4983230072969 + 3 ^ 40 * 3462 * 2
def baseEnd_3462 : Nat := 1479720860920782511367

theorem tailTrace_3462 : CollatzResearch.WordTrace tailWord_3462 prefixEnd_3462 1479720860920782511367 := by
  unfold tailWord_3462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3945922295788753363645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84179675643493405091093 3945922295788753363645)
  ·
    refine ⟨1479720860920782511367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3945922295788753363645 1479720860920782511367)
    ·
      rfl

theorem cell_3462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_3462 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3462 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3462 prefixEnd_3462 := by
    exact prefixLift 3462
  have htrace : WordTrace (prefixWord ++ tailWord_3462) baseStart_3462 baseEnd_3462 := by
    simpa [prefixWord, tailWord_3462, baseEnd_3462] using wordTrace_append hprefix tailTrace_3462
  have hstable : (prefixWord ++ tailWord_3462).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462).length < 2 ^ (prefixWord ++ tailWord_3462).sum := by decide
  have hdescent : baseEnd_3462 < baseStart_3462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466 : List Nat := [3, 1, 2, 6]
def baseStart_3466 : Nat := 118140960795 + 3466 * 2 ^ 59
def prefixEnd_3466 : Nat := 4983230072969 + 3 ^ 40 * 3466 * 2
def baseEnd_3466 : Nat := 1666609349204207690977

theorem tailTrace_3466 : CollatzResearch.WordTrace tailWord_3466 prefixEnd_3466 1666609349204207690977 := by
  unfold tailWord_3466
  simp only [CollatzResearch.WordTrace]
  refine ⟨31603851362687197695563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84276936967165860521501 31603851362687197695563)
  ·
    refine ⟨47405777044030796543345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31603851362687197695563 47405777044030796543345)
    ·
      refine ⟨35554332783023097407509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47405777044030796543345 35554332783023097407509)
      ·
        refine ⟨1666609349204207690977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35554332783023097407509 1666609349204207690977)
        ·
          rfl

theorem cell_3466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_3466 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3466 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3466 prefixEnd_3466 := by
    exact prefixLift 3466
  have htrace : WordTrace (prefixWord ++ tailWord_3466) baseStart_3466 baseEnd_3466 := by
    simpa [prefixWord, tailWord_3466, baseEnd_3466] using wordTrace_append hprefix tailTrace_3466
  have hstable : (prefixWord ++ tailWord_3466).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466).length < 2 ^ (prefixWord ++ tailWord_3466).sum := by decide
  have hdescent : baseEnd_3466 < baseStart_3466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469 : List Nat := [1, 8]
def baseStart_3469 : Nat := 118140960795 + 3469 * 2 ^ 59
def prefixEnd_3469 : Nat := 4983230072969 + 3 ^ 40 * 3469 * 2
def baseEnd_3469 : Nat := 1482712786404847302439

theorem tailTrace_3469 : CollatzResearch.WordTrace tailWord_3469 prefixEnd_3469 1482712786404847302439 := by
  unfold tailWord_3469
  simp only [CollatzResearch.WordTrace]
  refine ⟨126524824439880303141461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84349882959920202094307 126524824439880303141461)
  ·
    refine ⟨1482712786404847302439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 126524824439880303141461 1482712786404847302439)
    ·
      rfl

theorem cell_3469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_3469 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3469 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3469 prefixEnd_3469 := by
    exact prefixLift 3469
  have htrace : WordTrace (prefixWord ++ tailWord_3469) baseStart_3469 baseEnd_3469 := by
    simpa [prefixWord, tailWord_3469, baseEnd_3469] using wordTrace_append hprefix tailTrace_3469
  have hstable : (prefixWord ++ tailWord_3469).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469).length < 2 ^ (prefixWord ++ tailWord_3469).sum := by decide
  have hdescent : baseEnd_3469 < baseStart_3469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478 : List Nat := [5, 3, 1, 3]
def baseStart_3478 : Nat := 118140960795 + 3478 * 2 ^ 59
def prefixEnd_3478 : Nat := 4983230072969 + 3 ^ 40 * 3478 * 2
def baseEnd_3478 : Nat := 1672379491209189788045

theorem tailTrace_3478 : CollatzResearch.WordTrace tailWord_3478 prefixEnd_3478 1672379491209189788045 := by
  unfold tailWord_3478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7928317587954677513693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84568720938183226812725 7928317587954677513693)
  ·
    refine ⟨2973119095483004067635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7928317587954677513693 2973119095483004067635)
    ·
      refine ⟨4459678643224506101453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2973119095483004067635 4459678643224506101453)
      ·
        refine ⟨1672379491209189788045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4459678643224506101453 1672379491209189788045)
        ·
          rfl

theorem cell_3478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_3478 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3478 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3478 prefixEnd_3478 := by
    exact prefixLift 3478
  have htrace : WordTrace (prefixWord ++ tailWord_3478) baseStart_3478 baseEnd_3478 := by
    simpa [prefixWord, tailWord_3478, baseEnd_3478] using wordTrace_append hprefix tailTrace_3478
  have hstable : (prefixWord ++ tailWord_3478).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478).length < 2 ^ (prefixWord ++ tailWord_3478).sum := by decide
  have hdescent : baseEnd_3478 < baseStart_3478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494 : List Nat := [11]
def baseStart_3494 : Nat := 118140960795 + 3494 * 2 ^ 59
def prefixEnd_3494 : Nat := 4983230072969 + 3 ^ 40 * 3494 * 2
def baseEnd_3494 : Nat := 124449852880185129689

theorem tailTrace_3494 : CollatzResearch.WordTrace tailWord_3494 prefixEnd_3494 124449852880185129689 := by
  unfold tailWord_3494
  simp only [CollatzResearch.WordTrace]
  refine ⟨124449852880185129689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 11 84957766232873048534357 124449852880185129689)
  ·
    rfl

theorem cell_3494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_3494 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3494 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3494 prefixEnd_3494 := by
    exact prefixLift 3494
  have htrace : WordTrace (prefixWord ++ tailWord_3494) baseStart_3494 baseEnd_3494 := by
    simpa [prefixWord, tailWord_3494, baseEnd_3494] using wordTrace_append hprefix tailTrace_3494
  have hstable : (prefixWord ++ tailWord_3494).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494).length < 2 ^ (prefixWord ++ tailWord_3494).sum := by decide
  have hdescent : baseEnd_3494 < baseStart_3494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498 : List Nat := [3, 1, 6, 2]
def baseStart_3498 : Nat := 118140960795 + 3498 * 2 ^ 59
def prefixEnd_3498 : Nat := 4983230072969 + 3 ^ 40 * 3498 * 2
def baseEnd_3498 : Nat := 1681996394550826616491

theorem tailTrace_3498 : CollatzResearch.WordTrace tailWord_3498 prefixEnd_3498 1681996394550826616491 := by
  unfold tailWord_3498
  simp only [CollatzResearch.WordTrace]
  refine ⟨31895635333704563986787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85055027556545503964765 31895635333704563986787)
  ·
    refine ⟨47843453000556845980181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31895635333704563986787 47843453000556845980181)
    ·
      refine ⟨2242661859401102155321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47843453000556845980181 2242661859401102155321)
      ·
        refine ⟨1681996394550826616491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2242661859401102155321 1681996394550826616491)
        ·
          rfl

theorem cell_3498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_3498 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3498 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3498 prefixEnd_3498 := by
    exact prefixLift 3498
  have htrace : WordTrace (prefixWord ++ tailWord_3498) baseStart_3498 baseEnd_3498 := by
    simpa [prefixWord, tailWord_3498, baseEnd_3498] using wordTrace_append hprefix tailTrace_3498
  have hstable : (prefixWord ++ tailWord_3498).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498).length < 2 ^ (prefixWord ++ tailWord_3498).sum := by decide
  have hdescent : baseEnd_3498 < baseStart_3498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510 : List Nat := [5, 1, 5]
def baseStart_3510 : Nat := 118140960795 + 3510 * 2 ^ 59
def prefixEnd_3510 : Nat := 4983230072969 + 3 ^ 40 * 3510 * 2
def baseEnd_3510 : Nat := 1125177691037205809039

theorem tailTrace_3510 : CollatzResearch.WordTrace tailWord_3510 prefixEnd_3510 1125177691037205809039 := by
  unfold tailWord_3510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8001263580709019086499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85346811527562870255989 8001263580709019086499)
  ·
    refine ⟨12001895371063528629749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8001263580709019086499 12001895371063528629749)
    ·
      refine ⟨1125177691037205809039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12001895371063528629749 1125177691037205809039)
      ·
        rfl

theorem cell_3510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_3510 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3510 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3510 prefixEnd_3510 := by
    exact prefixLift 3510
  have htrace : WordTrace (prefixWord ++ tailWord_3510) baseStart_3510 baseEnd_3510 := by
    simpa [prefixWord, tailWord_3510, baseEnd_3510] using wordTrace_append hprefix tailTrace_3510
  have hstable : (prefixWord ++ tailWord_3510).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510).length < 2 ^ (prefixWord ++ tailWord_3510).sum := by decide
  have hdescent : baseEnd_3510 < baseStart_3510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3526 : List Nat := [6, 1, 4]
def baseStart_3526 : Nat := 118140960795 + 3526 * 2 ^ 59
def prefixEnd_3526 : Nat := 4983230072969 + 3 ^ 40 * 3526 * 2
def baseEnd_3526 : Nat := 1130306706152745450877

theorem tailTrace_3526 : CollatzResearch.WordTrace tailWord_3526 prefixEnd_3526 1130306706152745450877 := by
  unfold tailWord_3526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4018868288543094936451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85735856822252691977621 4018868288543094936451)
  ·
    refine ⟨6028302432814642404677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4018868288543094936451 6028302432814642404677)
    ·
      refine ⟨1130306706152745450877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6028302432814642404677 1130306706152745450877)
      ·
        rfl

theorem cell_3526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_3526 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3526 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3526 prefixEnd_3526 := by
    exact prefixLift 3526
  have htrace : WordTrace (prefixWord ++ tailWord_3526) baseStart_3526 baseEnd_3526 := by
    simpa [prefixWord, tailWord_3526, baseEnd_3526] using wordTrace_append hprefix tailTrace_3526
  have hstable : (prefixWord ++ tailWord_3526).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3526).length < 2 ^ (prefixWord ++ tailWord_3526).sum := by decide
  have hdescent : baseEnd_3526 < baseStart_3526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533 : List Nat := [1, 6, 4]
def baseStart_3533 : Nat := 118140960795 + 3533 * 2 ^ 59
def prefixEnd_3533 : Nat := 4983230072969 + 3 ^ 40 * 3533 * 2
def baseEnd_3533 : Nat := 1132550650265794044181

theorem tailTrace_3533 : CollatzResearch.WordTrace tailWord_3533 prefixEnd_3533 1132550650265794044181 := by
  unfold tailWord_3533
  simp only [CollatzResearch.WordTrace]
  refine ⟨128859096208019233471253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85906064138679488980835 128859096208019233471253)
  ·
    refine ⟨6040270134750901568965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128859096208019233471253 6040270134750901568965)
    ·
      refine ⟨1132550650265794044181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6040270134750901568965 1132550650265794044181)
      ·
        rfl

theorem cell_3533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_3533 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3533 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3533 prefixEnd_3533 := by
    exact prefixLift 3533
  have htrace : WordTrace (prefixWord ++ tailWord_3533) baseStart_3533 baseEnd_3533 := by
    simpa [prefixWord, tailWord_3533, baseEnd_3533] using wordTrace_append hprefix tailTrace_3533
  have hstable : (prefixWord ++ tailWord_3533).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533).length < 2 ^ (prefixWord ++ tailWord_3533).sum := by decide
  have hdescent : baseEnd_3533 < baseStart_3533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538 : List Nat := [3, 2, 2, 5]
def baseStart_3538 : Nat := 118140960795 + 3538 * 2 ^ 59
def prefixEnd_3538 : Nat := 4983230072969 + 3 ^ 40 * 3538 * 2
def baseEnd_3538 : Nat := 1701230201234100273383

theorem tailTrace_3538 : CollatzResearch.WordTrace tailWord_3538 prefixEnd_3538 1701230201234100273383 := by
  unfold tailWord_3538
  simp only [CollatzResearch.WordTrace]
  refine ⟨32260365297476271850817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86027640793270058268845 32260365297476271850817)
  ·
    refine ⟨24195273973107203888113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32260365297476271850817 24195273973107203888113)
    ·
      refine ⟨18146455479830402916085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24195273973107203888113 18146455479830402916085)
      ·
        refine ⟨1701230201234100273383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18146455479830402916085 1701230201234100273383)
        ·
          rfl

theorem cell_3538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_3538 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3538 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3538 prefixEnd_3538 := by
    exact prefixLift 3538
  have htrace : WordTrace (prefixWord ++ tailWord_3538) baseStart_3538 baseEnd_3538 := by
    simpa [prefixWord, tailWord_3538, baseEnd_3538] using wordTrace_append hprefix tailTrace_3538
  have hstable : (prefixWord ++ tailWord_3538).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538).length < 2 ^ (prefixWord ++ tailWord_3538).sum := by decide
  have hdescent : baseEnd_3538 < baseStart_3538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550 : List Nat := [4, 5]
def baseStart_3550 : Nat := 118140960795 + 3550 * 2 ^ 59
def prefixEnd_3550 : Nat := 4983230072969 + 3 ^ 40 * 3550 * 2
def baseEnd_3550 : Nat := 1517333638434739884845

theorem tailTrace_3550 : CollatzResearch.WordTrace tailWord_3550 prefixEnd_3550 1517333638434739884845 := by
  unfold tailWord_3550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16184892143303892105013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86319424764287424560069 16184892143303892105013)
  ·
    refine ⟨1517333638434739884845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16184892143303892105013 1517333638434739884845)
    ·
      rfl

theorem cell_3550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_3550 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3550 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3550 prefixEnd_3550 := by
    exact prefixLift 3550
  have htrace : WordTrace (prefixWord ++ tailWord_3550) baseStart_3550 baseEnd_3550 := by
    simpa [prefixWord, tailWord_3550, baseEnd_3550] using wordTrace_append hprefix tailTrace_3550
  have hstable : (prefixWord ++ tailWord_3550).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550).length < 2 ^ (prefixWord ++ tailWord_3550).sum := by decide
  have hdescent : baseEnd_3550 < baseStart_3550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3558 : List Nat := [7]
def baseStart_3558 : Nat := 118140960795 + 3558 * 2 ^ 59
def prefixEnd_3558 : Nat := 4983230072969 + 3 ^ 40 * 3558 * 2
def baseEnd_3558 : Nat := 2027670642460132861427

theorem tailTrace_3558 : CollatzResearch.WordTrace tailWord_3558 prefixEnd_3558 2027670642460132861427 := by
  unfold tailWord_3558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2027670642460132861427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 86513947411632335420885 2027670642460132861427)
  ·
    rfl

theorem cell_3558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3558 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3558 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3558 prefixEnd_3558 := by
    exact prefixLift 3558
  have htrace : WordTrace (prefixWord ++ tailWord_3558) baseStart_3558 baseEnd_3558 := by
    simpa [prefixWord, tailWord_3558, baseEnd_3558] using wordTrace_append hprefix tailTrace_3558
  have hstable : (prefixWord ++ tailWord_3558).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3558).length < 2 ^ (prefixWord ++ tailWord_3558).sum := by decide
  have hdescent : baseEnd_3558 < baseStart_3558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572 : List Nat := [2, 6, 3]
def baseStart_3572 : Nat := 118140960795 + 3572 * 2 ^ 59
def prefixEnd_3572 : Nat := 4983230072969 + 3 ^ 40 * 3572 * 2
def baseEnd_3572 : Nat := 1145052624609921921161

theorem tailTrace_3572 : CollatzResearch.WordTrace tailWord_3572 prefixEnd_3572 1145052624609921921161 := by
  unfold tailWord_3572
  simp only [CollatzResearch.WordTrace]
  refine ⟨65140771533364447070485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86854362044485929427313 65140771533364447070485)
  ·
    refine ⟨3053473665626458456429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65140771533364447070485 3053473665626458456429)
    ·
      refine ⟨1145052624609921921161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3053473665626458456429 1145052624609921921161)
      ·
        rfl

theorem cell_3572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_3572 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3572 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3572 prefixEnd_3572 := by
    exact prefixLift 3572
  have htrace : WordTrace (prefixWord ++ tailWord_3572) baseStart_3572 baseEnd_3572 := by
    simpa [prefixWord, tailWord_3572, baseEnd_3572] using wordTrace_append hprefix tailTrace_3572
  have hstable : (prefixWord ++ tailWord_3572).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572).length < 2 ^ (prefixWord ++ tailWord_3572).sum := by decide
  have hdescent : baseEnd_3572 < baseStart_3572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602 : List Nat := [3, 2, 6]
def baseStart_3602 : Nat := 118140960795 + 3602 * 2 ^ 59
def prefixEnd_3602 : Nat := 4983230072969 + 3 ^ 40 * 3602 * 2
def baseEnd_3602 : Nat := 1154669527951558749607

theorem tailTrace_3602 : CollatzResearch.WordTrace tailWord_3602 prefixEnd_3602 1154669527951558749607 := by
  unfold tailWord_3602
  simp only [CollatzResearch.WordTrace]
  refine ⟨32843933239511004433265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87583821972029345155373 32843933239511004433265)
  ·
    refine ⟨24632949929633253324949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32843933239511004433265 24632949929633253324949)
    ·
      refine ⟨1154669527951558749607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24632949929633253324949 1154669527951558749607)
      ·
        rfl

theorem cell_3602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_3602 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3602 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3602 prefixEnd_3602 := by
    exact prefixLift 3602
  have htrace : WordTrace (prefixWord ++ tailWord_3602) baseStart_3602 baseEnd_3602 := by
    simpa [prefixWord, tailWord_3602, baseEnd_3602] using wordTrace_append hprefix tailTrace_3602
  have hstable : (prefixWord ++ tailWord_3602).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602).length < 2 ^ (prefixWord ++ tailWord_3602).sum := by decide
  have hdescent : baseEnd_3602 < baseStart_3602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606 : List Nat := [5, 5]
def baseStart_3606 : Nat := 118140960795 + 3606 * 2 ^ 59
def prefixEnd_3606 : Nat := 4983230072969 + 3 ^ 40 * 3606 * 2
def baseEnd_3606 : Nat := 770634521153629106711

theorem tailTrace_3606 : CollatzResearch.WordTrace tailWord_3606 prefixEnd_3606 770634521153629106711 := by
  unfold tailWord_3606
  simp only [CollatzResearch.WordTrace]
  refine ⟨8220101558972043804917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87681083295701800585781 8220101558972043804917)
  ·
    refine ⟨770634521153629106711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8220101558972043804917 770634521153629106711)
    ·
      rfl

theorem cell_3606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_3606 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3606 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3606 prefixEnd_3606 := by
    exact prefixLift 3606
  have htrace : WordTrace (prefixWord ++ tailWord_3606) baseStart_3606 baseEnd_3606 := by
    simpa [prefixWord, tailWord_3606, baseEnd_3606] using wordTrace_append hprefix tailTrace_3606
  have hstable : (prefixWord ++ tailWord_3606).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606).length < 2 ^ (prefixWord ++ tailWord_3606).sum := by decide
  have hdescent : baseEnd_3606 < baseStart_3606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622 : List Nat := [8]
def baseStart_3622 : Nat := 118140960795 + 3622 * 2 ^ 59
def prefixEnd_3622 : Nat := 4983230072969 + 3 ^ 40 * 3622 * 2
def baseEnd_3622 : Nat := 1032071819418651823915

theorem tailTrace_3622 : CollatzResearch.WordTrace tailWord_3622 prefixEnd_3622 1032071819418651823915 := by
  unfold tailWord_3622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1032071819418651823915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 88070128590391622307413 1032071819418651823915)
  ·
    rfl

theorem cell_3622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_3622 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3622 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3622 prefixEnd_3622 := by
    exact prefixLift 3622
  have htrace : WordTrace (prefixWord ++ tailWord_3622) baseStart_3622 baseEnd_3622 := by
    simpa [prefixWord, tailWord_3622, baseEnd_3622] using wordTrace_append hprefix tailTrace_3622
  have hstable : (prefixWord ++ tailWord_3622).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622).length < 2 ^ (prefixWord ++ tailWord_3622).sum := by decide
  have hdescent : baseEnd_3622 < baseStart_3622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623 : List Nat := [1, 1, 7, 3]
def baseStart_3623 : Nat := 118140960795 + 3623 * 2 ^ 59
def prefixEnd_3623 : Nat := 4983230072969 + 3 ^ 40 * 3623 * 2
def baseEnd_3623 : Nat := 1742102040436056794279

theorem tailTrace_3623 : CollatzResearch.WordTrace tailWord_3623 prefixEnd_3623 1742102040436056794279 := by
  unfold tailWord_3623
  simp only [CollatzResearch.WordTrace]
  refine ⟨132141665881964604247523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88094443921309736165015 132141665881964604247523)
  ·
    refine ⟨198212498822946906371285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132141665881964604247523 198212498822946906371285)
    ·
      refine ⟨4645605441162818118077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 198212498822946906371285 4645605441162818118077)
      ·
        refine ⟨1742102040436056794279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4645605441162818118077 1742102040436056794279)
        ·
          rfl

theorem cell_3623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_3623 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3623 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3623 prefixEnd_3623 := by
    exact prefixLift 3623
  have htrace : WordTrace (prefixWord ++ tailWord_3623) baseStart_3623 baseEnd_3623 := by
    simpa [prefixWord, tailWord_3623, baseEnd_3623] using wordTrace_append hprefix tailTrace_3623
  have hstable : (prefixWord ++ tailWord_3623).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623).length < 2 ^ (prefixWord ++ tailWord_3623).sum := by decide
  have hdescent : baseEnd_3623 < baseStart_3623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629 : List Nat := [1, 5, 4, 2]
def baseStart_3629 : Nat := 118140960795 + 3629 * 2 ^ 59
def prefixEnd_3629 : Nat := 4983230072969 + 3 ^ 40 * 3629 * 2
def baseEnd_3629 : Nat := 1744987111438547842813

theorem tailTrace_3629 : CollatzResearch.WordTrace tailWord_3629 prefixEnd_3629 1744987111438547842813 := by
  unfold tailWord_3629
  simp only [CollatzResearch.WordTrace]
  refine ⟨132360503860227628965941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88240335906818419310627 132360503860227628965941)
  ·
    refine ⟨12408797236896340215557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132360503860227628965941 12408797236896340215557)
    ·
      refine ⟨2326649481918063790417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12408797236896340215557 2326649481918063790417)
      ·
        refine ⟨1744987111438547842813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2326649481918063790417 1744987111438547842813)
        ·
          rfl

theorem cell_3629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_3629 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3629 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3629 prefixEnd_3629 := by
    exact prefixLift 3629
  have htrace : WordTrace (prefixWord ++ tailWord_3629) baseStart_3629 baseEnd_3629 := by
    simpa [prefixWord, tailWord_3629, baseEnd_3629] using wordTrace_append hprefix tailTrace_3629
  have hstable : (prefixWord ++ tailWord_3629).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629).length < 2 ^ (prefixWord ++ tailWord_3629).sum := by decide
  have hdescent : baseEnd_3629 < baseStart_3629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636 : List Nat := [2, 5, 1, 4]
def baseStart_3636 : Nat := 118140960795 + 3636 * 2 ^ 59
def prefixEnd_3636 : Nat := 4983230072969 + 3 ^ 40 * 3636 * 2
def baseEnd_3636 : Nat := 1748353027608120732769

theorem tailTrace_3636 : CollatzResearch.WordTrace tailWord_3636 prefixEnd_3636 1748353027608120732769 := by
  unfold tailWord_3636
  simp only [CollatzResearch.WordTrace]
  refine ⟨66307907417433912235381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88410543223245216313841 66307907417433912235381)
  ·
    refine ⟨6216366320384429272067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66307907417433912235381 6216366320384429272067)
    ·
      refine ⟨9324549480576643908101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6216366320384429272067 9324549480576643908101)
      ·
        refine ⟨1748353027608120732769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9324549480576643908101 1748353027608120732769)
        ·
          rfl

theorem cell_3636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_3636 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3636 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3636 prefixEnd_3636 := by
    exact prefixLift 3636
  have htrace : WordTrace (prefixWord ++ tailWord_3636) baseStart_3636 baseEnd_3636 := by
    simpa [prefixWord, tailWord_3636, baseEnd_3636] using wordTrace_append hprefix tailTrace_3636
  have hstable : (prefixWord ++ tailWord_3636).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636).length < 2 ^ (prefixWord ++ tailWord_3636).sum := by decide
  have hdescent : baseEnd_3636 < baseStart_3636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650 : List Nat := [3, 6]
def baseStart_3650 : Nat := 118140960795 + 3650 * 2 ^ 59
def prefixEnd_3650 : Nat := 4983230072969 + 3 ^ 40 * 3650 * 2
def baseEnd_3650 : Nat := 1560075431064236900161

theorem tailTrace_3650 : CollatzResearch.WordTrace tailWord_3650 prefixEnd_3650 1560075431064236900161 := by
  unfold tailWord_3650
  simp only [CollatzResearch.WordTrace]
  refine ⟨33281609196037053870101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88750957856098810320269 33281609196037053870101)
  ·
    refine ⟨1560075431064236900161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33281609196037053870101 1560075431064236900161)
    ·
      rfl

theorem cell_3650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_3650 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3650 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3650 prefixEnd_3650 := by
    exact prefixLift 3650
  have htrace : WordTrace (prefixWord ++ tailWord_3650) baseStart_3650 baseEnd_3650 := by
    simpa [prefixWord, tailWord_3650, baseEnd_3650] using wordTrace_append hprefix tailTrace_3650
  have hstable : (prefixWord ++ tailWord_3650).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650).length < 2 ^ (prefixWord ++ tailWord_3650).sum := by decide
  have hdescent : baseEnd_3650 < baseStart_3650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682 : List Nat := [3, 3, 2, 4]
def baseStart_3682 : Nat := 118140960795 + 3682 * 2 ^ 59
def prefixEnd_3682 : Nat := 4983230072969 + 3 ^ 40 * 3682 * 2
def baseEnd_3682 : Nat := 1770471905293885438195

theorem tailTrace_3682 : CollatzResearch.WordTrace tailWord_3682 prefixEnd_3682 1770471905293885438195 := by
  unfold tailWord_3682
  simp only [CollatzResearch.WordTrace]
  refine ⟨33573393167054420161325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89529048445478453763533 33573393167054420161325)
  ·
    refine ⟨12590022437645407560497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33573393167054420161325 12590022437645407560497)
    ·
      refine ⟨9442516828234055670373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12590022437645407560497 9442516828234055670373)
      ·
        refine ⟨1770471905293885438195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9442516828234055670373 1770471905293885438195)
        ·
          rfl

theorem cell_3682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_3682 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3682 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3682 prefixEnd_3682 := by
    exact prefixLift 3682
  have htrace : WordTrace (prefixWord ++ tailWord_3682) baseStart_3682 baseEnd_3682 := by
    simpa [prefixWord, tailWord_3682, baseEnd_3682] using wordTrace_append hprefix tailTrace_3682
  have hstable : (prefixWord ++ tailWord_3682).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682).length < 2 ^ (prefixWord ++ tailWord_3682).sum := by decide
  have hdescent : baseEnd_3682 < baseStart_3682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686 : List Nat := [7]
def baseStart_3686 : Nat := 118140960795 + 3686 * 2 ^ 59
def prefixEnd_3686 : Nat := 4983230072969 + 3 ^ 40 * 3686 * 2
def baseEnd_3686 : Nat := 2100616635214474434233

theorem tailTrace_3686 : CollatzResearch.WordTrace tailWord_3686 prefixEnd_3686 2100616635214474434233 := by
  unfold tailWord_3686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100616635214474434233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 89626309769150909193941 2100616635214474434233)
  ·
    rfl

theorem cell_3686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3686 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3686 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3686 prefixEnd_3686 := by
    exact prefixLift 3686
  have htrace : WordTrace (prefixWord ++ tailWord_3686) baseStart_3686 baseEnd_3686 := by
    simpa [prefixWord, tailWord_3686, baseEnd_3686] using wordTrace_append hprefix tailTrace_3686
  have hstable : (prefixWord ++ tailWord_3686).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686).length < 2 ^ (prefixWord ++ tailWord_3686).sum := by decide
  have hdescent : baseEnd_3686 < baseStart_3686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700 : List Nat := [2, 7]
def baseStart_3700 : Nat := 118140960795 + 3700 * 2 ^ 59
def prefixEnd_3700 : Nat := 4983230072969 + 3 ^ 40 * 3700 * 2
def baseEnd_3700 : Nat := 1581446327378985407819

theorem tailTrace_3700 : CollatzResearch.WordTrace tailWord_3700 prefixEnd_3700 1581446327378985407819 := by
  unfold tailWord_3700
  simp only [CollatzResearch.WordTrace]
  refine ⟨67475043301503377400277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89966724402004503200369 67475043301503377400277)
  ·
    refine ⟨1581446327378985407819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 67475043301503377400277 1581446327378985407819)
    ·
      rfl

theorem cell_3700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_3700 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3700 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3700 prefixEnd_3700 := by
    exact prefixLift 3700
  have htrace : WordTrace (prefixWord ++ tailWord_3700) baseStart_3700 baseEnd_3700 := by
    simpa [prefixWord, tailWord_3700, baseEnd_3700] using wordTrace_append hprefix tailTrace_3700
  have hstable : (prefixWord ++ tailWord_3700).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700).length < 2 ^ (prefixWord ++ tailWord_3700).sum := by decide
  have hdescent : baseEnd_3700 < baseStart_3700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3710 : List Nat := [4, 2, 5]
def baseStart_3710 : Nat := 118140960795 + 3710 * 2 ^ 59
def prefixEnd_3710 : Nat := 4983230072969 + 3 ^ 40 * 3710 * 2
def baseEnd_3710 : Nat := 1189290379981451332013

theorem tailTrace_3710 : CollatzResearch.WordTrace tailWord_3710 prefixEnd_3710 1189290379981451332013 := by
  unfold tailWord_3710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16914352070847307833073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90209877711185641776389 16914352070847307833073)
  ·
    refine ⟨12685764053135480874805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16914352070847307833073 12685764053135480874805)
    ·
      refine ⟨1189290379981451332013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12685764053135480874805 1189290379981451332013)
      ·
        rfl

theorem cell_3710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_3710 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3710 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3710 prefixEnd_3710 := by
    exact prefixLift 3710
  have htrace : WordTrace (prefixWord ++ tailWord_3710) baseStart_3710 baseEnd_3710 := by
    simpa [prefixWord, tailWord_3710, baseEnd_3710] using wordTrace_append hprefix tailTrace_3710
  have hstable : (prefixWord ++ tailWord_3710).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3710).length < 2 ^ (prefixWord ++ tailWord_3710).sum := by decide
  have hdescent : baseEnd_3710 < baseStart_3710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714 : List Nat := [3, 4, 3, 2]
def baseStart_3714 : Nat := 118140960795 + 3714 * 2 ^ 59
def prefixEnd_3714 : Nat := 4983230072969 + 3 ^ 40 * 3714 * 2
def baseEnd_3714 : Nat := 1785858950640504363709

theorem tailTrace_3714 : CollatzResearch.WordTrace tailWord_3714 prefixEnd_3714 1785858950640504363709 := by
  unfold tailWord_3714
  simp only [CollatzResearch.WordTrace]
  refine ⟨33865177138071786452549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90307139034858097206797 33865177138071786452549)
  ·
    refine ⟨6349720713388459959853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33865177138071786452549 6349720713388459959853)
    ·
      refine ⟨2381145267520672484945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6349720713388459959853 2381145267520672484945)
      ·
        refine ⟨1785858950640504363709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2381145267520672484945 1785858950640504363709)
        ·
          rfl

theorem cell_3714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_3714 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3714 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3714 prefixEnd_3714 := by
    exact prefixLift 3714
  have htrace : WordTrace (prefixWord ++ tailWord_3714) baseStart_3714 baseEnd_3714 := by
    simpa [prefixWord, tailWord_3714, baseEnd_3714] using wordTrace_append hprefix tailTrace_3714
  have hstable : (prefixWord ++ tailWord_3714).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714).length < 2 ^ (prefixWord ++ tailWord_3714).sum := by decide
  have hdescent : baseEnd_3714 < baseStart_3714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734 : List Nat := [5, 3, 4]
def baseStart_3734 : Nat := 118140960795 + 3734 * 2 ^ 59
def prefixEnd_3734 : Nat := 4983230072969 + 3 ^ 40 * 3734 * 2
def baseEnd_3734 : Nat := 598491951327380397385

theorem tailTrace_3734 : CollatzResearch.WordTrace tailWord_3734 prefixEnd_3734 598491951327380397385 := by
  unfold tailWord_3734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8511885529989410096141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90793445653220374358837 8511885529989410096141)
  ·
    refine ⟨3191957073746028786053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8511885529989410096141 3191957073746028786053)
    ·
      refine ⟨598491951327380397385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3191957073746028786053 598491951327380397385)
      ·
        rfl

theorem cell_3734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_3734 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3734 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3734 prefixEnd_3734 := by
    exact prefixLift 3734
  have htrace : WordTrace (prefixWord ++ tailWord_3734) baseStart_3734 baseEnd_3734 := by
    simpa [prefixWord, tailWord_3734, baseEnd_3734] using wordTrace_append hprefix tailTrace_3734
  have hstable : (prefixWord ++ tailWord_3734).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734).length < 2 ^ (prefixWord ++ tailWord_3734).sum := by decide
  have hdescent : baseEnd_3734 < baseStart_3734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750 : List Nat := [9]
def baseStart_3750 : Nat := 118140960795 + 3750 * 2 ^ 59
def prefixEnd_3750 : Nat := 4983230072969 + 3 ^ 40 * 3750 * 2
def baseEnd_3750 : Nat := 534272407897911305159

theorem tailTrace_3750 : CollatzResearch.WordTrace tailWord_3750 prefixEnd_3750 534272407897911305159 := by
  unfold tailWord_3750
  simp only [CollatzResearch.WordTrace]
  refine ⟨534272407897911305159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 9 91182490947910196080469 534272407897911305159)
  ·
    rfl

theorem cell_3750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_3750 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3750 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3750 prefixEnd_3750 := by
    exact prefixLift 3750
  have htrace : WordTrace (prefixWord ++ tailWord_3750) baseStart_3750 baseEnd_3750 := by
    simpa [prefixWord, tailWord_3750, baseEnd_3750] using wordTrace_append hprefix tailTrace_3750
  have hstable : (prefixWord ++ tailWord_3750).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750).length < 2 ^ (prefixWord ++ tailWord_3750).sum := by decide
  have hdescent : baseEnd_3750 < baseStart_3750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754 : List Nat := [3, 1, 5, 3]
def baseStart_3754 : Nat := 118140960795 + 3754 * 2 ^ 59
def prefixEnd_3754 : Nat := 4983230072969 + 3 ^ 40 * 3754 * 2
def baseEnd_3754 : Nat := 1805092757323778020601

theorem tailTrace_3754 : CollatzResearch.WordTrace tailWord_3754 prefixEnd_3754 1805092757323778020601 := by
  unfold tailWord_3754
  simp only [CollatzResearch.WordTrace]
  refine ⟨34229907101843494316579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91279752271582651510877 34229907101843494316579)
  ·
    refine ⟨51344860652765241474869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34229907101843494316579 51344860652765241474869)
    ·
      refine ⟨4813580686196741388269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51344860652765241474869 4813580686196741388269)
      ·
        refine ⟨1805092757323778020601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4813580686196741388269 1805092757323778020601)
        ·
          rfl

theorem cell_3754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_3754 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3754 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3754 prefixEnd_3754 := by
    exact prefixLift 3754
  have htrace : WordTrace (prefixWord ++ tailWord_3754) baseStart_3754 baseEnd_3754 := by
    simpa [prefixWord, tailWord_3754, baseEnd_3754] using wordTrace_append hprefix tailTrace_3754
  have hstable : (prefixWord ++ tailWord_3754).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754).length < 2 ^ (prefixWord ++ tailWord_3754).sum := by decide
  have hdescent : baseEnd_3754 < baseStart_3754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761 : List Nat := [1, 2, 2, 7]
def baseStart_3761 : Nat := 118140960795 + 3761 * 2 ^ 59
def prefixEnd_3761 : Nat := 4983230072969 + 3 ^ 40 * 3761 * 2
def baseEnd_3761 : Nat := 1808458673493350910557

theorem tailTrace_3761 : CollatzResearch.WordTrace tailWord_3761 prefixEnd_3761 1808458673493350910557 := by
  unfold tailWord_3761
  simp only [CollatzResearch.WordTrace]
  refine ⟨137174939382014172771137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91449959588009448514091 137174939382014172771137)
  ·
    refine ⟨102881204536510629578353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137174939382014172771137 102881204536510629578353)
    ·
      refine ⟨77160903402382972183765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102881204536510629578353 77160903402382972183765)
      ·
        refine ⟨1808458673493350910557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 77160903402382972183765 1808458673493350910557)
        ·
          rfl

theorem cell_3761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_3761 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3761 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3761 prefixEnd_3761 := by
    exact prefixLift 3761
  have htrace : WordTrace (prefixWord ++ tailWord_3761) baseStart_3761 baseEnd_3761 := by
    simpa [prefixWord, tailWord_3761, baseEnd_3761] using wordTrace_append hprefix tailTrace_3761
  have hstable : (prefixWord ++ tailWord_3761).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761).length < 2 ^ (prefixWord ++ tailWord_3761).sum := by decide
  have hdescent : baseEnd_3761 < baseStart_3761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806 : List Nat := [4, 6]
def baseStart_3806 : Nat := 118140960795 + 3806 * 2 ^ 59
def prefixEnd_3806 : Nat := 4983230072969 + 3 ^ 40 * 3806 * 2
def baseEnd_3806 : Nat := 813376313783126122027

theorem tailTrace_3806 : CollatzResearch.WordTrace tailWord_3806 prefixEnd_3806 813376313783126122027 := by
  unfold tailWord_3806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17352028027373357269909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92544149479324572106181 17352028027373357269909)
  ·
    refine ⟨813376313783126122027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17352028027373357269909 813376313783126122027)
    ·
      rfl

theorem cell_3806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_3806 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3806 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3806 prefixEnd_3806 := by
    exact prefixLift 3806
  have htrace : WordTrace (prefixWord ++ tailWord_3806) baseStart_3806 baseEnd_3806 := by
    simpa [prefixWord, tailWord_3806, baseEnd_3806] using wordTrace_append hprefix tailTrace_3806
  have hstable : (prefixWord ++ tailWord_3806).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806).length < 2 ^ (prefixWord ++ tailWord_3806).sum := by decide
  have hdescent : baseEnd_3806 < baseStart_3806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814 : List Nat := [7]
def baseStart_3814 : Nat := 118140960795 + 3814 * 2 ^ 59
def prefixEnd_3814 : Nat := 4983230072969 + 3 ^ 40 * 3814 * 2
def baseEnd_3814 : Nat := 2173562627968816007039

theorem tailTrace_3814 : CollatzResearch.WordTrace tailWord_3814 prefixEnd_3814 2173562627968816007039 := by
  unfold tailWord_3814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2173562627968816007039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 92738672126669482966997 2173562627968816007039)
  ·
    rfl

theorem cell_3814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3814 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3814 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3814 prefixEnd_3814 := by
    exact prefixLift 3814
  have htrace : WordTrace (prefixWord ++ tailWord_3814) baseStart_3814 baseEnd_3814 := by
    simpa [prefixWord, tailWord_3814, baseEnd_3814] using wordTrace_append hprefix tailTrace_3814
  have hstable : (prefixWord ++ tailWord_3814).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814).length < 2 ^ (prefixWord ++ tailWord_3814).sum := by decide
  have hdescent : baseEnd_3814 < baseStart_3814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3862 : List Nat := [5, 4]
def baseStart_3862 : Nat := 118140960795 + 3862 * 2 ^ 59
def prefixEnd_3862 : Nat := 4983230072969 + 3 ^ 40 * 3862 * 2
def baseEnd_3862 : Nat := 1650688031438770572631

theorem tailTrace_3862 : CollatzResearch.WordTrace tailWord_3862 prefixEnd_3862 1650688031438770572631 := by
  unfold tailWord_3862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8803669501006776387365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93905808010738948131893 8803669501006776387365)
  ·
    refine ⟨1650688031438770572631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8803669501006776387365 1650688031438770572631)
    ·
      rfl

theorem cell_3862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_3862 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3862 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3862 prefixEnd_3862 := by
    exact prefixLift 3862
  have htrace : WordTrace (prefixWord ++ tailWord_3862) baseStart_3862 baseEnd_3862 := by
    simpa [prefixWord, tailWord_3862, baseEnd_3862] using wordTrace_append hprefix tailTrace_3862
  have hstable : (prefixWord ++ tailWord_3862).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3862).length < 2 ^ (prefixWord ++ tailWord_3862).sum := by decide
  have hdescent : baseEnd_3862 < baseStart_3862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878 : List Nat := [8]
def baseStart_3878 : Nat := 118140960795 + 3878 * 2 ^ 59
def prefixEnd_3878 : Nat := 4983230072969 + 3 ^ 40 * 3878 * 2
def baseEnd_3878 : Nat := 1105017812172993396721

theorem tailTrace_3878 : CollatzResearch.WordTrace tailWord_3878 prefixEnd_3878 1105017812172993396721 := by
  unfold tailWord_3878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105017812172993396721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 8 94294853305428769853525 1105017812172993396721)
  ·
    rfl

theorem cell_3878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_3878 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3878 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3878 prefixEnd_3878 := by
    exact prefixLift 3878
  have htrace : WordTrace (prefixWord ++ tailWord_3878) baseStart_3878 baseEnd_3878 := by
    simpa [prefixWord, tailWord_3878, baseEnd_3878] using wordTrace_append hprefix tailTrace_3878
  have hstable : (prefixWord ++ tailWord_3878).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878).length < 2 ^ (prefixWord ++ tailWord_3878).sum := by decide
  have hdescent : baseEnd_3878 < baseStart_3878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3879 : List Nat := [1, 1, 10]
def baseStart_3879 : Nat := 118140960795 + 3879 * 2 ^ 59
def prefixEnd_3879 : Nat := 4983230072969 + 3 ^ 40 * 3879 * 2
def baseEnd_3879 : Nat := 621732801069669399463

theorem tailTrace_3879 : CollatzResearch.WordTrace tailWord_3879 prefixEnd_3879 621732801069669399463 := by
  unfold tailWord_3879
  simp only [CollatzResearch.WordTrace]
  refine ⟨141478752954520325566691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94319168636346883711127 141478752954520325566691)
  ·
    refine ⟨212218129431780488350037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141478752954520325566691 212218129431780488350037)
    ·
      refine ⟨621732801069669399463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 10 212218129431780488350037 621732801069669399463)
      ·
        rfl

theorem cell_3879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_3879 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3879 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3879 prefixEnd_3879 := by
    exact prefixLift 3879
  have htrace : WordTrace (prefixWord ++ tailWord_3879) baseStart_3879 baseEnd_3879 := by
    simpa [prefixWord, tailWord_3879, baseEnd_3879] using wordTrace_append hprefix tailTrace_3879
  have hstable : (prefixWord ++ tailWord_3879).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3879).length < 2 ^ (prefixWord ++ tailWord_3879).sum := by decide
  have hdescent : baseEnd_3879 < baseStart_3879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3885 : List Nat := [1, 5, 3, 3]
def baseStart_3885 : Nat := 118140960795 + 3885 * 2 ^ 59
def prefixEnd_3885 : Nat := 4983230072969 + 3 ^ 40 * 3885 * 2
def baseEnd_3885 : Nat := 1868083474211499246923

theorem tailTrace_3885 : CollatzResearch.WordTrace tailWord_3885 prefixEnd_3885 1868083474211499246923 := by
  unfold tailWord_3885
  simp only [CollatzResearch.WordTrace]
  refine ⟨141697590932783350285109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94465060621855566856739 141697590932783350285109)
  ·
    refine ⟨13284149149948439089229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141697590932783350285109 13284149149948439089229)
    ·
      refine ⟨4981555931230664658461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13284149149948439089229 4981555931230664658461)
      ·
        refine ⟨1868083474211499246923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4981555931230664658461 1868083474211499246923)
        ·
          rfl

theorem cell_3885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_3885 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3885 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3885 prefixEnd_3885 := by
    exact prefixLift 3885
  have htrace : WordTrace (prefixWord ++ tailWord_3885) baseStart_3885 baseEnd_3885 := by
    simpa [prefixWord, tailWord_3885, baseEnd_3885] using wordTrace_append hprefix tailTrace_3885
  have hstable : (prefixWord ++ tailWord_3885).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3885).length < 2 ^ (prefixWord ++ tailWord_3885).sum := by decide
  have hdescent : baseEnd_3885 < baseStart_3885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905 : List Nat := [1, 2, 5, 4]
def baseStart_3905 : Nat := 118140960795 + 3905 * 2 ^ 59
def prefixEnd_3905 : Nat := 4983230072969 + 3 ^ 40 * 3905 * 2
def baseEnd_3905 : Nat := 1877700377553136075369

theorem tailTrace_3905 : CollatzResearch.WordTrace tailWord_3905 prefixEnd_3905 1877700377553136075369 := by
  unfold tailWord_3905
  simp only [CollatzResearch.WordTrace]
  refine ⟨142427050860326766013169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94951367240217844008779 142427050860326766013169)
  ·
    refine ⟨106820288145245074509877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142427050860326766013169 106820288145245074509877)
    ·
      refine ⟨10014402013616725735301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106820288145245074509877 10014402013616725735301)
      ·
        refine ⟨1877700377553136075369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10014402013616725735301 1877700377553136075369)
        ·
          rfl

theorem cell_3905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_3905 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3905 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3905 prefixEnd_3905 := by
    exact prefixLift 3905
  have htrace : WordTrace (prefixWord ++ tailWord_3905) baseStart_3905 baseEnd_3905 := by
    simpa [prefixWord, tailWord_3905, baseEnd_3905] using wordTrace_append hprefix tailTrace_3905
  have hstable : (prefixWord ++ tailWord_3905).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905).length < 2 ^ (prefixWord ++ tailWord_3905).sum := by decide
  have hdescent : baseEnd_3905 < baseStart_3905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906 : List Nat := [3, 7]
def baseStart_3906 : Nat := 118140960795 + 3906 * 2 ^ 59
def prefixEnd_3906 : Nat := 4983230072969 + 3 ^ 40 * 3906 * 2
def baseEnd_3906 : Nat := 834747210097874629685

theorem tailTrace_3906 : CollatzResearch.WordTrace tailWord_3906 prefixEnd_3906 834747210097874629685 := by
  unfold tailWord_3906
  simp only [CollatzResearch.WordTrace]
  refine ⟨35615880964175984199893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94975682571135957866381 35615880964175984199893)
  ·
    refine ⟨834747210097874629685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 35615880964175984199893 834747210097874629685)
    ·
      rfl

theorem cell_3906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_3906 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3906 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3906 prefixEnd_3906 := by
    exact prefixLift 3906
  have htrace : WordTrace (prefixWord ++ tailWord_3906) baseStart_3906 baseEnd_3906 := by
    simpa [prefixWord, tailWord_3906, baseEnd_3906] using wordTrace_append hprefix tailTrace_3906
  have hstable : (prefixWord ++ tailWord_3906).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906).length < 2 ^ (prefixWord ++ tailWord_3906).sum := by decide
  have hdescent : baseEnd_3906 < baseStart_3906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926 : List Nat := [5, 2, 4]
def baseStart_3926 : Nat := 118140960795 + 3926 * 2 ^ 59
def prefixEnd_3926 : Nat := 4983230072969 + 3 ^ 40 * 3926 * 2
def baseEnd_3926 : Nat := 1258532084041236496825

theorem tailTrace_3926 : CollatzResearch.WordTrace tailWord_3926 prefixEnd_3926 1258532084041236496825 := by
  unfold tailWord_3926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8949561486515459532977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95461989189498235018421 8949561486515459532977)
  ·
    refine ⟨6712171114886594649733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8949561486515459532977 6712171114886594649733)
    ·
      refine ⟨1258532084041236496825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6712171114886594649733 1258532084041236496825)
      ·
        rfl

theorem cell_3926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_3926 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3926 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3926 prefixEnd_3926 := by
    exact prefixLift 3926
  have htrace : WordTrace (prefixWord ++ tailWord_3926) baseStart_3926 baseEnd_3926 := by
    simpa [prefixWord, tailWord_3926, baseEnd_3926] using wordTrace_append hprefix tailTrace_3926
  have hstable : (prefixWord ++ tailWord_3926).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926).length < 2 ^ (prefixWord ++ tailWord_3926).sum := by decide
  have hdescent : baseEnd_3926 < baseStart_3926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3933 : List Nat := [1, 4, 6]
def baseStart_3933 : Nat := 118140960795 + 3933 * 2 ^ 59
def prefixEnd_3933 : Nat := 4983230072969 + 3 ^ 40 * 3933 * 2
def baseEnd_3933 : Nat := 1260776028154285090129

theorem tailTrace_3933 : CollatzResearch.WordTrace tailWord_3933 prefixEnd_3933 1260776028154285090129 := by
  unfold tailWord_3933
  simp only [CollatzResearch.WordTrace]
  refine ⟨143448294758887548032453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95632196505925032021635 143448294758887548032453)
  ·
    refine ⟨26896555267291415256085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143448294758887548032453 26896555267291415256085)
    ·
      refine ⟨1260776028154285090129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26896555267291415256085 1260776028154285090129)
      ·
        rfl

theorem cell_3933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_3933 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3933 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3933 prefixEnd_3933 := by
    exact prefixLift 3933
  have htrace : WordTrace (prefixWord ++ tailWord_3933) baseStart_3933 baseEnd_3933 := by
    simpa [prefixWord, tailWord_3933, baseEnd_3933] using wordTrace_append hprefix tailTrace_3933
  have hstable : (prefixWord ++ tailWord_3933).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3933).length < 2 ^ (prefixWord ++ tailWord_3933).sum := by decide
  have hdescent : baseEnd_3933 < baseStart_3933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3942 : List Nat := [7]
def baseStart_3942 : Nat := 118140960795 + 3942 * 2 ^ 59
def prefixEnd_3942 : Nat := 4983230072969 + 3 ^ 40 * 3942 * 2
def baseEnd_3942 : Nat := 2246508620723157579845

theorem tailTrace_3942 : CollatzResearch.WordTrace tailWord_3942 prefixEnd_3942 2246508620723157579845 := by
  unfold tailWord_3942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2246508620723157579845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 95851034484188056740053 2246508620723157579845)
  ·
    rfl

theorem cell_3942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3942 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3942 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3942 prefixEnd_3942 := by
    exact prefixLift 3942
  have htrace : WordTrace (prefixWord ++ tailWord_3942) baseStart_3942 baseEnd_3942 := by
    simpa [prefixWord, tailWord_3942, baseEnd_3942] using wordTrace_append hprefix tailTrace_3942
  have hstable : (prefixWord ++ tailWord_3942).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3942).length < 2 ^ (prefixWord ++ tailWord_3942).sum := by decide
  have hdescent : baseEnd_3942 < baseStart_3942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956 : List Nat := [2, 9]
def baseStart_3956 : Nat := 118140960795 + 3956 * 2 ^ 59
def prefixEnd_3956 : Nat := 4983230072969 + 3 ^ 40 * 3956 * 2
def baseEnd_3956 : Nat := 422716329127624441757

theorem tailTrace_3956 : CollatzResearch.WordTrace tailWord_3956 prefixEnd_3956 422716329127624441757 := by
  unfold tailWord_3956
  simp only [CollatzResearch.WordTrace]
  refine ⟨72143586837781238059861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96191449117041650746481 72143586837781238059861)
  ·
    refine ⟨422716329127624441757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 9 72143586837781238059861 422716329127624441757)
    ·
      rfl

theorem cell_3956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_3956 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3956 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3956 prefixEnd_3956 := by
    exact prefixLift 3956
  have htrace : WordTrace (prefixWord ++ tailWord_3956) baseStart_3956 baseEnd_3956 := by
    simpa [prefixWord, tailWord_3956, baseEnd_3956] using wordTrace_append hprefix tailTrace_3956
  have hstable : (prefixWord ++ tailWord_3956).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956).length < 2 ^ (prefixWord ++ tailWord_3956).sum := by decide
  have hdescent : baseEnd_3956 < baseStart_3956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970 : List Nat := [3, 4, 2, 3]
def baseStart_3970 : Nat := 118140960795 + 3970 * 2 ^ 59
def prefixEnd_3970 : Nat := 4983230072969 + 3 ^ 40 * 3970 * 2
def baseEnd_3970 : Nat := 1908955313413455767819

theorem tailTrace_3970 : CollatzResearch.WordTrace tailWord_3970 prefixEnd_3970 1908955313413455767819 := by
  unfold tailWord_3970
  simp only [CollatzResearch.WordTrace]
  refine ⟨36199448906210716782341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96531863749895244752909 36199448906210716782341)
  ·
    refine ⟨6787396669914509396689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36199448906210716782341 6787396669914509396689)
    ·
      refine ⟨5090547502435882047517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6787396669914509396689 5090547502435882047517)
      ·
        refine ⟨1908955313413455767819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5090547502435882047517 1908955313413455767819)
        ·
          rfl

theorem cell_3970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_3970 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3970 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3970 prefixEnd_3970 := by
    exact prefixLift 3970
  have htrace : WordTrace (prefixWord ++ tailWord_3970) baseStart_3970 baseEnd_3970 := by
    simpa [prefixWord, tailWord_3970, baseEnd_3970] using wordTrace_append hprefix tailTrace_3970
  have hstable : (prefixWord ++ tailWord_3970).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970).length < 2 ^ (prefixWord ++ tailWord_3970).sum := by decide
  have hdescent : baseEnd_3970 < baseStart_3970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974 : List Nat := [6, 3]
def baseStart_3974 : Nat := 118140960795 + 3974 * 2 ^ 59
def prefixEnd_3974 : Nat := 4983230072969 + 3 ^ 40 * 3974 * 2
def baseEnd_3974 : Nat := 1698558839183807229785

theorem tailTrace_3974 : CollatzResearch.WordTrace tailWord_3974 prefixEnd_3974 1698558839183807229785 := by
  unfold tailWord_3974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4529490237823485946093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96629125073567700183317 4529490237823485946093)
  ·
    refine ⟨1698558839183807229785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4529490237823485946093 1698558839183807229785)
    ·
      rfl

theorem cell_3974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_3974 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3974 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3974 prefixEnd_3974 := by
    exact prefixLift 3974
  have htrace : WordTrace (prefixWord ++ tailWord_3974) baseStart_3974 baseEnd_3974 := by
    simpa [prefixWord, tailWord_3974, baseEnd_3974] using wordTrace_append hprefix tailTrace_3974
  have hstable : (prefixWord ++ tailWord_3974).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974).length < 2 ^ (prefixWord ++ tailWord_3974).sum := by decide
  have hdescent : baseEnd_3974 < baseStart_3974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3981 : List Nat := [1, 8]
def baseStart_3981 : Nat := 118140960795 + 3981 * 2 ^ 59
def prefixEnd_3981 : Nat := 4983230072969 + 3 ^ 40 * 3981 * 2
def baseEnd_3981 : Nat := 1701550764667872020857

theorem tailTrace_3981 : CollatzResearch.WordTrace tailWord_3981 prefixEnd_3981 1701550764667872020857 := by
  unfold tailWord_3981
  simp only [CollatzResearch.WordTrace]
  refine ⟨145198998584991745779797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96799332389994497186531 145198998584991745779797)
  ·
    refine ⟨1701550764667872020857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 8 145198998584991745779797 1701550764667872020857)
    ·
      rfl

theorem cell_3981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_3981 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_3981 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_3981 prefixEnd_3981 := by
    exact prefixLift 3981
  have htrace : WordTrace (prefixWord ++ tailWord_3981) baseStart_3981 baseEnd_3981 := by
    simpa [prefixWord, tailWord_3981, baseEnd_3981] using wordTrace_append hprefix tailTrace_3981
  have hstable : (prefixWord ++ tailWord_3981).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3981).length < 2 ^ (prefixWord ++ tailWord_3981).sum := by decide
  have hdescent : baseEnd_3981 < baseStart_3981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4006 : List Nat := [10]
def baseStart_4006 : Nat := 118140960795 + 4006 * 2 ^ 59
def prefixEnd_4006 : Nat := 4983230072969 + 3 ^ 40 * 4006 * 2
def baseEnd_4006 : Nat := 285372702137541045781

theorem tailTrace_4006 : CollatzResearch.WordTrace tailWord_4006 prefixEnd_4006 285372702137541045781 := by
  unfold tailWord_4006
  simp only [CollatzResearch.WordTrace]
  refine ⟨285372702137541045781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 10 97407215662947343626581 285372702137541045781)
  ·
    rfl

theorem cell_4006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_4006 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_4006 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_4006 prefixEnd_4006 := by
    exact prefixLift 4006
  have htrace : WordTrace (prefixWord ++ tailWord_4006) baseStart_4006 baseEnd_4006 := by
    simpa [prefixWord, tailWord_4006, baseEnd_4006] using wordTrace_append hprefix tailTrace_4006
  have hstable : (prefixWord ++ tailWord_4006).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4006).length < 2 ^ (prefixWord ++ tailWord_4006).sum := by decide
  have hdescent : baseEnd_4006 < baseStart_4006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4010 : List Nat := [3, 1, 8]
def baseStart_4010 : Nat := 118140960795 + 4010 * 2 ^ 59
def prefixEnd_4010 : Nat := 4983230072969 + 3 ^ 40 * 4010 * 2
def baseEnd_4010 : Nat := 642729706698909808237

theorem tailTrace_4010 : CollatzResearch.WordTrace tailWord_4010 prefixEnd_4010 642729706698909808237 := by
  unfold tailWord_4010
  simp only [CollatzResearch.WordTrace]
  refine ⟨36564178869982424646371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97504476986619799056989 36564178869982424646371)
  ·
    refine ⟨54846268304973636969557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36564178869982424646371 54846268304973636969557)
    ·
      refine ⟨642729706698909808237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 54846268304973636969557 642729706698909808237)
      ·
        rfl

theorem cell_4010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_4010 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_4010 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_4010 prefixEnd_4010 := by
    exact prefixLift 4010
  have htrace : WordTrace (prefixWord ++ tailWord_4010) baseStart_4010 baseEnd_4010 := by
    simpa [prefixWord, tailWord_4010, baseEnd_4010] using wordTrace_append hprefix tailTrace_4010
  have hstable : (prefixWord ++ tailWord_4010).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4010).length < 2 ^ (prefixWord ++ tailWord_4010).sum := by decide
  have hdescent : baseEnd_4010 < baseStart_4010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4022 : List Nat := [5, 1, 4, 2]
def baseStart_4022 : Nat := 118140960795 + 4022 * 2 ^ 59
def prefixEnd_4022 : Nat := 4983230072969 + 3 ^ 40 * 4022 * 2
def baseEnd_4022 : Nat := 1933959262101711521779

theorem tailTrace_4022 : CollatzResearch.WordTrace tailWord_4022 prefixEnd_4022 1933959262101711521779 := by
  unfold tailWord_4022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9168399464778484251395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97796260957637165348213 9168399464778484251395)
  ·
    refine ⟨13752599197167726377093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9168399464778484251395 13752599197167726377093)
    ·
      refine ⟨2578612349468948695705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13752599197167726377093 2578612349468948695705)
      ·
        refine ⟨1933959262101711521779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2578612349468948695705 1933959262101711521779)
        ·
          rfl

theorem cell_4022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_4022 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_4022 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_4022 prefixEnd_4022 := by
    exact prefixLift 4022
  have htrace : WordTrace (prefixWord ++ tailWord_4022) baseStart_4022 baseEnd_4022 := by
    simpa [prefixWord, tailWord_4022, baseEnd_4022] using wordTrace_append hprefix tailTrace_4022
  have hstable : (prefixWord ++ tailWord_4022).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4022).length < 2 ^ (prefixWord ++ tailWord_4022).sum := by decide
  have hdescent : baseEnd_4022 < baseStart_4022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034 : List Nat := [3, 5, 3]
def baseStart_4034 : Nat := 118140960795 + 4034 * 2 ^ 59
def prefixEnd_4034 : Nat := 4983230072969 + 3 ^ 40 * 4034 * 2
def baseEnd_4034 : Nat := 1293152936071129079231

theorem tailTrace_4034 : CollatzResearch.WordTrace tailWord_4034 prefixEnd_4034 1293152936071129079231 := by
  unfold tailWord_4034
  simp only [CollatzResearch.WordTrace]
  refine ⟨36783016848245449364789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98088044928654531639437 36783016848245449364789)
  ·
    refine ⟨3448407829523010877949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36783016848245449364789 3448407829523010877949)
    ·
      refine ⟨1293152936071129079231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3448407829523010877949 1293152936071129079231)
      ·
        rfl

theorem cell_4034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_4034 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_4034 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_4034 prefixEnd_4034 := by
    exact prefixLift 4034
  have htrace : WordTrace (prefixWord ++ tailWord_4034) baseStart_4034 baseEnd_4034 := by
    simpa [prefixWord, tailWord_4034, baseEnd_4034] using wordTrace_append hprefix tailTrace_4034
  have hstable : (prefixWord ++ tailWord_4034).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034).length < 2 ^ (prefixWord ++ tailWord_4034).sum := by decide
  have hdescent : baseEnd_4034 < baseStart_4034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036 : List Nat := [2, 3, 3, 4]
def baseStart_4036 : Nat := 118140960795 + 4036 * 2 ^ 59
def prefixEnd_4036 : Nat := 4983230072969 + 3 ^ 40 * 4036 * 2
def baseEnd_4036 : Nat := 1940691094440857301691

theorem tailTrace_4036 : CollatzResearch.WordTrace tailWord_4036 prefixEnd_4036 1940691094440857301691 := by
  unfold tailWord_4036
  simp only [CollatzResearch.WordTrace]
  refine ⟨73602506692868069515981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98136675590490759354641 73602506692868069515981)
  ·
    refine ⟨27600940009825526068493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73602506692868069515981 27600940009825526068493)
    ·
      refine ⟨10350352503684572275685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27600940009825526068493 10350352503684572275685)
      ·
        refine ⟨1940691094440857301691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10350352503684572275685 1940691094440857301691)
        ·
          rfl

theorem cell_4036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_4036 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_4036 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_4036 prefixEnd_4036 := by
    exact prefixLift 4036
  have htrace : WordTrace (prefixWord ++ tailWord_4036) baseStart_4036 baseEnd_4036 := by
    simpa [prefixWord, tailWord_4036, baseEnd_4036] using wordTrace_append hprefix tailTrace_4036
  have hstable : (prefixWord ++ tailWord_4036).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036).length < 2 ^ (prefixWord ++ tailWord_4036).sum := by decide
  have hdescent : baseEnd_4036 < baseStart_4036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062 : List Nat := [4, 5]
def baseStart_4062 : Nat := 118140960795 + 4062 * 2 ^ 59
def prefixEnd_4062 : Nat := 4983230072969 + 3 ^ 40 * 4062 * 2
def baseEnd_4062 : Nat := 1736171616697764603263

theorem tailTrace_4062 : CollatzResearch.WordTrace tailWord_4062 prefixEnd_4062 1736171616697764603263 := by
  unfold tailWord_4062
  simp only [CollatzResearch.WordTrace]
  refine ⟨18519163911442822434805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98768874194361719652293 18519163911442822434805)
  ·
    refine ⟨1736171616697764603263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18519163911442822434805 1736171616697764603263)
    ·
      rfl

theorem cell_4062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_4062 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_4062 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_4062 prefixEnd_4062 := by
    exact prefixLift 4062
  have htrace : WordTrace (prefixWord ++ tailWord_4062) baseStart_4062 baseEnd_4062 := by
    simpa [prefixWord, tailWord_4062, baseEnd_4062] using wordTrace_append hprefix tailTrace_4062
  have hstable : (prefixWord ++ tailWord_4062).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062).length < 2 ^ (prefixWord ++ tailWord_4062).sum := by decide
  have hdescent : baseEnd_4062 < baseStart_4062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069 : List Nat := [1, 3, 1, 7]
def baseStart_4069 : Nat := 118140960795 + 4069 * 2 ^ 59
def prefixEnd_4069 : Nat := 4983230072969 + 3 ^ 40 * 4069 * 2
def baseEnd_4069 : Nat := 1956558984954558068627

theorem tailTrace_4069 : CollatzResearch.WordTrace tailWord_4069 prefixEnd_4069 1956558984954558068627 := by
  unfold tailWord_4069
  simp only [CollatzResearch.WordTrace]
  refine ⟨148408622266182774983261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98939081510788516655507 148408622266182774983261)
  ·
    refine ⟨55653233349818540618723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148408622266182774983261 55653233349818540618723)
    ·
      refine ⟨83479850024727810928085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55653233349818540618723 83479850024727810928085)
      ·
        refine ⟨1956558984954558068627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 83479850024727810928085 1956558984954558068627)
        ·
          rfl

theorem cell_4069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_4069 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_4069 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_4069 prefixEnd_4069 := by
    exact prefixLift 4069
  have htrace : WordTrace (prefixWord ++ tailWord_4069) baseStart_4069 baseEnd_4069 := by
    simpa [prefixWord, tailWord_4069, baseEnd_4069] using wordTrace_append hprefix tailTrace_4069
  have hstable : (prefixWord ++ tailWord_4069).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069).length < 2 ^ (prefixWord ++ tailWord_4069).sum := by decide
  have hdescent : baseEnd_4069 < baseStart_4069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070 : List Nat := [7]
def baseStart_4070 : Nat := 118140960795 + 4070 * 2 ^ 59
def prefixEnd_4070 : Nat := 4983230072969 + 3 ^ 40 * 4070 * 2
def baseEnd_4070 : Nat := 2319454613477499152651

theorem tailTrace_4070 : CollatzResearch.WordTrace tailWord_4070 prefixEnd_4070 2319454613477499152651 := by
  unfold tailWord_4070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2319454613477499152651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 7 98963396841706630513109 2319454613477499152651)
  ·
    rfl

theorem cell_4070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_4070 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_4070 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_4070 prefixEnd_4070 := by
    exact prefixLift 4070
  have htrace : WordTrace (prefixWord ++ tailWord_4070) baseStart_4070 baseEnd_4070 := by
    simpa [prefixWord, tailWord_4070, baseEnd_4070] using wordTrace_append hprefix tailTrace_4070
  have hstable : (prefixWord ++ tailWord_4070).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070).length < 2 ^ (prefixWord ++ tailWord_4070).sum := by decide
  have hdescent : baseEnd_4070 < baseStart_4070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082 : List Nat := [3, 2, 1, 6]
def baseStart_4082 : Nat := 118140960795 + 4082 * 2 ^ 59
def prefixEnd_4082 : Nat := 4983230072969 + 3 ^ 40 * 4082 * 2
def baseEnd_4082 : Nat := 1962809972126622007117

theorem tailTrace_4082 : CollatzResearch.WordTrace tailWord_4082 prefixEnd_4082 1962809972126622007117 := by
  unfold tailWord_4082
  simp only [CollatzResearch.WordTrace]
  refine ⟨37220692804771498801625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99255180812723996804333 37220692804771498801625)
  ·
    refine ⟨27915519603578624101219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37220692804771498801625 27915519603578624101219)
    ·
      refine ⟨41873279405367936151829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27915519603578624101219 41873279405367936151829)
      ·
        refine ⟨1962809972126622007117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41873279405367936151829 1962809972126622007117)
        ·
          rfl

theorem cell_4082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_4082 + u * 2 ^ 71) = endpoint ∧
      endpoint < baseStart_4082 + u * 2 ^ 71 := by
  have hprefix : WordTrace prefixWord baseStart_4082 prefixEnd_4082 := by
    exact prefixLift 4082
  have htrace : WordTrace (prefixWord ++ tailWord_4082) baseStart_4082 baseEnd_4082 := by
    simpa [prefixWord, tailWord_4082, baseEnd_4082] using wordTrace_append hprefix tailTrace_4082
  have hstable : (prefixWord ++ tailWord_4082).sum < 71 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082).length < 2 ^ (prefixWord ++ tailWord_4082).sum := by decide
  have hdescent : baseEnd_4082 < baseStart_4082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan12

#print axioms V185TrunkScan12.cell_18_ordinary_descent
