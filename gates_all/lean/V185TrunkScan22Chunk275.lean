import V185TrunkScan22Chunk274

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2451895 : List Nat := [1, 1, 3, 1, 3, 4, 3, 2, 1, 3]
def baseStart_2451895 : Nat := 118140960795 + 2451895 * 2 ^ 59
def prefixEnd_2451895 : Nat := 4983230072969 + 3 ^ 40 * 2451895 * 2
def baseEnd_2451895 : Nat := 839333766237193122157631

theorem tailTrace_2451895 : CollatzResearch.WordTrace tailWord_2451895 prefixEnd_2451895 839333766237193122157631 := by
  unfold tailWord_2451895
  simp only [CollatzResearch.WordTrace]
  refine ⟨89427957452210640172693139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59618638301473760115128759 89427957452210640172693139)
  ·
    refine ⟨134141936178315960259039709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89427957452210640172693139 134141936178315960259039709)
    ·
      refine ⟨50303226066868485097139891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134141936178315960259039709 50303226066868485097139891)
      ·
        refine ⟨75454839100302727645709837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50303226066868485097139891 75454839100302727645709837)
        ·
          refine ⟨28295564662613522867141189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75454839100302727645709837 28295564662613522867141189)
          ·
            refine ⟨5305418374240035537588973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28295564662613522867141189 5305418374240035537588973)
            ·
              refine ⟨1989531890340013326595865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5305418374240035537588973 1989531890340013326595865)
              ·
                refine ⟨1492148917755009994946899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1989531890340013326595865 1492148917755009994946899)
                ·
                  refine ⟨2238223376632514992420349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492148917755009994946899 2238223376632514992420349)
                  ·
                    refine ⟨839333766237193122157631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2238223376632514992420349 839333766237193122157631)
                    ·
                      rfl

theorem cell22_2451895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_2451895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451895 prefixEnd_2451895 := by exact prefixLift 2451895
  have htrace : WordTrace (prefixWord ++ tailWord_2451895) baseStart_2451895 baseEnd_2451895 := by
    simpa [prefixWord, tailWord_2451895, baseEnd_2451895] using wordTrace_append hprefix tailTrace_2451895
  have hstable : (prefixWord ++ tailWord_2451895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451895).length < 2 ^ (prefixWord ++ tailWord_2451895).sum := by decide
  have hdescent : baseEnd_2451895 < baseStart_2451895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451904 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 3, 4]
def baseStart_2451904 : Nat := 118140960795 + 2451904 * 2 ^ 59
def prefixEnd_2451904 : Nat := 4983230072969 + 3 ^ 40 * 2451904 * 2
def baseEnd_2451904 : Nat := 839336847121120098682603

theorem tailTrace_2451904 : CollatzResearch.WordTrace tailWord_2451904 prefixEnd_2451904 839336847121120098682603 := by
  unfold tailWord_2451904
  simp only [CollatzResearch.WordTrace]
  refine ⟨44714142854589017354885383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59618857139452023139847177 44714142854589017354885383)
  ·
    refine ⟨67071214281883526032328075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44714142854589017354885383 67071214281883526032328075)
    ·
      refine ⟨100606821422825289048492113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67071214281883526032328075 100606821422825289048492113)
      ·
        refine ⟨75455116067118966786369085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100606821422825289048492113 75455116067118966786369085)
        ·
          refine ⟨28295668525169612544888407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75455116067118966786369085 28295668525169612544888407)
          ·
            refine ⟨42443502787754418817332611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28295668525169612544888407 42443502787754418817332611)
            ·
              refine ⟨63665254181631628225998917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42443502787754418817332611 63665254181631628225998917)
              ·
                refine ⟨11937235159055930292374797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63665254181631628225998917 11937235159055930292374797)
                ·
                  refine ⟨4476463184645973859640549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11937235159055930292374797 4476463184645973859640549)
                  ·
                    refine ⟨839336847121120098682603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4476463184645973859640549 839336847121120098682603)
                    ·
                      rfl

theorem cell22_2451904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_2451904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451904 prefixEnd_2451904 := by exact prefixLift 2451904
  have htrace : WordTrace (prefixWord ++ tailWord_2451904) baseStart_2451904 baseEnd_2451904 := by
    simpa [prefixWord, tailWord_2451904, baseEnd_2451904] using wordTrace_append hprefix tailTrace_2451904
  have hstable : (prefixWord ++ tailWord_2451904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451904).length < 2 ^ (prefixWord ++ tailWord_2451904).sum := by decide
  have hdescent : baseEnd_2451904 < baseStart_2451904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451908 : List Nat := [2, 3, 3, 2, 2, 1, 1, 3, 5]
def baseStart_2451908 : Nat := 118140960795 + 2451908 * 2 ^ 59
def prefixEnd_2451908 : Nat := 4983230072969 + 3 ^ 40 * 2451908 * 2
def baseEnd_2451908 : Nat := 279779405467621807194197

theorem tailTrace_2451908 : CollatzResearch.WordTrace tailWord_2451908 prefixEnd_2451908 279779405467621807194197 := by
  unfold tailWord_2451908
  simp only [CollatzResearch.WordTrace]
  refine ⟨44714215800581771696458189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59618954400775695595277585 44714215800581771696458189)
  ·
    refine ⟨16767830925218164386171821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44714215800581771696458189 16767830925218164386171821)
    ·
      refine ⟨6287936596956811644814433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16767830925218164386171821 6287936596956811644814433)
      ·
        refine ⟨4715952447717608733610825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6287936596956811644814433 4715952447717608733610825)
        ·
          refine ⟨3536964335788206550208119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4715952447717608733610825 3536964335788206550208119)
          ·
            refine ⟨5305446503682309825312179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3536964335788206550208119 5305446503682309825312179)
            ·
              refine ⟨7958169755523464737968269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5305446503682309825312179 7958169755523464737968269)
              ·
                refine ⟨2984313658321299276738101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7958169755523464737968269 2984313658321299276738101)
                ·
                  refine ⟨279779405467621807194197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2984313658321299276738101 279779405467621807194197)
                  ·
                    rfl

theorem cell22_2451908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_2451908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451908 prefixEnd_2451908 := by exact prefixLift 2451908
  have htrace : WordTrace (prefixWord ++ tailWord_2451908) baseStart_2451908 baseEnd_2451908 := by
    simpa [prefixWord, tailWord_2451908, baseEnd_2451908] using wordTrace_append hprefix tailTrace_2451908
  have hstable : (prefixWord ++ tailWord_2451908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451908).length < 2 ^ (prefixWord ++ tailWord_2451908).sum := by decide
  have hdescent : baseEnd_2451908 < baseStart_2451908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451936 : List Nat := [2, 1, 1, 3, 1, 1, 4, 5, 4]
def baseStart_2451936 : Nat := 118140960795 + 2451936 * 2 ^ 59
def prefixEnd_2451936 : Nat := 4983230072969 + 3 ^ 40 * 2451936 * 2
def baseEnd_2451936 : Nat := 279782600458360893960835

theorem tailTrace_2451936 : CollatzResearch.WordTrace tailWord_2451936 prefixEnd_2451936 279782600458360893960835 := by
  unfold tailWord_2451936
  simp only [CollatzResearch.WordTrace]
  refine ⟨44714726422531052087467831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59619635230041402783290441 44714726422531052087467831)
  ·
    refine ⟨67072089633796578131201747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44714726422531052087467831 67072089633796578131201747)
    ·
      refine ⟨100608134450694867196802621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67072089633796578131201747 100608134450694867196802621)
      ·
        refine ⟨37728050419010575198800983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100608134450694867196802621 37728050419010575198800983)
        ·
          refine ⟨56592075628515862798201475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37728050419010575198800983 56592075628515862798201475)
          ·
            refine ⟨84888113442773794197302213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56592075628515862798201475 84888113442773794197302213)
            ·
              refine ⟨15916521270520086411994165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84888113442773794197302213 15916521270520086411994165)
              ·
                refine ⟨1492173869111258101124453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15916521270520086411994165 1492173869111258101124453)
                ·
                  refine ⟨279782600458360893960835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1492173869111258101124453 279782600458360893960835)
                  ·
                    rfl

theorem cell22_2451936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 4].length) (baseStart_2451936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2451936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2451936 prefixEnd_2451936 := by exact prefixLift 2451936
  have htrace : WordTrace (prefixWord ++ tailWord_2451936) baseStart_2451936 baseEnd_2451936 := by
    simpa [prefixWord, tailWord_2451936, baseEnd_2451936] using wordTrace_append hprefix tailTrace_2451936
  have hstable : (prefixWord ++ tailWord_2451936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451936).length < 2 ^ (prefixWord ++ tailWord_2451936).sum := by decide
  have hdescent : baseEnd_2451936 < baseStart_2451936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452120 : List Nat := [2, 1, 2, 4, 1, 1, 4, 2, 2, 3]
def baseStart_2452120 : Nat := 118140960795 + 2452120 * 2 ^ 59
def prefixEnd_2452120 : Nat := 4983230072969 + 3 ^ 40 * 2452120 * 2
def baseEnd_2452120 : Nat := 839410788335367535281941

theorem tailTrace_2452120 : CollatzResearch.WordTrace tailWord_2452120 prefixEnd_2452120 839410788335367535281941 := by
  unfold tailWord_2452120
  simp only [CollatzResearch.WordTrace]
  refine ⟨44718081938197751799816907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59624109250930335733089209 44718081938197751799816907)
  ·
    refine ⟨67077122907296627699725361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44718081938197751799816907 67077122907296627699725361)
    ·
      refine ⟨50307842180472470774794021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67077122907296627699725361 50307842180472470774794021)
      ·
        refine ⟨9432720408838588270273879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50307842180472470774794021 9432720408838588270273879)
        ·
          refine ⟨14149080613257882405410819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9432720408838588270273879 14149080613257882405410819)
          ·
            refine ⟨21223620919886823608116229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14149080613257882405410819 21223620919886823608116229)
            ·
              refine ⟨3979428922478779426521793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21223620919886823608116229 3979428922478779426521793)
              ·
                refine ⟨2984571691859084569891345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3979428922478779426521793 2984571691859084569891345)
                ·
                  refine ⟨2238428768894313427418509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2984571691859084569891345 2238428768894313427418509)
                  ·
                    refine ⟨839410788335367535281941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2238428768894313427418509 839410788335367535281941)
                    ·
                      rfl

theorem cell22_2452120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_2452120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2452120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2452120 prefixEnd_2452120 := by exact prefixLift 2452120
  have htrace : WordTrace (prefixWord ++ tailWord_2452120) baseStart_2452120 baseEnd_2452120 := by
    simpa [prefixWord, tailWord_2452120, baseEnd_2452120] using wordTrace_append hprefix tailTrace_2452120
  have hstable : (prefixWord ++ tailWord_2452120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452120).length < 2 ^ (prefixWord ++ tailWord_2452120).sum := by decide
  have hdescent : baseEnd_2452120 < baseStart_2452120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452122 : List Nat := [3, 1, 1, 6, 1, 1, 1, 4, 4]
def baseStart_2452122 : Nat := 118140960795 + 2452122 * 2 ^ 59
def prefixEnd_2452122 : Nat := 4983230072969 + 3 ^ 40 * 2452122 * 2
def baseEnd_2452122 : Nat := 279803824325413398910645

theorem tailTrace_2452122 : CollatzResearch.WordTrace tailWord_2452122 prefixEnd_2452122 279803824325413398910645 := by
  unfold tailWord_2452122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22359059205597064485301655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59624157881592171960804413 22359059205597064485301655)
  ·
    refine ⟨33538588808395596727952483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22359059205597064485301655 33538588808395596727952483)
    ·
      refine ⟨50307883212593395091928725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33538588808395596727952483 50307883212593395091928725)
      ·
        refine ⟨2358182025590315394934159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50307883212593395091928725 2358182025590315394934159)
        ·
          refine ⟨3537273038385473092401239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358182025590315394934159 3537273038385473092401239)
          ·
            refine ⟨5305909557578209638601859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3537273038385473092401239 5305909557578209638601859)
            ·
              refine ⟨7958864336367314457902789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5305909557578209638601859 7958864336367314457902789)
              ·
                refine ⟨1492287063068871460856773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7958864336367314457902789 1492287063068871460856773)
                ·
                  refine ⟨279803824325413398910645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1492287063068871460856773 279803824325413398910645)
                  ·
                    rfl

theorem cell22_2452122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_2452122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2452122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2452122 prefixEnd_2452122 := by exact prefixLift 2452122
  have htrace : WordTrace (prefixWord ++ tailWord_2452122) baseStart_2452122 baseEnd_2452122 := by
    simpa [prefixWord, tailWord_2452122, baseEnd_2452122] using wordTrace_append hprefix tailTrace_2452122
  have hstable : (prefixWord ++ tailWord_2452122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452122).length < 2 ^ (prefixWord ++ tailWord_2452122).sum := by decide
  have hdescent : baseEnd_2452122 < baseStart_2452122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452146 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_2452146 : Nat := 118140960795 + 2452146 * 2 ^ 59
def prefixEnd_2452146 : Nat := 4983230072969 + 3 ^ 40 * 2452146 * 2
def baseEnd_2452146 : Nat := 839419688666712134131861

theorem tailTrace_2452146 : CollatzResearch.WordTrace tailWord_2452146 prefixEnd_2452146 839419688666712134131861 := by
  unfold tailWord_2452146
  simp only [CollatzResearch.WordTrace]
  refine ⟨22359278043575327510020073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59624741449534206693386861 22359278043575327510020073)
  ·
    refine ⟨16769458532681495632515055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22359278043575327510020073 16769458532681495632515055)
    ·
      refine ⟨25154187799022243448772583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16769458532681495632515055 25154187799022243448772583)
      ·
        refine ⟨37731281698533365173158875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25154187799022243448772583 37731281698533365173158875)
        ·
          refine ⟨56596922547800047759738313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37731281698533365173158875 56596922547800047759738313)
          ·
            refine ⟨42447691910850035819803735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56596922547800047759738313 42447691910850035819803735)
            ·
              refine ⟨63671537866275053729705603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42447691910850035819803735 63671537866275053729705603)
              ·
                refine ⟨95507306799412580594558405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63671537866275053729705603 95507306799412580594558405)
                ·
                  refine ⟨17907620024889858861479701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95507306799412580594558405 17907620024889858861479701)
                  ·
                    refine ⟨839419688666712134131861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17907620024889858861479701 839419688666712134131861)
                    ·
                      rfl

theorem cell22_2452146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_2452146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2452146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2452146 prefixEnd_2452146 := by exact prefixLift 2452146
  have htrace : WordTrace (prefixWord ++ tailWord_2452146) baseStart_2452146 baseEnd_2452146 := by
    simpa [prefixWord, tailWord_2452146, baseEnd_2452146] using wordTrace_append hprefix tailTrace_2452146
  have hstable : (prefixWord ++ tailWord_2452146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452146).length < 2 ^ (prefixWord ++ tailWord_2452146).sum := by decide
  have hdescent : baseEnd_2452146 < baseStart_2452146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452193 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 2, 5]
def baseStart_2452193 : Nat := 118140960795 + 2452193 * 2 ^ 59
def prefixEnd_2452193 : Nat := 4983230072969 + 3 ^ 40 * 2452193 * 2
def baseEnd_2452193 : Nat := 839435777727219678206717

theorem tailTrace_2452193 : CollatzResearch.WordTrace tailWord_2452193 prefixEnd_2452193 839435777727219678206717 := by
  unfold tailWord_2452193
  simp only [CollatzResearch.WordTrace]
  refine ⟨89438826405131037067041233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59625884270087358044694155 89438826405131037067041233)
  ·
    refine ⟨67079119803848277800280925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89438826405131037067041233 67079119803848277800280925)
    ·
      refine ⟨25154669926443104175105347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67079119803848277800280925 25154669926443104175105347)
      ·
        refine ⟨37732004889664656262658021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25154669926443104175105347 37732004889664656262658021)
        ·
          refine ⟨7074750916812123049248379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37732004889664656262658021 7074750916812123049248379)
          ·
            refine ⟨10612126375218184573872569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7074750916812123049248379 10612126375218184573872569)
            ·
              refine ⟨7959094781413638430404427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10612126375218184573872569 7959094781413638430404427)
              ·
                refine ⟨11938642172120457645606641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7959094781413638430404427 11938642172120457645606641)
                ·
                  refine ⟨8953981629090343234204981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11938642172120457645606641 8953981629090343234204981)
                  ·
                    refine ⟨839435777727219678206717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8953981629090343234204981 839435777727219678206717)
                    ·
                      rfl

theorem cell22_2452193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_2452193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2452193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2452193 prefixEnd_2452193 := by exact prefixLift 2452193
  have htrace : WordTrace (prefixWord ++ tailWord_2452193) baseStart_2452193 baseEnd_2452193 := by
    simpa [prefixWord, tailWord_2452193, baseEnd_2452193] using wordTrace_append hprefix tailTrace_2452193
  have hstable : (prefixWord ++ tailWord_2452193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452193).length < 2 ^ (prefixWord ++ tailWord_2452193).sum := by decide
  have hdescent : baseEnd_2452193 < baseStart_2452193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452285 : List Nat := [1, 4, 1, 4, 3, 9]
def baseStart_2452285 : Nat := 118140960795 + 2452285 * 2 ^ 59
def prefixEnd_2452285 : Nat := 4983230072969 + 3 ^ 40 * 2452285 * 2
def baseEnd_2452285 : Nat := 10363793471695828455635

theorem tailTrace_2452285 : CollatzResearch.WordTrace tailWord_2452285 prefixEnd_2452285 10363793471695828455635 := by
  unfold tailWord_2452285
  simp only [CollatzResearch.WordTrace]
  refine ⟨89442181920797736779390309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59628121280531824519593539 89442181920797736779390309)
  ·
    refine ⟨16770409110149575646135683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89442181920797736779390309 16770409110149575646135683)
    ·
      refine ⟨25155613665224363469203525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16770409110149575646135683 25155613665224363469203525)
      ·
        refine ⟨4716677562229568150475661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25155613665224363469203525 4716677562229568150475661)
        ·
          refine ⟨1768754085836088056428373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4716677562229568150475661 1768754085836088056428373)
          ·
            refine ⟨10363793471695828455635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1768754085836088056428373 10363793471695828455635)
            ·
              rfl

theorem cell22_2452285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 9].length) (baseStart_2452285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2452285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2452285 prefixEnd_2452285 := by exact prefixLift 2452285
  have htrace : WordTrace (prefixWord ++ tailWord_2452285) baseStart_2452285 baseEnd_2452285 := by
    simpa [prefixWord, tailWord_2452285, baseEnd_2452285] using wordTrace_append hprefix tailTrace_2452285
  have hstable : (prefixWord ++ tailWord_2452285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452285).length < 2 ^ (prefixWord ++ tailWord_2452285).sum := by decide
  have hdescent : baseEnd_2452285 < baseStart_2452285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452409 : List Nat := [1, 2, 1, 4, 2, 3, 3, 2, 4]
def baseStart_2452409 : Nat := 118140960795 + 2452409 * 2 ^ 59
def prefixEnd_2452409 : Nat := 4983230072969 + 3 ^ 40 * 2452409 * 2
def baseEnd_2452409 : Nat := 279836572980489038268685

theorem tailTrace_2452409 : CollatzResearch.WordTrace tailWord_2452409 prefixEnd_2452409 279836572980489038268685 := by
  unfold tailWord_2452409
  simp only [CollatzResearch.WordTrace]
  refine ⟨89446704572348505956904281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59631136381565670637936187 89446704572348505956904281)
  ·
    refine ⟨67085028429261379467678211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89446704572348505956904281 67085028429261379467678211)
    ·
      refine ⟨100627542643892069201517317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67085028429261379467678211 100627542643892069201517317)
      ·
        refine ⟨18867664245729762975284497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100627542643892069201517317 18867664245729762975284497)
        ·
          refine ⟨14150748184297322231463373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18867664245729762975284497 14150748184297322231463373)
          ·
            refine ⟨5306530569111495836798765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14150748184297322231463373 5306530569111495836798765)
            ·
              refine ⟨1989948963416810938799537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5306530569111495836798765 1989948963416810938799537)
              ·
                refine ⟨1492461722562608204099653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1989948963416810938799537 1492461722562608204099653)
                ·
                  refine ⟨279836572980489038268685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1492461722562608204099653 279836572980489038268685)
                  ·
                    rfl

theorem cell22_2452409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 4].length) (baseStart_2452409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2452409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2452409 prefixEnd_2452409 := by exact prefixLift 2452409
  have htrace : WordTrace (prefixWord ++ tailWord_2452409) baseStart_2452409 baseEnd_2452409 := by
    simpa [prefixWord, tailWord_2452409, baseEnd_2452409] using wordTrace_append hprefix tailTrace_2452409
  have hstable : (prefixWord ++ tailWord_2452409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452409).length < 2 ^ (prefixWord ++ tailWord_2452409).sum := by decide
  have hdescent : baseEnd_2452409 < baseStart_2452409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452424 : List Nat := [2, 1, 3, 1, 5, 1, 1, 3, 2, 3]
def baseStart_2452424 : Nat := 118140960795 + 2452424 * 2 ^ 59
def prefixEnd_2452424 : Nat := 4983230072969 + 3 ^ 40 * 2452424 * 2
def baseEnd_2452424 : Nat := 839514853748012075681009

theorem tailTrace_2452424 : CollatzResearch.WordTrace tailWord_2452424 prefixEnd_2452424 839514853748012075681009 := by
  unfold tailWord_2452424
  simp only [CollatzResearch.WordTrace]
  refine ⟨44723625833647081759350163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59631501111529442345800217 44723625833647081759350163)
  ·
    refine ⟨67085438750470622639025245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44723625833647081759350163 67085438750470622639025245)
    ·
      refine ⟨25157039531426483489634467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67085438750470622639025245 25157039531426483489634467)
      ·
        refine ⟨37735559297139725234451701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25157039531426483489634467 37735559297139725234451701)
        ·
          refine ⟨3537708684106849240729847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37735559297139725234451701 3537708684106849240729847)
          ·
            refine ⟨5306563026160273861094771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3537708684106849240729847 5306563026160273861094771)
            ·
              refine ⟨7959844539240410791642157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5306563026160273861094771 7959844539240410791642157)
              ·
                refine ⟨2984941702215154046865809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7959844539240410791642157 2984941702215154046865809)
                ·
                  refine ⟨2238706276661365535149357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2984941702215154046865809 2238706276661365535149357)
                  ·
                    refine ⟨839514853748012075681009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2238706276661365535149357 839514853748012075681009)
                    ·
                      rfl

theorem cell22_2452424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_2452424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2452424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2452424 prefixEnd_2452424 := by exact prefixLift 2452424
  have htrace : WordTrace (prefixWord ++ tailWord_2452424) baseStart_2452424 baseEnd_2452424 := by
    simpa [prefixWord, tailWord_2452424, baseEnd_2452424] using wordTrace_append hprefix tailTrace_2452424
  have hstable : (prefixWord ++ tailWord_2452424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452424).length < 2 ^ (prefixWord ++ tailWord_2452424).sum := by decide
  have hdescent : baseEnd_2452424 < baseStart_2452424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452578 : List Nat := [3, 3, 2, 2, 1, 2, 3, 2, 4]
def baseStart_2452578 : Nat := 118140960795 + 2452578 * 2 ^ 59
def prefixEnd_2452578 : Nat := 4983230072969 + 3 ^ 40 * 2452578 * 2
def baseEnd_2452578 : Nat := 279855857031735669110179

theorem tailTrace_2452578 : CollatzResearch.WordTrace tailWord_2452578 prefixEnd_2452578 279855857031735669110179 := by
  unfold tailWord_2452578
  simp only [CollatzResearch.WordTrace]
  refine ⟨22363217127184061954951597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59635245672490831879870925 22363217127184061954951597)
  ·
    refine ⟨8386206422694023233106849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22363217127184061954951597 8386206422694023233106849)
    ·
      refine ⟨6289654817020517424830137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8386206422694023233106849 6289654817020517424830137)
      ·
        refine ⟨4717241112765388068622603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6289654817020517424830137 4717241112765388068622603)
        ·
          refine ⟨7075861669148082102933905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4717241112765388068622603 7075861669148082102933905)
          ·
            refine ⟨5306896251861061577200429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7075861669148082102933905 5306896251861061577200429)
            ·
              refine ⟨1990086094447898091450161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5306896251861061577200429 1990086094447898091450161)
              ·
                refine ⟨1492564570835923568587621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1990086094447898091450161 1492564570835923568587621)
                ·
                  refine ⟨279855857031735669110179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1492564570835923568587621 279855857031735669110179)
                  ·
                    rfl

theorem cell22_2452578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_2452578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2452578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2452578 prefixEnd_2452578 := by exact prefixLift 2452578
  have htrace : WordTrace (prefixWord ++ tailWord_2452578) baseStart_2452578 baseEnd_2452578 := by
    simpa [prefixWord, tailWord_2452578, baseEnd_2452578] using wordTrace_append hprefix tailTrace_2452578
  have hstable : (prefixWord ++ tailWord_2452578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452578).length < 2 ^ (prefixWord ++ tailWord_2452578).sum := by decide
  have hdescent : baseEnd_2452578 < baseStart_2452578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452634 : List Nat := [3, 1, 1, 5, 1, 1, 1, 4, 5]
def baseStart_2452634 : Nat := 118140960795 + 2452634 * 2 ^ 59
def prefixEnd_2452634 : Nat := 4983230072969 + 3 ^ 40 * 2452634 * 2
def baseEnd_2452634 : Nat := 279862247013213842643455

theorem tailTrace_2452634 : CollatzResearch.WordTrace tailWord_2452634 prefixEnd_2452634 279862247013213842643455 := by
  unfold tailWord_2452634
  simp only [CollatzResearch.WordTrace]
  refine ⟨22363727749133342345961239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59636607331022246255896637 22363727749133342345961239)
  ·
    refine ⟨33545591623700013518941859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22363727749133342345961239 33545591623700013518941859)
    ·
      refine ⟨50318387435550020278412789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33545591623700013518941859 50318387435550020278412789)
      ·
        refine ⟨4717348822082814401101199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50318387435550020278412789 4717348822082814401101199)
        ·
          refine ⟨7076023233124221601651799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4717348822082814401101199 7076023233124221601651799)
          ·
            refine ⟨10614034849686332402477699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7076023233124221601651799 10614034849686332402477699)
            ·
              refine ⟨15921052274529498603716549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10614034849686332402477699 15921052274529498603716549)
              ·
                refine ⟨2985197301474280988196853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15921052274529498603716549 2985197301474280988196853)
                ·
                  refine ⟨279862247013213842643455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2985197301474280988196853 279862247013213842643455)
                  ·
                    rfl

theorem cell22_2452634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_2452634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2452634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2452634 prefixEnd_2452634 := by exact prefixLift 2452634
  have htrace : WordTrace (prefixWord ++ tailWord_2452634) baseStart_2452634 baseEnd_2452634 := by
    simpa [prefixWord, tailWord_2452634, baseEnd_2452634] using wordTrace_append hprefix tailTrace_2452634
  have hstable : (prefixWord ++ tailWord_2452634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452634).length < 2 ^ (prefixWord ++ tailWord_2452634).sum := by decide
  have hdescent : baseEnd_2452634 < baseStart_2452634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452685 : List Nat := [1, 6, 2, 2, 1, 2, 1, 2, 5]
def baseStart_2452685 : Nat := 118140960795 + 2452685 * 2 ^ 59
def prefixEnd_2452685 : Nat := 4983230072969 + 3 ^ 40 * 2452685 * 2
def baseEnd_2452685 : Nat := 279868066460631464968403

theorem tailTrace_2452685 : CollatzResearch.WordTrace tailWord_2452685 prefixEnd_2452685 279868066460631464968403 := by
  unfold tailWord_2452685
  simp only [CollatzResearch.WordTrace]
  refine ⟨89456771119348605093951509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59637847412899070062634339 89456771119348605093951509)
  ·
    refine ⟨4193286146219465863778977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89456771119348605093951509 4193286146219465863778977)
    ·
      refine ⟨3144964609664599397834233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4193286146219465863778977 3144964609664599397834233)
      ·
        refine ⟨2358723457248449548375675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3144964609664599397834233 2358723457248449548375675)
        ·
          refine ⟨3538085185872674322563513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358723457248449548375675 3538085185872674322563513)
          ·
            refine ⟨2653563889404505741922635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3538085185872674322563513 2653563889404505741922635)
            ·
              refine ⟨3980345834106758612883953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653563889404505741922635 3980345834106758612883953)
              ·
                refine ⟨2985259375580068959662965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3980345834106758612883953 2985259375580068959662965)
                ·
                  refine ⟨279868066460631464968403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2985259375580068959662965 279868066460631464968403)
                  ·
                    rfl

theorem cell22_2452685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_2452685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2452685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2452685 prefixEnd_2452685 := by exact prefixLift 2452685
  have htrace : WordTrace (prefixWord ++ tailWord_2452685) baseStart_2452685 baseEnd_2452685 := by
    simpa [prefixWord, tailWord_2452685, baseEnd_2452685] using wordTrace_append hprefix tailTrace_2452685
  have hstable : (prefixWord ++ tailWord_2452685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452685).length < 2 ^ (prefixWord ++ tailWord_2452685).sum := by decide
  have hdescent : baseEnd_2452685 < baseStart_2452685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452814 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_2452814 : Nat := 118140960795 + 2452814 * 2 ^ 59
def prefixEnd_2452814 : Nat := 4983230072969 + 3 ^ 40 * 2452814 * 2
def baseEnd_2452814 : Nat := 279882786239393686143271

theorem tailTrace_2452814 : CollatzResearch.WordTrace tailWord_2452814 prefixEnd_2452814 279882786239393686143271 := by
  unfold tailWord_2452814
  simp only [CollatzResearch.WordTrace]
  refine ⟨11182684516985157515674687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59640984090587506750264997 11182684516985157515674687)
  ·
    refine ⟨16774026775477736273512031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11182684516985157515674687 16774026775477736273512031)
    ·
      refine ⟨25161040163216604410268047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16774026775477736273512031 25161040163216604410268047)
      ·
        refine ⟨37741560244824906615402071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25161040163216604410268047 37741560244824906615402071)
        ·
          refine ⟨56612340367237359923103107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37741560244824906615402071 56612340367237359923103107)
          ·
            refine ⟨84918510550856039884654661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56612340367237359923103107 84918510550856039884654661)
            ·
              refine ⟨15922220728285507478372749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84918510550856039884654661 15922220728285507478372749)
              ·
                refine ⟨5970832773107065304389781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15922220728285507478372749 5970832773107065304389781)
                ·
                  refine ⟨279882786239393686143271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5970832773107065304389781 279882786239393686143271)
                  ·
                    rfl

theorem cell22_2452814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_2452814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2452814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2452814 prefixEnd_2452814 := by exact prefixLift 2452814
  have htrace : WordTrace (prefixWord ++ tailWord_2452814) baseStart_2452814 baseEnd_2452814 := by
    simpa [prefixWord, tailWord_2452814, baseEnd_2452814] using wordTrace_append hprefix tailTrace_2452814
  have hstable : (prefixWord ++ tailWord_2452814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452814).length < 2 ^ (prefixWord ++ tailWord_2452814).sum := by decide
  have hdescent : baseEnd_2452814 < baseStart_2452814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452893 : List Nat := [1, 4, 2, 1, 3, 3, 2, 6]
def baseStart_2452893 : Nat := 118140960795 + 2452893 * 2 ^ 59
def prefixEnd_2452893 : Nat := 4983230072969 + 3 ^ 40 * 2452893 * 2
def baseEnd_2452893 : Nat := 93297266892516798411619

theorem tailTrace_2452893 : CollatzResearch.WordTrace tailWord_2452893 prefixEnd_2452893 93297266892516798411619 := by
  unfold tailWord_2452893
  simp only [CollatzResearch.WordTrace]
  refine ⟨89464357502595056617523333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59642905001730037745015555 89464357502595056617523333)
  ·
    refine ⟨16774567031736573115785625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89464357502595056617523333 16774567031736573115785625)
    ·
      refine ⟨12580925273802429836839219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16774567031736573115785625 12580925273802429836839219)
      ·
        refine ⟨18871387910703644755258829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12580925273802429836839219 18871387910703644755258829)
        ·
          refine ⟨7076770466513866783222061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18871387910703644755258829 7076770466513866783222061)
          ·
            refine ⟨2653788924942700043708273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7076770466513866783222061 2653788924942700043708273)
            ·
              refine ⟨1990341693707025032781205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2653788924942700043708273 1990341693707025032781205)
              ·
                refine ⟨93297266892516798411619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1990341693707025032781205 93297266892516798411619)
                ·
                  rfl

theorem cell22_2452893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 6].length) (baseStart_2452893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2452893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2452893 prefixEnd_2452893 := by exact prefixLift 2452893
  have htrace : WordTrace (prefixWord ++ tailWord_2452893) baseStart_2452893 baseEnd_2452893 := by
    simpa [prefixWord, tailWord_2452893, baseEnd_2452893] using wordTrace_append hprefix tailTrace_2452893
  have hstable : (prefixWord ++ tailWord_2452893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452893).length < 2 ^ (prefixWord ++ tailWord_2452893).sum := by decide
  have hdescent : baseEnd_2452893 < baseStart_2452893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452938 : List Nat := [3, 1, 2, 1, 2, 3, 4, 1, 5]
def baseStart_2452938 : Nat := 118140960795 + 2452938 * 2 ^ 59
def prefixEnd_2452938 : Nat := 4983230072969 + 3 ^ 40 * 2452938 * 2
def baseEnd_2452938 : Nat := 279896935484095356109811

theorem tailTrace_2452938 : CollatzResearch.WordTrace tailWord_2452938 prefixEnd_2452938 279896935484095356109811 := by
  unfold tailWord_2452938
  simp only [CollatzResearch.WordTrace]
  refine ⟨22366499696858007325727867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59643999191621352868607645 22366499696858007325727867)
  ·
    refine ⟨33549749545287010988591801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22366499696858007325727867 33549749545287010988591801)
    ·
      refine ⟨25162312158965258241443851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33549749545287010988591801 25162312158965258241443851)
      ·
        refine ⟨37743468238447887362165777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25162312158965258241443851 37743468238447887362165777)
        ·
          refine ⟨28307601178835915521624333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37743468238447887362165777 28307601178835915521624333)
          ·
            refine ⟨10615350442063468320609125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28307601178835915521624333 10615350442063468320609125)
            ·
              refine ⟨1990378207886900310114211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10615350442063468320609125 1990378207886900310114211)
              ·
                refine ⟨2985567311830350465171317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1990378207886900310114211 2985567311830350465171317)
                ·
                  refine ⟨279896935484095356109811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2985567311830350465171317 279896935484095356109811)
                  ·
                    rfl

theorem cell22_2452938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_2452938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2452938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2452938 prefixEnd_2452938 := by exact prefixLift 2452938
  have htrace : WordTrace (prefixWord ++ tailWord_2452938) baseStart_2452938 baseEnd_2452938 := by
    simpa [prefixWord, tailWord_2452938, baseEnd_2452938] using wordTrace_append hprefix tailTrace_2452938
  have hstable : (prefixWord ++ tailWord_2452938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452938).length < 2 ^ (prefixWord ++ tailWord_2452938).sum := by decide
  have hdescent : baseEnd_2452938 < baseStart_2452938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453013 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 2, 4]
def baseStart_2453013 : Nat := 118140960795 + 2453013 * 2 ^ 59
def prefixEnd_2453013 : Nat := 4983230072969 + 3 ^ 40 * 2453013 * 2
def baseEnd_2453013 : Nat := 839716480485010872704203

theorem tailTrace_2453013 : CollatzResearch.WordTrace tailWord_2453013 prefixEnd_2453013 839716480485010872704203 := by
  unfold tailWord_2453013
  simp only [CollatzResearch.WordTrace]
  refine ⟨89468734262160317111891693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59645822841440211407927795 89468734262160317111891693)
  ·
    refine ⟨33550775348310118916959385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89468734262160317111891693 33550775348310118916959385)
    ·
      refine ⟨25163081511232589187719539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33550775348310118916959385 25163081511232589187719539)
      ·
        refine ⟨37744622266848883781579309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25163081511232589187719539 37744622266848883781579309)
        ·
          refine ⟨14154233350068331418092241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37744622266848883781579309 14154233350068331418092241)
          ·
            refine ⟨10615675012551248563569181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14154233350068331418092241 10615675012551248563569181)
            ·
              refine ⟨3980878129706718211338443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10615675012551248563569181 3980878129706718211338443)
              ·
                refine ⟨5971317194560077317007665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980878129706718211338443 5971317194560077317007665)
                ·
                  refine ⟨4478487895920057987755749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5971317194560077317007665 4478487895920057987755749)
                  ·
                    refine ⟨839716480485010872704203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4478487895920057987755749 839716480485010872704203)
                    ·
                      rfl

theorem cell22_2453013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_2453013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453013 prefixEnd_2453013 := by exact prefixLift 2453013
  have htrace : WordTrace (prefixWord ++ tailWord_2453013) baseStart_2453013 baseEnd_2453013 := by
    simpa [prefixWord, tailWord_2453013, baseEnd_2453013] using wordTrace_append hprefix tailTrace_2453013
  have hstable : (prefixWord ++ tailWord_2453013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453013).length < 2 ^ (prefixWord ++ tailWord_2453013).sum := by decide
  have hdescent : baseEnd_2453013 < baseStart_2453013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453043 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 3, 3]
def baseStart_2453043 : Nat := 118140960795 + 2453043 * 2 ^ 59
def prefixEnd_2453043 : Nat := 4983230072969 + 3 ^ 40 * 2453043 * 2
def baseEnd_2453043 : Nat := 839726750098100794454111

theorem tailTrace_2453043 : CollatzResearch.WordTrace tailWord_2453043 prefixEnd_2453043 839726750098100794454111 := by
  unfold tailWord_2453043
  simp only [CollatzResearch.WordTrace]
  refine ⟨89469828452051632235483783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59646552301367754823655855 89469828452051632235483783)
  ·
    refine ⟨134204742678077448353225675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89469828452051632235483783 134204742678077448353225675)
    ·
      refine ⟨201307114017116172529838513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134204742678077448353225675 201307114017116172529838513)
      ·
        refine ⟨150980335512837129397378885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201307114017116172529838513 150980335512837129397378885)
        ·
          refine ⟨28308812908656961762008541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150980335512837129397378885 28308812908656961762008541)
          ·
            refine ⟨10615804840746360660753203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28308812908656961762008541 10615804840746360660753203)
            ·
              refine ⟨15923707261119540991129805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10615804840746360660753203 15923707261119540991129805)
              ·
                refine ⟨5971390222919827871673677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15923707261119540991129805 5971390222919827871673677)
                ·
                  refine ⟨2239271333594935451877629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5971390222919827871673677 2239271333594935451877629)
                  ·
                    refine ⟨839726750098100794454111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2239271333594935451877629 839726750098100794454111)
                    ·
                      rfl

theorem cell22_2453043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 3].length) (baseStart_2453043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453043 prefixEnd_2453043 := by exact prefixLift 2453043
  have htrace : WordTrace (prefixWord ++ tailWord_2453043) baseStart_2453043 baseEnd_2453043 := by
    simpa [prefixWord, tailWord_2453043, baseEnd_2453043] using wordTrace_append hprefix tailTrace_2453043
  have hstable : (prefixWord ++ tailWord_2453043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453043).length < 2 ^ (prefixWord ++ tailWord_2453043).sum := by decide
  have hdescent : baseEnd_2453043 < baseStart_2453043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453146 : List Nat := [3, 1, 1, 17]
def baseStart_2453146 : Nat := 118140960795 + 2453146 * 2 ^ 59
def prefixEnd_2453146 : Nat := 4983230072969 + 3 ^ 40 * 2453146 * 2
def baseEnd_2453146 : Nat := 1151936912349853030355

theorem tailTrace_2453146 : CollatzResearch.WordTrace tailWord_2453146 prefixEnd_2453146 1151936912349853030355 := by
  unfold tailWord_2453146
  simp only [CollatzResearch.WordTrace]
  refine ⟨22368396292669620206620823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59649056780452320550988861 22368396292669620206620823)
  ·
    refine ⟨33552594439004430309931235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22368396292669620206620823 33552594439004430309931235)
    ·
      refine ⟨50328891658506645464896853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33552594439004430309931235 50328891658506645464896853)
      ·
        refine ⟨1151936912349853030355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 50328891658506645464896853 1151936912349853030355)
        ·
          rfl

theorem cell22_2453146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 17].length) (baseStart_2453146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453146 prefixEnd_2453146 := by exact prefixLift 2453146
  have htrace : WordTrace (prefixWord ++ tailWord_2453146) baseStart_2453146 baseEnd_2453146 := by
    simpa [prefixWord, tailWord_2453146, baseEnd_2453146] using wordTrace_append hprefix tailTrace_2453146
  have hstable : (prefixWord ++ tailWord_2453146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453146).length < 2 ^ (prefixWord ++ tailWord_2453146).sum := by decide
  have hdescent : baseEnd_2453146 < baseStart_2453146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453152 : List Nat := [2, 1, 1, 4, 3, 1, 4, 2, 4]
def baseStart_2453152 : Nat := 118140960795 + 2453152 * 2 ^ 59
def prefixEnd_2453152 : Nat := 4983230072969 + 3 ^ 40 * 2453152 * 2
def baseEnd_2453152 : Nat := 279921354341886947826259

theorem tailTrace_2453152 : CollatzResearch.WordTrace tailWord_2453152 prefixEnd_2453152 279921354341886947826259 := by
  unfold tailWord_2453152
  simp only [CollatzResearch.WordTrace]
  refine ⟨44736902004328371925600855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59649202672437829234134473 44736902004328371925600855)
  ·
    refine ⟨67105353006492557888401283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44736902004328371925600855 67105353006492557888401283)
    ·
      refine ⟨100658029509738836832601925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67105353006492557888401283 100658029509738836832601925)
      ·
        refine ⟨18873380533076031906112861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100658029509738836832601925 18873380533076031906112861)
        ·
          refine ⟨7077517699903511964792323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18873380533076031906112861 7077517699903511964792323)
          ·
            refine ⟨10616276549855267947188485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7077517699903511964792323 10616276549855267947188485)
            ·
              refine ⟨1990551853097862740097841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10616276549855267947188485 1990551853097862740097841)
              ·
                refine ⟨1492913889823397055073381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1990551853097862740097841 1492913889823397055073381)
                ·
                  refine ⟨279921354341886947826259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1492913889823397055073381 279921354341886947826259)
                  ·
                    rfl

theorem cell22_2453152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 4].length) (baseStart_2453152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453152 prefixEnd_2453152 := by exact prefixLift 2453152
  have htrace : WordTrace (prefixWord ++ tailWord_2453152) baseStart_2453152 baseEnd_2453152 := by
    simpa [prefixWord, tailWord_2453152, baseEnd_2453152] using wordTrace_append hprefix tailTrace_2453152
  have hstable : (prefixWord ++ tailWord_2453152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453152).length < 2 ^ (prefixWord ++ tailWord_2453152).sum := by decide
  have hdescent : baseEnd_2453152 < baseStart_2453152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453180 : List Nat := [2, 2, 2, 3, 1, 3, 3, 6]
def baseStart_2453180 : Nat := 118140960795 + 2453180 * 2 ^ 59
def prefixEnd_2453180 : Nat := 4983230072969 + 3 ^ 40 * 2453180 * 2
def baseEnd_2453180 : Nat := 93308183110875344864299

theorem tailTrace_2453180 : CollatzResearch.WordTrace tailWord_2453180 prefixEnd_2453180 93308183110875344864299 := by
  unfold tailWord_2453180
  simp only [CollatzResearch.WordTrace]
  refine ⟨44737412626277652316610497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59649883501703536422147329 44737412626277652316610497)
  ·
    refine ⟨33553059469708239237457873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44737412626277652316610497 33553059469708239237457873)
    ·
      refine ⟨25164794602281179428093405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33553059469708239237457873 25164794602281179428093405)
      ·
        refine ⟨9436797975855442285535027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25164794602281179428093405 9436797975855442285535027)
        ·
          refine ⟨14155196963783163428302541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9436797975855442285535027 14155196963783163428302541)
          ·
            refine ⟨5308198861418686285613453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14155196963783163428302541 5308198861418686285613453)
            ·
              refine ⟨1990574573032007357105045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5308198861418686285613453 1990574573032007357105045)
              ·
                refine ⟨93308183110875344864299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1990574573032007357105045 93308183110875344864299)
                ·
                  rfl

theorem cell22_2453180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 6].length) (baseStart_2453180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453180 prefixEnd_2453180 := by exact prefixLift 2453180
  have htrace : WordTrace (prefixWord ++ tailWord_2453180) baseStart_2453180 baseEnd_2453180 := by
    simpa [prefixWord, tailWord_2453180, baseEnd_2453180] using wordTrace_append hprefix tailTrace_2453180
  have hstable : (prefixWord ++ tailWord_2453180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453180).length < 2 ^ (prefixWord ++ tailWord_2453180).sum := by decide
  have hdescent : baseEnd_2453180 < baseStart_2453180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453182 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_2453182 : Nat := 118140960795 + 2453182 * 2 ^ 59
def prefixEnd_2453182 : Nat := 4983230072969 + 3 ^ 40 * 2453182 * 2
def baseEnd_2453182 : Nat := 839774332638750765228685

theorem tailTrace_2453182 : CollatzResearch.WordTrace tailWord_2453182 prefixEnd_2453182 839774332638750765228685 := by
  unfold tailWord_2453182
  simp only [CollatzResearch.WordTrace]
  refine ⟨11184362274818507371849225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59649932132365372649862533 11184362274818507371849225)
  ·
    refine ⟨8388271706113880528886919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11184362274818507371849225 8388271706113880528886919)
    ·
      refine ⟨12582407559170820793330379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8388271706113880528886919 12582407559170820793330379)
      ·
        refine ⟨18873611338756231189995569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12582407559170820793330379 18873611338756231189995569)
        ·
          refine ⟨14155208504067173392496677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18873611338756231189995569 14155208504067173392496677)
          ·
            refine ⟨2654101594512595011093127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14155208504067173392496677 2654101594512595011093127)
            ·
              refine ⟨3981152391768892516639691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2654101594512595011093127 3981152391768892516639691)
              ·
                refine ⟨5971728587653338774959537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3981152391768892516639691 5971728587653338774959537)
                ·
                  refine ⟨4478796440740004081219653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5971728587653338774959537 4478796440740004081219653)
                  ·
                    refine ⟨839774332638750765228685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4478796440740004081219653 839774332638750765228685)
                    ·
                      rfl

theorem cell22_2453182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_2453182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453182 prefixEnd_2453182 := by exact prefixLift 2453182
  have htrace : WordTrace (prefixWord ++ tailWord_2453182) baseStart_2453182 baseEnd_2453182 := by
    simpa [prefixWord, tailWord_2453182, baseEnd_2453182] using wordTrace_append hprefix tailTrace_2453182
  have hstable : (prefixWord ++ tailWord_2453182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453182).length < 2 ^ (prefixWord ++ tailWord_2453182).sum := by decide
  have hdescent : baseEnd_2453182 < baseStart_2453182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453208 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 7]
def baseStart_2453208 : Nat := 118140960795 + 2453208 * 2 ^ 59
def prefixEnd_2453208 : Nat := 4983230072969 + 3 ^ 40 * 2453208 * 2
def baseEnd_2453208 : Nat := 279927744323365121359535

theorem tailTrace_2453208 : CollatzResearch.WordTrace tailWord_2453208 prefixEnd_2453208 279927744323365121359535 := by
  unfold tailWord_2453208
  simp only [CollatzResearch.WordTrace]
  refine ⟨44737923248226932707620139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59650564330969243610160185 44737923248226932707620139)
  ·
    refine ⟨67106884872340399061430209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44737923248226932707620139 67106884872340399061430209)
    ·
      refine ⟨50330163654255299296072657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67106884872340399061430209 50330163654255299296072657)
      ·
        refine ⟨37747622740691474472054493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50330163654255299296072657 37747622740691474472054493)
        ·
          refine ⟨14155358527759302927020435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37747622740691474472054493 14155358527759302927020435)
          ·
            refine ⟨21233037791638954390530653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14155358527759302927020435 21233037791638954390530653)
            ·
              refine ⟨7962389171864607896448995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21233037791638954390530653 7962389171864607896448995)
              ·
                refine ⟨11943583757796911844673493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7962389171864607896448995 11943583757796911844673493)
                ·
                  refine ⟨279927744323365121359535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11943583757796911844673493 279927744323365121359535)
                  ·
                    rfl

theorem cell22_2453208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 7].length) (baseStart_2453208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453208 prefixEnd_2453208 := by exact prefixLift 2453208
  have htrace : WordTrace (prefixWord ++ tailWord_2453208) baseStart_2453208 baseEnd_2453208 := by
    simpa [prefixWord, tailWord_2453208, baseEnd_2453208] using wordTrace_append hprefix tailTrace_2453208
  have hstable : (prefixWord ++ tailWord_2453208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453208).length < 2 ^ (prefixWord ++ tailWord_2453208).sum := by decide
  have hdescent : baseEnd_2453208 < baseStart_2453208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453283 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 3, 6]
def baseStart_2453283 : Nat := 118140960795 + 2453283 * 2 ^ 59
def prefixEnd_2453283 : Nat := 4983230072969 + 3 ^ 40 * 2453283 * 2
def baseEnd_2453283 : Nat := 839808907002820168453375

theorem tailTrace_2453283 : CollatzResearch.WordTrace tailWord_2453283 prefixEnd_2453283 839808907002820168453375 := by
  unfold tailWord_2453283
  simp only [CollatzResearch.WordTrace]
  refine ⟨89478581971182153224220503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59652387980788102149480335 89478581971182153224220503)
  ·
    refine ⟨134217872956773229836330755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89478581971182153224220503 134217872956773229836330755)
    ·
      refine ⟨201326809435159844754496133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134217872956773229836330755 201326809435159844754496133)
      ·
        refine ⟨37748776769092470891468025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201326809435159844754496133 37748776769092470891468025)
        ·
          refine ⟨28311582576819353168601019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37748776769092470891468025 28311582576819353168601019)
          ·
            refine ⟨42467373865229029752901529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28311582576819353168601019 42467373865229029752901529)
            ·
              refine ⟨31850530398921772314676147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42467373865229029752901529 31850530398921772314676147)
              ·
                refine ⟨47775795598382658472014221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31850530398921772314676147 47775795598382658472014221)
                ·
                  refine ⟨17915923349393496927005333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47775795598382658472014221 17915923349393496927005333)
                  ·
                    refine ⟨839808907002820168453375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17915923349393496927005333 839808907002820168453375)
                    ·
                      rfl

theorem cell22_2453283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 6].length) (baseStart_2453283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453283 prefixEnd_2453283 := by exact prefixLift 2453283
  have htrace : WordTrace (prefixWord ++ tailWord_2453283) baseStart_2453283 baseEnd_2453283 := by
    simpa [prefixWord, tailWord_2453283, baseEnd_2453283] using wordTrace_append hprefix tailTrace_2453283
  have hstable : (prefixWord ++ tailWord_2453283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453283).length < 2 ^ (prefixWord ++ tailWord_2453283).sum := by decide
  have hdescent : baseEnd_2453283 < baseStart_2453283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453302 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2453302 : Nat := 118140960795 + 2453302 * 2 ^ 59
def prefixEnd_2453302 : Nat := 4983230072969 + 3 ^ 40 * 2453302 * 2
def baseEnd_2453302 : Nat := 839815411091110452228317

theorem tailTrace_2453302 : CollatzResearch.WordTrace tailWord_2453302 prefixEnd_2453302 839815411091110452228317 := by
  unfold tailWord_2453302
  simp only [CollatzResearch.WordTrace]
  refine ⟨5592454684882082466822635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59652849972075546312774773 5592454684882082466822635)
  ·
    refine ⟨8388682027323123700233953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5592454684882082466822635 8388682027323123700233953)
    ·
      refine ⟨6291511520492342775175465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8388682027323123700233953 6291511520492342775175465)
      ·
        refine ⟨4718633640369257081381599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6291511520492342775175465 4718633640369257081381599)
        ·
          refine ⟨7077950460553885622072399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4718633640369257081381599 7077950460553885622072399)
          ·
            refine ⟨10616925690830828433108599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7077950460553885622072399 10616925690830828433108599)
            ·
              refine ⟨15925388536246242649662899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10616925690830828433108599 15925388536246242649662899)
              ·
                refine ⟨23888082804369363974494349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15925388536246242649662899 23888082804369363974494349)
                ·
                  refine ⟨8958031051638511490435381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23888082804369363974494349 8958031051638511490435381)
                  ·
                    refine ⟨839815411091110452228317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8958031051638511490435381 839815411091110452228317)
                    ·
                      rfl

theorem cell22_2453302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2453302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453302 prefixEnd_2453302 := by exact prefixLift 2453302
  have htrace : WordTrace (prefixWord ++ tailWord_2453302) baseStart_2453302 baseEnd_2453302 := by
    simpa [prefixWord, tailWord_2453302, baseEnd_2453302] using wordTrace_append hprefix tailTrace_2453302
  have hstable : (prefixWord ++ tailWord_2453302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453302).length < 2 ^ (prefixWord ++ tailWord_2453302).sum := by decide
  have hdescent : baseEnd_2453302 < baseStart_2453302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453332 : List Nat := [2, 4, 1, 1, 3, 3, 1, 7]
def baseStart_2453332 : Nat := 118140960795 + 2453332 * 2 ^ 59
def prefixEnd_2453332 : Nat := 4983230072969 + 3 ^ 40 * 2453332 * 2
def baseEnd_2453332 : Nat := 93313964522688930442025

theorem tailTrace_2453332 : CollatzResearch.WordTrace tailWord_2453332 prefixEnd_2453332 93313964522688930442025 := by
  unfold tailWord_2453332
  simp only [CollatzResearch.WordTrace]
  refine ⟨44740184574002317296377125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59653579432003089728502833 44740184574002317296377125)
  ·
    refine ⟨8388784607625434493070711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44740184574002317296377125 8388784607625434493070711)
    ·
      refine ⟨12583176911438151739606067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8388784607625434493070711 12583176911438151739606067)
      ·
        refine ⟨18874765367157227609409101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12583176911438151739606067 18874765367157227609409101)
        ·
          refine ⟨7078037012683960353528413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18874765367157227609409101 7078037012683960353528413)
          ·
            refine ⟨2654263879756485132573155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7078037012683960353528413 2654263879756485132573155)
            ·
              refine ⟨3981395819634727698859733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2654263879756485132573155 3981395819634727698859733)
              ·
                refine ⟨93313964522688930442025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3981395819634727698859733 93313964522688930442025)
                ·
                  rfl

theorem cell22_2453332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 7].length) (baseStart_2453332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453332 prefixEnd_2453332 := by exact prefixLift 2453332
  have htrace : WordTrace (prefixWord ++ tailWord_2453332) baseStart_2453332 baseEnd_2453332 := by
    simpa [prefixWord, tailWord_2453332, baseEnd_2453332] using wordTrace_append hprefix tailTrace_2453332
  have hstable : (prefixWord ++ tailWord_2453332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453332).length < 2 ^ (prefixWord ++ tailWord_2453332).sum := by decide
  have hdescent : baseEnd_2453332 < baseStart_2453332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453435 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 4, 4]
def baseStart_2453435 : Nat := 118140960795 + 2453435 * 2 ^ 59
def prefixEnd_2453435 : Nat := 4983230072969 + 3 ^ 40 * 2453435 * 2
def baseEnd_2453435 : Nat := 839860939709142438652909

theorem tailTrace_2453435 : CollatzResearch.WordTrace tailWord_2453435 prefixEnd_2453435 839860939709142438652909 := by
  unfold tailWord_2453435
  simp only [CollatzResearch.WordTrace]
  refine ⟨89484125866631483183753759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59656083911087655455835839 89484125866631483183753759)
  ·
    refine ⟨134226188799947224775630639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89484125866631483183753759 134226188799947224775630639)
    ·
      refine ⟨201339283199920837163445959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134226188799947224775630639 201339283199920837163445959)
      ·
        refine ⟨302008924799881255745168939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201339283199920837163445959 302008924799881255745168939)
        ·
          refine ⟨453013387199821883617753409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302008924799881255745168939 453013387199821883617753409)
          ·
            refine ⟨339760040399866412713315057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453013387199821883617753409 339760040399866412713315057)
            ·
              refine ⟨254820030299899809534986293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339760040399866412713315057 254820030299899809534986293)
              ·
                refine ⟨23889377840615607143904965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 254820030299899809534986293 23889377840615607143904965)
                ·
                  refine ⟨4479258345115426339482181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23889377840615607143904965 4479258345115426339482181)
                  ·
                    refine ⟨839860939709142438652909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4479258345115426339482181 839860939709142438652909)
                    ·
                      rfl

theorem cell22_2453435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 4].length) (baseStart_2453435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453435 prefixEnd_2453435 := by exact prefixLift 2453435
  have htrace : WordTrace (prefixWord ++ tailWord_2453435) baseStart_2453435 baseEnd_2453435 := by
    simpa [prefixWord, tailWord_2453435, baseEnd_2453435] using wordTrace_append hprefix tailTrace_2453435
  have hstable : (prefixWord ++ tailWord_2453435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453435).length < 2 ^ (prefixWord ++ tailWord_2453435).sum := by decide
  have hdescent : baseEnd_2453435 < baseStart_2453435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453439 : List Nat := [1, 1, 2, 2, 2, 1, 7, 2, 4]
def baseStart_2453439 : Nat := 118140960795 + 2453439 * 2 ^ 59
def prefixEnd_2453439 : Nat := 4983230072969 + 3 ^ 40 * 2453439 * 2
def baseEnd_2453439 : Nat := 279954102996962587184299

theorem tailTrace_2453439 : CollatzResearch.WordTrace tailWord_2453439 prefixEnd_2453439 279954102996962587184299 := by
  unfold tailWord_2453439
  simp only [CollatzResearch.WordTrace]
  refine ⟨89484271758616991866899371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59656181172411327911266247 89484271758616991866899371)
  ·
    refine ⟨134226407637925487800349057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89484271758616991866899371 134226407637925487800349057)
    ·
      refine ⟨100669805728444115850261793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134226407637925487800349057 100669805728444115850261793)
      ·
        refine ⟨75502354296333086887696345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100669805728444115850261793 75502354296333086887696345)
        ·
          refine ⟨56626765722249815165772259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75502354296333086887696345 56626765722249815165772259)
          ·
            refine ⟨84940148583374722748658389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56626765722249815165772259 84940148583374722748658389)
            ·
              refine ⟨1990784732422845064421681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 84940148583374722748658389 1990784732422845064421681)
              ·
                refine ⟨1493088549317133798316261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1990784732422845064421681 1493088549317133798316261)
                ·
                  refine ⟨279954102996962587184299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1493088549317133798316261 279954102996962587184299)
                  ·
                    rfl

theorem cell22_2453439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 4].length) (baseStart_2453439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453439 prefixEnd_2453439 := by exact prefixLift 2453439
  have htrace : WordTrace (prefixWord ++ tailWord_2453439) baseStart_2453439 baseEnd_2453439 := by
    simpa [prefixWord, tailWord_2453439, baseEnd_2453439] using wordTrace_append hprefix tailTrace_2453439
  have hstable : (prefixWord ++ tailWord_2453439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453439).length < 2 ^ (prefixWord ++ tailWord_2453439).sum := by decide
  have hdescent : baseEnd_2453439 < baseStart_2453439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453450 : List Nat := [3, 1, 2, 1, 2, 1, 3, 9]
def baseStart_2453450 : Nat := 118140960795 + 2453450 * 2 ^ 59
def prefixEnd_2453450 : Nat := 4983230072969 + 3 ^ 40 * 2453450 * 2
def baseEnd_2453450 : Nat := 93318452723965266614207

theorem tailTrace_2453450 : CollatzResearch.WordTrace tailWord_2453450 prefixEnd_2453450 93318452723965266614207 := by
  unfold tailWord_2453450
  simp only [CollatzResearch.WordTrace]
  refine ⟨22371168240394285186387451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59656448641051427163699869 22371168240394285186387451)
  ·
    refine ⟨33556752360591427779581177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22371168240394285186387451 33556752360591427779581177)
    ·
      refine ⟨25167564270443570834685883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33556752360591427779581177 25167564270443570834685883)
      ·
        refine ⟨37751346405665356252028825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25167564270443570834685883 37751346405665356252028825)
        ·
          refine ⟨28313509804249017189021619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37751346405665356252028825 28313509804249017189021619)
          ·
            refine ⟨42470264706373525783532429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28313509804249017189021619 42470264706373525783532429)
            ·
              refine ⟨15926349264890072168824661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42470264706373525783532429 15926349264890072168824661)
              ·
                refine ⟨93318452723965266614207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15926349264890072168824661 93318452723965266614207)
                ·
                  rfl

theorem cell22_2453450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_2453450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453450 prefixEnd_2453450 := by exact prefixLift 2453450
  have htrace : WordTrace (prefixWord ++ tailWord_2453450) baseStart_2453450 baseEnd_2453450 := by
    simpa [prefixWord, tailWord_2453450, baseEnd_2453450] using wordTrace_append hprefix tailTrace_2453450
  have hstable : (prefixWord ++ tailWord_2453450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453450).length < 2 ^ (prefixWord ++ tailWord_2453450).sum := by decide
  have hdescent : baseEnd_2453450 < baseStart_2453450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453454 : List Nat := [4, 1, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_2453454 : Nat := 118140960795 + 2453454 * 2 ^ 59
def prefixEnd_2453454 : Nat := 4983230072969 + 3 ^ 40 * 2453454 * 2
def baseEnd_2453454 : Nat := 839867443797432722427851

theorem tailTrace_2453454 : CollatzResearch.WordTrace tailWord_2453454 prefixEnd_2453454 839867443797432722427851 := by
  unfold tailWord_2453454
  simp only [CollatzResearch.WordTrace]
  refine ⟨11185602356695331178586927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59656545902375099619130277 11185602356695331178586927)
  ·
    refine ⟨16778403535042996767880391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11185602356695331178586927 16778403535042996767880391)
    ·
      refine ⟨25167605302564495151820587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16778403535042996767880391 25167605302564495151820587)
      ·
        refine ⟨37751407953846742727730881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25167605302564495151820587 37751407953846742727730881)
        ·
          refine ⟨28313555965385057045798161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37751407953846742727730881 28313555965385057045798161)
          ·
            refine ⟨21235166974038792784348621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28313555965385057045798161 21235166974038792784348621)
            ·
              refine ⟨7963187615264547294130733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21235166974038792784348621 7963187615264547294130733)
              ·
                refine ⟨2986195355724205235299025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7963187615264547294130733 2986195355724205235299025)
                ·
                  refine ⟨2239646516793153926474269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2986195355724205235299025 2239646516793153926474269)
                  ·
                    refine ⟨839867443797432722427851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2239646516793153926474269 839867443797432722427851)
                    ·
                      rfl

theorem cell22_2453454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_2453454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453454 prefixEnd_2453454 := by exact prefixLift 2453454
  have htrace : WordTrace (prefixWord ++ tailWord_2453454) baseStart_2453454 baseEnd_2453454 := by
    simpa [prefixWord, tailWord_2453454, baseEnd_2453454] using wordTrace_append hprefix tailTrace_2453454
  have hstable : (prefixWord ++ tailWord_2453454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453454).length < 2 ^ (prefixWord ++ tailWord_2453454).sum := by decide
  have hdescent : baseEnd_2453454 < baseStart_2453454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453458 : List Nat := [3, 2, 2, 3, 3, 1, 1, 2, 1, 4]
def baseStart_2453458 : Nat := 118140960795 + 2453458 * 2 ^ 59
def prefixEnd_2453458 : Nat := 4983230072969 + 3 ^ 40 * 2453458 * 2
def baseEnd_2453458 : Nat := 839868813079178045327839

theorem tailTrace_2453458 : CollatzResearch.WordTrace tailWord_2453458 prefixEnd_2453458 839868813079178045327839 := by
  unfold tailWord_2453458
  simp only [CollatzResearch.WordTrace]
  refine ⟨22371241186387039527960257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59656643163698772074560685 22371241186387039527960257)
  ·
    refine ⟨16778430889790279645970193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22371241186387039527960257 16778430889790279645970193)
    ·
      refine ⟨12583823167342709734477645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16778430889790279645970193 12583823167342709734477645)
      ·
        refine ⟨4718933687753516150429117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12583823167342709734477645 4718933687753516150429117)
        ·
          refine ⟨1769600132907568556410919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4718933687753516150429117 1769600132907568556410919)
          ·
            refine ⟨2654400199361352834616379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769600132907568556410919 2654400199361352834616379)
            ·
              refine ⟨3981600299042029251924569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2654400199361352834616379 3981600299042029251924569)
              ·
                refine ⟨2986200224281521938943427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3981600299042029251924569 2986200224281521938943427)
                ·
                  refine ⟨4479300336422282908415141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986200224281521938943427 4479300336422282908415141)
                  ·
                    refine ⟨839868813079178045327839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4479300336422282908415141 839868813079178045327839)
                    ·
                      rfl

theorem cell22_2453458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_2453458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453458 prefixEnd_2453458 := by exact prefixLift 2453458
  have htrace : WordTrace (prefixWord ++ tailWord_2453458) baseStart_2453458 baseEnd_2453458 := by
    simpa [prefixWord, tailWord_2453458, baseEnd_2453458] using wordTrace_append hprefix tailTrace_2453458
  have hstable : (prefixWord ++ tailWord_2453458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453458).length < 2 ^ (prefixWord ++ tailWord_2453458).sum := by decide
  have hdescent : baseEnd_2453458 < baseStart_2453458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453512 : List Nat := [2, 1, 3, 2, 1, 2, 1, 5, 5]
def baseStart_2453512 : Nat := 118140960795 + 2453512 * 2 ^ 59
def prefixEnd_2453512 : Nat := 4983230072969 + 3 ^ 40 * 2453512 * 2
def baseEnd_2453512 : Nat := 279962432794246634825891

theorem tailTrace_2453512 : CollatzResearch.WordTrace tailWord_2453512 prefixEnd_2453512 279962432794246634825891 := by
  unfold tailWord_2453512
  simp only [CollatzResearch.WordTrace]
  refine ⟨44743467143676262667153395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59657956191568350222871193 44743467143676262667153395)
  ·
    refine ⟨67115200715514394000730093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44743467143676262667153395 67115200715514394000730093)
    ·
      refine ⟨25168200268317897750273785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67115200715514394000730093 25168200268317897750273785)
      ·
        refine ⟨18876150201238423312705339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25168200268317897750273785 18876150201238423312705339)
        ·
          refine ⟨28314225301857634969058009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18876150201238423312705339 28314225301857634969058009)
          ·
            refine ⟨21235668976393226226793507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28314225301857634969058009 21235668976393226226793507)
            ·
              refine ⟨31853503464589839340190261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21235668976393226226793507 31853503464589839340190261)
              ·
                refine ⟨2986265949805297438142837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31853503464589839340190261 2986265949805297438142837)
                ·
                  refine ⟨279962432794246634825891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2986265949805297438142837 279962432794246634825891)
                  ·
                    rfl

theorem cell22_2453512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 5].length) (baseStart_2453512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453512 prefixEnd_2453512 := by exact prefixLift 2453512
  have htrace : WordTrace (prefixWord ++ tailWord_2453512) baseStart_2453512 baseEnd_2453512 := by
    simpa [prefixWord, tailWord_2453512, baseEnd_2453512] using wordTrace_append hprefix tailTrace_2453512
  have hstable : (prefixWord ++ tailWord_2453512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453512).length < 2 ^ (prefixWord ++ tailWord_2453512).sum := by decide
  have hdescent : baseEnd_2453512 < baseStart_2453512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453533 : List Nat := [1, 4, 2, 2, 2, 2, 2, 3, 1, 3]
def baseStart_2453533 : Nat := 118140960795 + 2453533 * 2 ^ 59
def prefixEnd_2453533 : Nat := 4983230072969 + 3 ^ 40 * 2453533 * 2
def baseEnd_2453533 : Nat := 839894487111902849702609

theorem tailTrace_2453533 : CollatzResearch.WordTrace tailWord_2453533 prefixEnd_2453533 839894487111902849702609 := by
  unfold tailWord_2453533
  simp only [CollatzResearch.WordTrace]
  refine ⟨89487700220276445920821253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59658466813517630613880835 89487700220276445920821253)
  ·
    refine ⟨16778943791301833610153985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89487700220276445920821253 16778943791301833610153985)
    ·
      refine ⟨12584207843476375207615489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16778943791301833610153985 12584207843476375207615489)
      ·
        refine ⟨9438155882607281405711617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12584207843476375207615489 9438155882607281405711617)
        ·
          refine ⟨7078616911955461054283713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9438155882607281405711617 7078616911955461054283713)
          ·
            refine ⟨5308962683966595790712785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7078616911955461054283713 5308962683966595790712785)
            ·
              refine ⟨3981722012974946843034589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5308962683966595790712785 3981722012974946843034589)
              ·
                refine ⟨1493145754865605066137971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3981722012974946843034589 1493145754865605066137971)
                ·
                  refine ⟨2239718632298407599206957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493145754865605066137971 2239718632298407599206957)
                  ·
                    refine ⟨839894487111902849702609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2239718632298407599206957 839894487111902849702609)
                    ·
                      rfl

theorem cell22_2453533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_2453533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453533 prefixEnd_2453533 := by exact prefixLift 2453533
  have htrace : WordTrace (prefixWord ++ tailWord_2453533) baseStart_2453533 baseEnd_2453533 := by
    simpa [prefixWord, tailWord_2453533, baseEnd_2453533] using wordTrace_append hprefix tailTrace_2453533
  have hstable : (prefixWord ++ tailWord_2453533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453533).length < 2 ^ (prefixWord ++ tailWord_2453533).sum := by decide
  have hdescent : baseEnd_2453533 < baseStart_2453533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453546 : List Nat := [3, 1, 4, 1, 2, 3, 1, 2, 5]
def baseStart_2453546 : Nat := 118140960795 + 2453546 * 2 ^ 59
def prefixEnd_2453546 : Nat := 4983230072969 + 3 ^ 40 * 2453546 * 2
def baseEnd_2453546 : Nat := 279966312425858383042523

theorem tailTrace_2453546 : CollatzResearch.WordTrace tailWord_2453546 prefixEnd_2453546 279966312425858383042523 := by
  unfold tailWord_2453546
  simp only [CollatzResearch.WordTrace]
  refine ⟨22372043592307337285261123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59658782912819566094029661 22372043592307337285261123)
  ·
    refine ⟨33558065388461005927891685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22372043592307337285261123 33558065388461005927891685)
    ·
      refine ⟨6292137260336438611479691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33558065388461005927891685 6292137260336438611479691)
      ·
        refine ⟨9438205890504657917219537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6292137260336438611479691 9438205890504657917219537)
        ·
          refine ⟨7078654417878493437914653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9438205890504657917219537 7078654417878493437914653)
          ·
            refine ⟨2654495406704435039217995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7078654417878493437914653 2654495406704435039217995)
            ·
              refine ⟨3981743110056652558826993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2654495406704435039217995 3981743110056652558826993)
              ·
                refine ⟨2986307332542489419120245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3981743110056652558826993 2986307332542489419120245)
                ·
                  refine ⟨279966312425858383042523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2986307332542489419120245 279966312425858383042523)
                  ·
                    rfl

theorem cell22_2453546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_2453546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453546 prefixEnd_2453546 := by exact prefixLift 2453546
  have htrace : WordTrace (prefixWord ++ tailWord_2453546) baseStart_2453546 baseEnd_2453546 := by
    simpa [prefixWord, tailWord_2453546, baseEnd_2453546] using wordTrace_append hprefix tailTrace_2453546
  have hstable : (prefixWord ++ tailWord_2453546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453546).length < 2 ^ (prefixWord ++ tailWord_2453546).sum := by decide
  have hdescent : baseEnd_2453546 < baseStart_2453546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453557 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 6]
def baseStart_2453557 : Nat := 118140960795 + 2453557 * 2 ^ 59
def prefixEnd_2453557 : Nat := 4983230072969 + 3 ^ 40 * 2453557 * 2
def baseEnd_2453557 : Nat := 279967567600791595700845

theorem tailTrace_2453557 : CollatzResearch.WordTrace tailWord_2453557 prefixEnd_2453557 279967567600791595700845 := by
  unfold tailWord_2453557
  simp only [CollatzResearch.WordTrace]
  refine ⟨89488575572189498019694925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59659050381459665346463283 89488575572189498019694925)
  ·
    refine ⟨33558215839571061757385597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89488575572189498019694925 33558215839571061757385597)
    ·
      refine ⟨12584330939839148159019599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33558215839571061757385597 12584330939839148159019599)
      ·
        refine ⟨18876496409758722238529399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12584330939839148159019599 18876496409758722238529399)
        ·
          refine ⟨28314744614638083357794099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18876496409758722238529399 28314744614638083357794099)
          ·
            refine ⟨42472116921957125036691149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28314744614638083357794099 42472116921957125036691149)
            ·
              refine ⟨15927043845733921888759181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42472116921957125036691149 15927043845733921888759181)
              ·
                refine ⟨5972641442150220708284693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15927043845733921888759181 5972641442150220708284693)
                ·
                  refine ⟨279967567600791595700845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5972641442150220708284693 279967567600791595700845)
                  ·
                    rfl

theorem cell22_2453557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_2453557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453557 prefixEnd_2453557 := by exact prefixLift 2453557
  have htrace : WordTrace (prefixWord ++ tailWord_2453557) baseStart_2453557 baseEnd_2453557 := by
    simpa [prefixWord, tailWord_2453557, baseEnd_2453557] using wordTrace_append hprefix tailTrace_2453557
  have hstable : (prefixWord ++ tailWord_2453557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453557).length < 2 ^ (prefixWord ++ tailWord_2453557).sum := by decide
  have hdescent : baseEnd_2453557 < baseStart_2453557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453589 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 4, 3]
def baseStart_2453589 : Nat := 118140960795 + 2453589 * 2 ^ 59
def prefixEnd_2453589 : Nat := 4983230072969 + 3 ^ 40 * 2453589 * 2
def baseEnd_2453589 : Nat := 839913657056337370302437

theorem tailTrace_2453589 : CollatzResearch.WordTrace tailWord_2453589 prefixEnd_2453589 839913657056337370302437 := by
  unfold tailWord_2453589
  simp only [CollatzResearch.WordTrace]
  refine ⟨89489742708073567484859821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59659828472049044989906547 89489742708073567484859821)
  ·
    refine ⟨33558653515527587806822433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89489742708073567484859821 33558653515527587806822433)
    ·
      refine ⟨25168990136645690855116825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33558653515527587806822433 25168990136645690855116825)
      ·
        refine ⟨18876742602484268141337619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25168990136645690855116825 18876742602484268141337619)
        ·
          refine ⟨28315113903726402212006429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18876742602484268141337619 28315113903726402212006429)
          ·
            refine ⟨10618167713897400829502411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28315113903726402212006429 10618167713897400829502411)
            ·
              refine ⟨15927251570846101244253617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10618167713897400829502411 15927251570846101244253617)
              ·
                refine ⟨11945438678134575933190213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15927251570846101244253617 11945438678134575933190213)
                ·
                  refine ⟨2239769752150232987473165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11945438678134575933190213 2239769752150232987473165)
                  ·
                    refine ⟨839913657056337370302437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2239769752150232987473165 839913657056337370302437)
                    ·
                      rfl

theorem cell22_2453589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_2453589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453589 prefixEnd_2453589 := by exact prefixLift 2453589
  have htrace : WordTrace (prefixWord ++ tailWord_2453589) baseStart_2453589 baseEnd_2453589 := by
    simpa [prefixWord, tailWord_2453589, baseEnd_2453589] using wordTrace_append hprefix tailTrace_2453589
  have hstable : (prefixWord ++ tailWord_2453589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453589).length < 2 ^ (prefixWord ++ tailWord_2453589).sum := by decide
  have hdescent : baseEnd_2453589 < baseStart_2453589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453623 : List Nat := [1, 1, 3, 1, 1, 7, 2, 1, 2, 3]
def baseStart_2453623 : Nat := 118140960795 + 2453623 * 2 ^ 59
def prefixEnd_2453623 : Nat := 4983230072969 + 3 ^ 40 * 2453623 * 2
def baseEnd_2453623 : Nat := 839925295951172614952333

theorem tailTrace_2453623 : CollatzResearch.WordTrace tailWord_2453623 prefixEnd_2453623 839925295951172614952333 := by
  unfold tailWord_2453623
  simp only [CollatzResearch.WordTrace]
  refine ⟨89490982789950391291597523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59660655193300260861065015 89490982789950391291597523)
  ·
    refine ⟨134236474184925586937396285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89490982789950391291597523 134236474184925586937396285)
    ·
      refine ⟨50338677819347095101523607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134236474184925586937396285 50338677819347095101523607)
      ·
        refine ⟨75508016729020642652285411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50338677819347095101523607 75508016729020642652285411)
        ·
          refine ⟨113262025093530963978428117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75508016729020642652285411 113262025093530963978428117)
          ·
            refine ⟨2654578713129631968244409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 113262025093530963978428117 2654578713129631968244409)
            ·
              refine ⟨1990934034847223976183307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2654578713129631968244409 1990934034847223976183307)
              ·
                refine ⟨2986401052270835964274961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1990934034847223976183307 2986401052270835964274961)
                ·
                  refine ⟨2239800789203126973206221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2986401052270835964274961 2239800789203126973206221)
                  ·
                    refine ⟨839925295951172614952333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2239800789203126973206221 839925295951172614952333)
                    ·
                      rfl

theorem cell22_2453623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_2453623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453623 prefixEnd_2453623 := by exact prefixLift 2453623
  have htrace : WordTrace (prefixWord ++ tailWord_2453623) baseStart_2453623 baseEnd_2453623 := by
    simpa [prefixWord, tailWord_2453623, baseEnd_2453623] using wordTrace_append hprefix tailTrace_2453623
  have hstable : (prefixWord ++ tailWord_2453623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453623).length < 2 ^ (prefixWord ++ tailWord_2453623).sum := by decide
  have hdescent : baseEnd_2453623 < baseStart_2453623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453651 : List Nat := [1, 1, 1, 2, 1, 2, 3, 7, 1, 3]
def baseStart_2453651 : Nat := 118140960795 + 2453651 * 2 ^ 59
def prefixEnd_2453651 : Nat := 4983230072969 + 3 ^ 40 * 2453651 * 2
def baseEnd_2453651 : Nat := 839934880923389875252247

theorem tailTrace_2453651 : CollatzResearch.WordTrace tailWord_2453651 prefixEnd_2453651 839934880923389875252247 := by
  unfold tailWord_2453651
  simp only [CollatzResearch.WordTrace]
  refine ⟨89492004033848952073616807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59661336022565968049077871 89492004033848952073616807)
  ·
    refine ⟨134238006050773428110425211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89492004033848952073616807 134238006050773428110425211)
    ·
      refine ⟨201357009076160142165637817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134238006050773428110425211 201357009076160142165637817)
      ·
        refine ⟨151017756807120106624228363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201357009076160142165637817 151017756807120106624228363)
        ·
          refine ⟨226526635210680159936342545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151017756807120106624228363 226526635210680159936342545)
          ·
            refine ⟨169894976408010119952256909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226526635210680159936342545 169894976408010119952256909)
            ·
              refine ⟨63710616153003794982096341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169894976408010119952256909 63710616153003794982096341)
              ·
                refine ⟨1493217566086026444892883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 63710616153003794982096341 1493217566086026444892883)
                ·
                  refine ⟨2239826349129039667339325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493217566086026444892883 2239826349129039667339325)
                  ·
                    refine ⟨839934880923389875252247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2239826349129039667339325 839934880923389875252247)
                    ·
                      rfl

theorem cell22_2453651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 1, 3].length) (baseStart_2453651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453651 prefixEnd_2453651 := by exact prefixLift 2453651
  have htrace : WordTrace (prefixWord ++ tailWord_2453651) baseStart_2453651 baseEnd_2453651 := by
    simpa [prefixWord, tailWord_2453651, baseEnd_2453651] using wordTrace_append hprefix tailTrace_2453651
  have hstable : (prefixWord ++ tailWord_2453651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453651).length < 2 ^ (prefixWord ++ tailWord_2453651).sum := by decide
  have hdescent : baseEnd_2453651 < baseStart_2453651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453664 : List Nat := [2, 1, 1, 4, 2, 2, 1, 4, 5]
def baseStart_2453664 : Nat := 118140960795 + 2453664 * 2 ^ 59
def prefixEnd_2453664 : Nat := 4983230072969 + 3 ^ 40 * 2453664 * 2
def baseEnd_2453664 : Nat := 279979777029687391559069

theorem tailTrace_2453664 : CollatzResearch.WordTrace tailWord_2453664 prefixEnd_2453664 279979777029687391559069 := by
  unfold tailWord_2453664
  simp only [CollatzResearch.WordTrace]
  refine ⟨44746239091400927646920023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59661652121867903529226697 44746239091400927646920023)
  ·
    refine ⟨67119358637101391470380035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44746239091400927646920023 67119358637101391470380035)
    ·
      refine ⟨100679037955652087205570053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67119358637101391470380035 100679037955652087205570053)
      ·
        refine ⟨18877319616684766351044385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100679037955652087205570053 18877319616684766351044385)
        ·
          refine ⟨14157989712513574763283289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18877319616684766351044385 14157989712513574763283289)
          ·
            refine ⟨10618492284385181072462467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14157989712513574763283289 10618492284385181072462467)
            ·
              refine ⟨15927738426577771608693701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10618492284385181072462467 15927738426577771608693701)
              ·
                refine ⟨2986450954983332176630069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15927738426577771608693701 2986450954983332176630069)
                ·
                  refine ⟨279979777029687391559069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2986450954983332176630069 279979777029687391559069)
                  ·
                    rfl

theorem cell22_2453664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 5].length) (baseStart_2453664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453664 prefixEnd_2453664 := by exact prefixLift 2453664
  have htrace : WordTrace (prefixWord ++ tailWord_2453664) baseStart_2453664 baseEnd_2453664 := by
    simpa [prefixWord, tailWord_2453664, baseEnd_2453664] using wordTrace_append hprefix tailTrace_2453664
  have hstable : (prefixWord ++ tailWord_2453664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453664).length < 2 ^ (prefixWord ++ tailWord_2453664).sum := by decide
  have hdescent : baseEnd_2453664 < baseStart_2453664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453754 : List Nat := [3, 1, 1, 1, 1, 6, 1, 8]
def baseStart_2453754 : Nat := 118140960795 + 2453754 * 2 ^ 59
def prefixEnd_2453754 : Nat := 4983230072969 + 3 ^ 40 * 2453754 * 2
def baseEnd_2453754 : Nat := 93330015547592437769659

theorem tailTrace_2453754 : CollatzResearch.WordTrace tailWord_2453754 prefixEnd_2453754 93330015547592437769659 := by
  unfold tailWord_2453754
  simp only [CollatzResearch.WordTrace]
  refine ⟨22373940188118950166154079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59663840501650533776410877 22373940188118950166154079)
  ·
    refine ⟨33560910282178425249231119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22373940188118950166154079 33560910282178425249231119)
    ·
      refine ⟨50341365423267637873846679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33560910282178425249231119 50341365423267637873846679)
      ·
        refine ⟨75512048134901456810770019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50341365423267637873846679 75512048134901456810770019)
        ·
          refine ⟨113268072202352185216155029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75512048134901456810770019 113268072202352185216155029)
          ·
            refine ⟨5309440884485258682007267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 113268072202352185216155029 5309440884485258682007267)
            ·
              refine ⟨7964161326727888023010901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5309440884485258682007267 7964161326727888023010901)
              ·
                refine ⟨93330015547592437769659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7964161326727888023010901 93330015547592437769659)
                ·
                  rfl

theorem cell22_2453754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_2453754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453754 prefixEnd_2453754 := by exact prefixLift 2453754
  have htrace : WordTrace (prefixWord ++ tailWord_2453754) baseStart_2453754 baseEnd_2453754 := by
    simpa [prefixWord, tailWord_2453754, baseEnd_2453754] using wordTrace_append hprefix tailTrace_2453754
  have hstable : (prefixWord ++ tailWord_2453754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453754).length < 2 ^ (prefixWord ++ tailWord_2453754).sum := by decide
  have hdescent : baseEnd_2453754 < baseStart_2453754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453784 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 2, 6]
def baseStart_2453784 : Nat := 118140960795 + 2453784 * 2 ^ 59
def prefixEnd_2453784 : Nat := 4983230072969 + 3 ^ 40 * 2453784 * 2
def baseEnd_2453784 : Nat := 839980409541421861676839

theorem tailTrace_2453784 : CollatzResearch.WordTrace tailWord_2453784 prefixEnd_2453784 839980409541421861676839 := by
  unfold tailWord_2453784
  simp only [CollatzResearch.WordTrace]
  refine ⟨44748427471183557894104203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59664569961578077192138937 44748427471183557894104203)
  ·
    refine ⟨67122641206775336841156305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44748427471183557894104203 67122641206775336841156305)
    ·
      refine ⟨50341980905081502630867229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67122641206775336841156305 50341980905081502630867229)
      ·
        refine ⟨18878242839405563486575211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50341980905081502630867229 18878242839405563486575211)
        ·
          refine ⟨28317364259108345229862817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18878242839405563486575211 28317364259108345229862817)
          ·
            refine ⟨21238023194331258922397113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28317364259108345229862817 21238023194331258922397113)
            ·
              refine ⟨15928517395748444191797835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21238023194331258922397113 15928517395748444191797835)
              ·
                refine ⟨23892776093622666287696753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15928517395748444191797835 23892776093622666287696753)
                ·
                  refine ⟨17919582070216999715772565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23892776093622666287696753 17919582070216999715772565)
                  ·
                    refine ⟨839980409541421861676839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17919582070216999715772565 839980409541421861676839)
                    ·
                      rfl

theorem cell22_2453784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_2453784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453784 prefixEnd_2453784 := by exact prefixLift 2453784
  have htrace : WordTrace (prefixWord ++ tailWord_2453784) baseStart_2453784 baseEnd_2453784 := by
    simpa [prefixWord, tailWord_2453784, baseEnd_2453784] using wordTrace_append hprefix tailTrace_2453784
  have hstable : (prefixWord ++ tailWord_2453784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453784).length < 2 ^ (prefixWord ++ tailWord_2453784).sum := by decide
  have hdescent : baseEnd_2453784 < baseStart_2453784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453861 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 6]
def baseStart_2453861 : Nat := 118140960795 + 2453861 * 2 ^ 59
def prefixEnd_2453861 : Nat := 4983230072969 + 3 ^ 40 * 2453861 * 2
def baseEnd_2453861 : Nat := 280002256071673109167201

theorem tailTrace_2453861 : CollatzResearch.WordTrace tailWord_2453861 prefixEnd_2453861 280002256071673109167201 := by
  unfold tailWord_2453861
  simp only [CollatzResearch.WordTrace]
  refine ⟨89499663363088157938761437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59666442242058771959174291 89499663363088157938761437)
  ·
    refine ⟨33562373761158059227035539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89499663363088157938761437 33562373761158059227035539)
    ·
      refine ⟨50343560641737088840553309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33562373761158059227035539 50343560641737088840553309)
      ·
        refine ⟨18878835240651408315207491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50343560641737088840553309 18878835240651408315207491)
        ·
          refine ⟨28318252860977112472811237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18878835240651408315207491 28318252860977112472811237)
          ·
            refine ⟨5309672411433208588652107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28318252860977112472811237 5309672411433208588652107)
            ·
              refine ⟨7964508617149812882978161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5309672411433208588652107 7964508617149812882978161)
              ·
                refine ⟨5973381462862359662233621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7964508617149812882978161 5973381462862359662233621)
                ·
                  refine ⟨280002256071673109167201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5973381462862359662233621 280002256071673109167201)
                  ·
                    rfl

theorem cell22_2453861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_2453861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453861 prefixEnd_2453861 := by exact prefixLift 2453861
  have htrace : WordTrace (prefixWord ++ tailWord_2453861) baseStart_2453861 baseEnd_2453861 := by
    simpa [prefixWord, tailWord_2453861, baseEnd_2453861] using wordTrace_append hprefix tailTrace_2453861
  have hstable : (prefixWord ++ tailWord_2453861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453861).length < 2 ^ (prefixWord ++ tailWord_2453861).sum := by decide
  have hdescent : baseEnd_2453861 < baseStart_2453861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453923 : List Nat := [1, 1, 1, 4, 1, 6, 2, 6]
def baseStart_2453923 : Nat := 118140960795 + 2453923 * 2 ^ 59
def prefixEnd_2453923 : Nat := 4983230072969 + 3 ^ 40 * 2453923 * 2
def baseEnd_2453923 : Nat := 93336443564674648050157

theorem tailTrace_2453923 : CollatzResearch.WordTrace tailWord_2453923 prefixEnd_2453923 93336443564674648050157 := by
  unfold tailWord_2453923
  simp only [CollatzResearch.WordTrace]
  refine ⟨89501924688863542527518423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59667949792575695018345615 89501924688863542527518423)
  ·
    refine ⟨134252887033295313791277635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89501924688863542527518423 134252887033295313791277635)
    ·
      refine ⟨201379330549942970686916453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134252887033295313791277635 201379330549942970686916453)
      ·
        refine ⟨37758624478114307003796835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201379330549942970686916453 37758624478114307003796835)
        ·
          refine ⟨56637936717171460505695253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37758624478114307003796835 56637936717171460505695253)
          ·
            refine ⟨2654903283617412211204465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56637936717171460505695253 2654903283617412211204465)
            ·
              refine ⟨1991177462713059158403349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2654903283617412211204465 1991177462713059158403349)
              ·
                refine ⟨93336443564674648050157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1991177462713059158403349 93336443564674648050157)
                ·
                  rfl

theorem cell22_2453923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 6].length) (baseStart_2453923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453923 prefixEnd_2453923 := by exact prefixLift 2453923
  have htrace : WordTrace (prefixWord ++ tailWord_2453923) baseStart_2453923 baseEnd_2453923 := by
    simpa [prefixWord, tailWord_2453923, baseEnd_2453923] using wordTrace_append hprefix tailTrace_2453923
  have hstable : (prefixWord ++ tailWord_2453923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453923).length < 2 ^ (prefixWord ++ tailWord_2453923).sum := by decide
  have hdescent : baseEnd_2453923 < baseStart_2453923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2453966 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_2453966 : Nat := 118140960795 + 2453966 * 2 ^ 59
def prefixEnd_2453966 : Nat := 4983230072969 + 3 ^ 40 * 2453966 * 2
def baseEnd_2453966 : Nat := 840042711860834053626281

theorem tailTrace_2453966 : CollatzResearch.WordTrace tailWord_2453966 prefixEnd_2453966 840042711860834053626281 := by
  unfold tailWord_2453966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11187936628463470108916719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59668995351805173914222501 11187936628463470108916719)
  ·
    refine ⟨16781904942695205163375079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11187936628463470108916719 16781904942695205163375079)
    ·
      refine ⟨25172857414042807745062619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16781904942695205163375079 25172857414042807745062619)
      ·
        refine ⟨37759286121064211617593929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25172857414042807745062619 37759286121064211617593929)
        ·
          refine ⟨28319464590798158713195447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37759286121064211617593929 28319464590798158713195447)
          ·
            refine ⟨42479196886197238069793171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28319464590798158713195447 42479196886197238069793171)
            ·
              refine ⟨63718795329295857104689757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42479196886197238069793171 63718795329295857104689757)
              ·
                refine ⟨23894548248485946414258659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63718795329295857104689757 23894548248485946414258659)
                ·
                  refine ⟨35841822372728919621387989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23894548248485946414258659 35841822372728919621387989)
                  ·
                    refine ⟨840042711860834053626281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35841822372728919621387989 840042711860834053626281)
                    ·
                      rfl

theorem cell22_2453966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_2453966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2453966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2453966 prefixEnd_2453966 := by exact prefixLift 2453966
  have htrace : WordTrace (prefixWord ++ tailWord_2453966) baseStart_2453966 baseEnd_2453966 := by
    simpa [prefixWord, tailWord_2453966, baseEnd_2453966] using wordTrace_append hprefix tailTrace_2453966
  have hstable : (prefixWord ++ tailWord_2453966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2453966).length < 2 ^ (prefixWord ++ tailWord_2453966).sum := by decide
  have hdescent : baseEnd_2453966 < baseStart_2453966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2453966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454028 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_2454028 : Nat := 118140960795 + 2454028 * 2 ^ 59
def prefixEnd_2454028 : Nat := 4983230072969 + 3 ^ 40 * 2454028 * 2
def baseEnd_2454028 : Nat := 840063935727886558576091

theorem tailTrace_2454028 : CollatzResearch.WordTrace tailWord_2454028 prefixEnd_2454028 840063935727886558576091 := by
  unfold tailWord_2454028
  simp only [CollatzResearch.WordTrace]
  refine ⟨44752877176741572730045369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59670502902322096973393825 44752877176741572730045369)
  ·
    refine ⟨33564657882556179547534027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44752877176741572730045369 33564657882556179547534027)
    ·
      refine ⟨50346986823834269321301041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33564657882556179547534027 50346986823834269321301041)
      ·
        refine ⟨37760240117875701990975781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50346986823834269321301041 37760240117875701990975781)
        ·
          refine ⟨7080045022101694123307959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37760240117875701990975781 7080045022101694123307959)
          ·
            refine ⟨10620067533152541184961939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7080045022101694123307959 10620067533152541184961939)
            ·
              refine ⟨15930101299728811777442909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10620067533152541184961939 15930101299728811777442909)
              ·
                refine ⟨5973787987398304416541091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15930101299728811777442909 5973787987398304416541091)
                ·
                  refine ⟨8960681981097456624811637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5973787987398304416541091 8960681981097456624811637)
                  ·
                    refine ⟨840063935727886558576091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8960681981097456624811637 840063935727886558576091)
                    ·
                      rfl

theorem cell22_2454028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_2454028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454028 prefixEnd_2454028 := by exact prefixLift 2454028
  have htrace : WordTrace (prefixWord ++ tailWord_2454028) baseStart_2454028 baseEnd_2454028 := by
    simpa [prefixWord, tailWord_2454028, baseEnd_2454028] using wordTrace_append hprefix tailTrace_2454028
  have hstable : (prefixWord ++ tailWord_2454028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454028).length < 2 ^ (prefixWord ++ tailWord_2454028).sum := by decide
  have hdescent : baseEnd_2454028 < baseStart_2454028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454058 : List Nat := [3, 1, 4, 1, 1, 3, 9]
def baseStart_2454058 : Nat := 118140960795 + 2454058 * 2 ^ 59
def prefixEnd_2454058 : Nat := 4983230072969 + 3 ^ 40 * 2454058 * 2
def baseEnd_2454058 : Nat := 31113859457073202975037

theorem tailTrace_2454058 : CollatzResearch.WordTrace tailWord_2454058 prefixEnd_2454058 31113859457073202975037 := by
  unfold tailWord_2454058
  simp only [CollatzResearch.WordTrace]
  refine ⟨22376712135843615145920707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59671232362249640389121885 22376712135843615145920707)
  ·
    refine ⟨33565068203765422718881061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22376712135843615145920707 33565068203765422718881061)
    ·
      refine ⟨6293450288206016759790199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33565068203765422718881061 6293450288206016759790199)
      ·
        refine ⟨9440175432309025139685299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6293450288206016759790199 9440175432309025139685299)
        ·
          refine ⟨14160263148463537709527949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9440175432309025139685299 14160263148463537709527949)
          ·
            refine ⟨5310098680673826641072981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14160263148463537709527949 5310098680673826641072981)
            ·
              refine ⟨31113859457073202975037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5310098680673826641072981 31113859457073202975037)
              ·
                rfl

theorem cell22_2454058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 9].length) (baseStart_2454058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454058 prefixEnd_2454058 := by exact prefixLift 2454058
  have htrace : WordTrace (prefixWord ++ tailWord_2454058) baseStart_2454058 baseEnd_2454058 := by
    simpa [prefixWord, tailWord_2454058, baseEnd_2454058] using wordTrace_append hprefix tailTrace_2454058
  have hstable : (prefixWord ++ tailWord_2454058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454058).length < 2 ^ (prefixWord ++ tailWord_2454058).sum := by decide
  have hdescent : baseEnd_2454058 < baseStart_2454058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454062 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2454062 : Nat := 118140960795 + 2454062 * 2 ^ 59
def prefixEnd_2454062 : Nat := 4983230072969 + 3 ^ 40 * 2454062 * 2
def baseEnd_2454062 : Nat := 840075574622721803225987

theorem tailTrace_2454062 : CollatzResearch.WordTrace tailWord_2454062 prefixEnd_2454062 840075574622721803225987 := by
  unfold tailWord_2454062
  simp only [CollatzResearch.WordTrace]
  refine ⟨11188374304419996158353555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59671329623573312844552293 11188374304419996158353555)
  ·
    refine ⟨16782561456629994237530333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11188374304419996158353555 16782561456629994237530333)
    ·
      refine ⟨6293460546236247839073875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16782561456629994237530333 6293460546236247839073875)
      ·
        refine ⟨9440190819354371758610813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6293460546236247839073875 9440190819354371758610813)
        ·
          refine ⟨3540071557257889409479055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9440190819354371758610813 3540071557257889409479055)
          ·
            refine ⟨5310107335886834114218583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3540071557257889409479055 5310107335886834114218583)
            ·
              refine ⟨7965161003830251171327875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5310107335886834114218583 7965161003830251171327875)
              ·
                refine ⟨11947741505745376756991813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7965161003830251171327875 11947741505745376756991813)
                ·
                  refine ⟨2240201532327258141935965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11947741505745376756991813 2240201532327258141935965)
                  ·
                    refine ⟨840075574622721803225987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2240201532327258141935965 840075574622721803225987)
                    ·
                      rfl

theorem cell22_2454062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2454062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454062 prefixEnd_2454062 := by exact prefixLift 2454062
  have htrace : WordTrace (prefixWord ++ tailWord_2454062) baseStart_2454062 baseEnd_2454062 := by
    simpa [prefixWord, tailWord_2454062, baseEnd_2454062] using wordTrace_append hprefix tailTrace_2454062
  have hstable : (prefixWord ++ tailWord_2454062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454062).length < 2 ^ (prefixWord ++ tailWord_2454062).sum := by decide
  have hdescent : baseEnd_2454062 < baseStart_2454062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454090 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 3, 3]
def baseStart_2454090 : Nat := 118140960795 + 2454090 * 2 ^ 59
def prefixEnd_2454090 : Nat := 4983230072969 + 3 ^ 40 * 2454090 * 2
def baseEnd_2454090 : Nat := 840085159594939063525901

theorem tailTrace_2454090 : CollatzResearch.WordTrace tailWord_2454090 prefixEnd_2454090 840085159594939063525901 := by
  unfold tailWord_2454090
  simp only [CollatzResearch.WordTrace]
  refine ⟨22377003919814632512211931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59672010452839020032565149 22377003919814632512211931)
  ·
    refine ⟨33565505879721948768317897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22377003919814632512211931 33565505879721948768317897)
    ·
      refine ⟨25174129409791461576238423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33565505879721948768317897 25174129409791461576238423)
      ·
        refine ⟨37761194114687192364357635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25174129409791461576238423 37761194114687192364357635)
        ·
          refine ⟨56641791172030788546536453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37761194114687192364357635 56641791172030788546536453)
          ·
            refine ⟨10620335844755772852475585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56641791172030788546536453 10620335844755772852475585)
            ·
              refine ⟨7965251883566829639356689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10620335844755772852475585 7965251883566829639356689)
              ·
                refine ⟨5973938912675122229517517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7965251883566829639356689 5973938912675122229517517)
                ·
                  refine ⟨2240227092253170836069069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5973938912675122229517517 2240227092253170836069069)
                  ·
                    refine ⟨840085159594939063525901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2240227092253170836069069 840085159594939063525901)
                    ·
                      rfl

theorem cell22_2454090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_2454090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454090 prefixEnd_2454090 := by exact prefixLift 2454090
  have htrace : WordTrace (prefixWord ++ tailWord_2454090) baseStart_2454090 baseEnd_2454090 := by
    simpa [prefixWord, tailWord_2454090, baseEnd_2454090] using wordTrace_append hprefix tailTrace_2454090
  have hstable : (prefixWord ++ tailWord_2454090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454090).length < 2 ^ (prefixWord ++ tailWord_2454090).sum := by decide
  have hdescent : baseEnd_2454090 < baseStart_2454090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454137 : List Nat := [1, 2, 1, 3, 3, 4, 2, 1, 5]
def baseStart_2454137 : Nat := 118140960795 + 2454137 * 2 ^ 59
def prefixEnd_2454137 : Nat := 4983230072969 + 3 ^ 40 * 2454137 * 2
def baseEnd_2454137 : Nat := 280033749551815535866919

theorem tailTrace_2454137 : CollatzResearch.WordTrace tailWord_2454137 prefixEnd_2454137 280033749551815535866919 := by
  unfold tailWord_2454137
  simp only [CollatzResearch.WordTrace]
  refine ⟨89509729910088257075808665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59673153273392171383872443 89509729910088257075808665)
  ·
    refine ⟨67132297432566192806856499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89509729910088257075808665 67132297432566192806856499)
    ·
      refine ⟨100698446148849289210284749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67132297432566192806856499 100698446148849289210284749)
      ·
        refine ⟨37761917305818483453856781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100698446148849289210284749 37761917305818483453856781)
        ·
          refine ⟨14160718989681931295196293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37761917305818483453856781 14160718989681931295196293)
          ·
            refine ⟨2655134810565362117849305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14160718989681931295196293 2655134810565362117849305)
            ·
              refine ⟨1991351107924021588386979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2655134810565362117849305 1991351107924021588386979)
              ·
                refine ⟨2987026661886032382580469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1991351107924021588386979 2987026661886032382580469)
                ·
                  refine ⟨280033749551815535866919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2987026661886032382580469 280033749551815535866919)
                  ·
                    rfl

theorem cell22_2454137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 5].length) (baseStart_2454137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454137 prefixEnd_2454137 := by exact prefixLift 2454137
  have htrace : WordTrace (prefixWord ++ tailWord_2454137) baseStart_2454137 baseEnd_2454137 := by
    simpa [prefixWord, tailWord_2454137, baseEnd_2454137] using wordTrace_append hprefix tailTrace_2454137
  have hstable : (prefixWord ++ tailWord_2454137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454137).length < 2 ^ (prefixWord ++ tailWord_2454137).sum := by decide
  have hdescent : baseEnd_2454137 < baseStart_2454137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454163 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 1, 5]
def baseStart_2454163 : Nat := 118140960795 + 2454163 * 2 ^ 59
def prefixEnd_2454163 : Nat := 4983230072969 + 3 ^ 40 * 2454163 * 2
def baseEnd_2454163 : Nat := 840110148986791206450677

theorem tailTrace_2454163 : CollatzResearch.WordTrace tailWord_2454163 prefixEnd_2454163 840110148986791206450677 := by
  unfold tailWord_2454163
  simp only [CollatzResearch.WordTrace]
  refine ⟨89510678207994063516255143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59673785471996042344170095 89510678207994063516255143)
  ·
    refine ⟨134266017311991095274382715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89510678207994063516255143 134266017311991095274382715)
    ·
      refine ⟨201399025967986642911574073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134266017311991095274382715 201399025967986642911574073)
      ·
        refine ⟨151049269475989982183680555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201399025967986642911574073 151049269475989982183680555)
        ·
          refine ⟨226573904213984973275520833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151049269475989982183680555 226573904213984973275520833)
          ·
            refine ⟨169930428160488729956640625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226573904213984973275520833 169930428160488729956640625)
            ·
              refine ⟨127447821120366547467480469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169930428160488729956640625 127447821120366547467480469)
              ·
                refine ⟨5974116615017181912538147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 127447821120366547467480469 5974116615017181912538147)
                ·
                  refine ⟨8961174922525772868807221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5974116615017181912538147 8961174922525772868807221)
                  ·
                    refine ⟨840110148986791206450677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8961174922525772868807221 840110148986791206450677)
                    ·
                      rfl

theorem cell22_2454163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 5].length) (baseStart_2454163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454163 prefixEnd_2454163 := by exact prefixLift 2454163
  have htrace : WordTrace (prefixWord ++ tailWord_2454163) baseStart_2454163 baseEnd_2454163 := by
    simpa [prefixWord, tailWord_2454163, baseEnd_2454163] using wordTrace_append hprefix tailTrace_2454163
  have hstable : (prefixWord ++ tailWord_2454163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454163).length < 2 ^ (prefixWord ++ tailWord_2454163).sum := by decide
  have hdescent : baseEnd_2454163 < baseStart_2454163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454167 : List Nat := [1, 1, 3, 3, 2, 1, 5, 1, 1, 4]
def baseStart_2454167 : Nat := 118140960795 + 2454167 * 2 ^ 59
def prefixEnd_2454167 : Nat := 4983230072969 + 3 ^ 40 * 2454167 * 2
def baseEnd_2454167 : Nat := 840111518268536529350665

theorem tailTrace_2454167 : CollatzResearch.WordTrace tailWord_2454167 prefixEnd_2454167 840111518268536529350665 := by
  unfold tailWord_2454167
  simp only [CollatzResearch.WordTrace]
  refine ⟨89510824099979572199400755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59673882733319714799600503 89510824099979572199400755)
  ·
    refine ⟨134266236149969358299101133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89510824099979572199400755 134266236149969358299101133)
    ·
      refine ⟨50349838556238509362162925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134266236149969358299101133 50349838556238509362162925)
      ·
        refine ⟨18881189458589441010811097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50349838556238509362162925 18881189458589441010811097)
        ·
          refine ⟨14160892093942080758108323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18881189458589441010811097 14160892093942080758108323)
          ·
            refine ⟨21241338140913121137162485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14160892093942080758108323 21241338140913121137162485)
            ·
              refine ⟨1991375450710605106608983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21241338140913121137162485 1991375450710605106608983)
              ·
                refine ⟨2987063176065907659913475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1991375450710605106608983 2987063176065907659913475)
                ·
                  refine ⟨4480594764098861489870213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2987063176065907659913475 4480594764098861489870213)
                  ·
                    refine ⟨840111518268536529350665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4480594764098861489870213 840111518268536529350665)
                    ·
                      rfl

theorem cell22_2454167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_2454167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454167 prefixEnd_2454167 := by exact prefixLift 2454167
  have htrace : WordTrace (prefixWord ++ tailWord_2454167) baseStart_2454167 baseEnd_2454167 := by
    simpa [prefixWord, tailWord_2454167, baseEnd_2454167] using wordTrace_append hprefix tailTrace_2454167
  have hstable : (prefixWord ++ tailWord_2454167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454167).length < 2 ^ (prefixWord ++ tailWord_2454167).sum := by decide
  have hdescent : baseEnd_2454167 < baseStart_2454167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454197 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 1, 5]
def baseStart_2454197 : Nat := 118140960795 + 2454197 * 2 ^ 59
def prefixEnd_2454197 : Nat := 4983230072969 + 3 ^ 40 * 2454197 * 2
def baseEnd_2454197 : Nat := 840121787881626451100573

theorem tailTrace_2454197 : CollatzResearch.WordTrace tailWord_2454197 prefixEnd_2454197 840121787881626451100573 := by
  unfold tailWord_2454197
  simp only [CollatzResearch.WordTrace]
  refine ⟨89511918289870887322992845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59674612193247258215328563 89511918289870887322992845)
  ·
    refine ⟨33566969358701582746122317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89511918289870887322992845 33566969358701582746122317)
    ·
      refine ⟨12587613509513093529795869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33566969358701582746122317 12587613509513093529795869)
      ·
        refine ⟨4720355066067410073673451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12587613509513093529795869 4720355066067410073673451)
        ·
          refine ⟨7080532599101115110510177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4720355066067410073673451 7080532599101115110510177)
          ·
            refine ⟨5310399449325836332882633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7080532599101115110510177 5310399449325836332882633)
            ·
              refine ⟨3982799586994377249661975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5310399449325836332882633 3982799586994377249661975)
              ·
                refine ⟨5974199380491565874492963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3982799586994377249661975 5974199380491565874492963)
                ·
                  refine ⟨8961299070737348811739445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5974199380491565874492963 8961299070737348811739445)
                  ·
                    refine ⟨840121787881626451100573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8961299070737348811739445 840121787881626451100573)
                    ·
                      rfl

theorem cell22_2454197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_2454197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454197 prefixEnd_2454197 := by exact prefixLift 2454197
  have htrace : WordTrace (prefixWord ++ tailWord_2454197) baseStart_2454197 baseEnd_2454197 := by
    simpa [prefixWord, tailWord_2454197, baseEnd_2454197] using wordTrace_append hprefix tailTrace_2454197
  have hstable : (prefixWord ++ tailWord_2454197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454197).length < 2 ^ (prefixWord ++ tailWord_2454197).sum := by decide
  have hdescent : baseEnd_2454197 < baseStart_2454197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454212 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2454212 : Nat := 118140960795 + 2454212 * 2 ^ 59
def prefixEnd_2454212 : Nat := 4983230072969 + 3 ^ 40 * 2454212 * 2
def baseEnd_2454212 : Nat := 840126922688171411975527

theorem tailTrace_2454212 : CollatzResearch.WordTrace tailWord_2454212 prefixEnd_2454212 840126922688171411975527 := by
  unfold tailWord_2454212
  simp only [CollatzResearch.WordTrace]
  refine ⟨44756232692408272442394445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59674976923211029923192593 44756232692408272442394445)
  ·
    refine ⟨16783587259653102165897917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44756232692408272442394445 16783587259653102165897917)
    ·
      refine ⟨6293845222369913312211719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16783587259653102165897917 6293845222369913312211719)
      ·
        refine ⟨9440767833554869968317579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6293845222369913312211719 9440767833554869968317579)
        ·
          refine ⟨14161151750332304952476369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9440767833554869968317579 14161151750332304952476369)
          ·
            refine ⟨10620863812749228714357277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14161151750332304952476369 10620863812749228714357277)
            ·
              refine ⟨3982823929780960767883979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10620863812749228714357277 3982823929780960767883979)
              ·
                refine ⟨5974235894671441151825969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3982823929780960767883979 5974235894671441151825969)
                ·
                  refine ⟨4480676921003580863869477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5974235894671441151825969 4480676921003580863869477)
                  ·
                    refine ⟨840126922688171411975527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4480676921003580863869477 840126922688171411975527)
                    ·
                      rfl

theorem cell22_2454212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2454212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454212 prefixEnd_2454212 := by exact prefixLift 2454212
  have htrace : WordTrace (prefixWord ++ tailWord_2454212) baseStart_2454212 baseEnd_2454212 := by
    simpa [prefixWord, tailWord_2454212, baseEnd_2454212] using wordTrace_append hprefix tailTrace_2454212
  have hstable : (prefixWord ++ tailWord_2454212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454212).length < 2 ^ (prefixWord ++ tailWord_2454212).sum := by decide
  have hdescent : baseEnd_2454212 < baseStart_2454212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454225 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 5, 3]
def baseStart_2454225 : Nat := 118140960795 + 2454225 * 2 ^ 59
def prefixEnd_2454225 : Nat := 4983230072969 + 3 ^ 40 * 2454225 * 2
def baseEnd_2454225 : Nat := 840131372853843711400487

theorem tailTrace_2454225 : CollatzResearch.WordTrace tailWord_2454225 prefixEnd_2454225 840131372853843711400487 := by
  unfold tailWord_2454225
  simp only [CollatzResearch.WordTrace]
  refine ⟨89512939533769448105012129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59675293022512965403341419 89512939533769448105012129)
  ·
    refine ⟨67134704650327086078759097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89512939533769448105012129 67134704650327086078759097)
    ·
      refine ⟨50351028487745314559069323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67134704650327086078759097 50351028487745314559069323)
      ·
        refine ⟨75526542731617971838603985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50351028487745314559069323 75526542731617971838603985)
        ·
          refine ⟨56644907048713478878952989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75526542731617971838603985 56644907048713478878952989)
          ·
            refine ⟨21241840143267554579607371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56644907048713478878952989 21241840143267554579607371)
            ·
              refine ⟨31862760214901331869411057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21241840143267554579607371 31862760214901331869411057)
              ·
                refine ⟨23897070161175998902058293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31862760214901331869411057 23897070161175998902058293)
                ·
                  refine ⟨2240350327610249897067965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23897070161175998902058293 2240350327610249897067965)
                  ·
                    refine ⟨840131372853843711400487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2240350327610249897067965 840131372853843711400487)
                    ·
                      rfl

theorem cell22_2454225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_2454225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454225 prefixEnd_2454225 := by exact prefixLift 2454225
  have htrace : WordTrace (prefixWord ++ tailWord_2454225) baseStart_2454225 baseEnd_2454225 := by
    simpa [prefixWord, tailWord_2454225, baseEnd_2454225] using wordTrace_append hprefix tailTrace_2454225
  have hstable : (prefixWord ++ tailWord_2454225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454225).length < 2 ^ (prefixWord ++ tailWord_2454225).sum := by decide
  have hdescent : baseEnd_2454225 < baseStart_2454225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454362 : List Nat := [3, 1, 1, 2, 1, 6, 1, 7]
def baseStart_2454362 : Nat := 118140960795 + 2454362 * 2 ^ 59
def prefixEnd_2454362 : Nat := 4983230072969 + 3 ^ 40 * 2454362 * 2
def baseEnd_2454362 : Nat := 93353141194846780080563

theorem tailTrace_2454362 : CollatzResearch.WordTrace tailWord_2454362 prefixEnd_2454362 93353141194846780080563 := by
  unfold tailWord_2454362
  simp only [CollatzResearch.WordTrace]
  refine ⟨22379484083568280125687335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59678624222848747001832893 22379484083568280125687335)
  ·
    refine ⟨33569226125352420188531003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22379484083568280125687335 33569226125352420188531003)
    ·
      refine ⟨50353839188028630282796505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33569226125352420188531003 50353839188028630282796505)
      ·
        refine ⟨37765379391021472712097379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50353839188028630282796505 37765379391021472712097379)
        ·
          refine ⟨56648069086532209068146069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37765379391021472712097379 56648069086532209068146069)
          ·
            refine ⟨2655378238431197300069347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56648069086532209068146069 2655378238431197300069347)
            ·
              refine ⟨3983067357646795950104021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2655378238431197300069347 3983067357646795950104021)
              ·
                refine ⟨93353141194846780080563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3983067357646795950104021 93353141194846780080563)
                ·
                  rfl

theorem cell22_2454362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 7].length) (baseStart_2454362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454362 prefixEnd_2454362 := by exact prefixLift 2454362
  have htrace : WordTrace (prefixWord ++ tailWord_2454362) baseStart_2454362 baseEnd_2454362 := by
    simpa [prefixWord, tailWord_2454362, baseEnd_2454362] using wordTrace_append hprefix tailTrace_2454362
  have hstable : (prefixWord ++ tailWord_2454362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454362).length < 2 ^ (prefixWord ++ tailWord_2454362).sum := by decide
  have hdescent : baseEnd_2454362 < baseStart_2454362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454407 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 7]
def baseStart_2454407 : Nat := 118140960795 + 2454407 * 2 ^ 59
def prefixEnd_2454407 : Nat := 4983230072969 + 3 ^ 40 * 2454407 * 2
def baseEnd_2454407 : Nat := 280064558391085301116643

theorem tailTrace_2454407 : CollatzResearch.WordTrace tailWord_2454407 prefixEnd_2454407 280064558391085301116643 := by
  unfold tailWord_2454407
  simp only [CollatzResearch.WordTrace]
  refine ⟨89519577619110093188137475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59679718412740062125424983 89519577619110093188137475)
  ·
    refine ⟨134279366428665139782206213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89519577619110093188137475 134279366428665139782206213)
    ·
      refine ⟨25177381205374713709163665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134279366428665139782206213 25177381205374713709163665)
      ·
        refine ⟨18883035904031035281872749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25177381205374713709163665 18883035904031035281872749)
        ·
          refine ⟨7081138464011638230702281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18883035904031035281872749 7081138464011638230702281)
          ·
            refine ⟨5310853848008728673026711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7081138464011638230702281 5310853848008728673026711)
            ·
              refine ⟨7966280772013093009540067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5310853848008728673026711 7966280772013093009540067)
              ·
                refine ⟨11949421158019639514310101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7966280772013093009540067 11949421158019639514310101)
                ·
                  refine ⟨280064558391085301116643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11949421158019639514310101 280064558391085301116643)
                  ·
                    rfl

theorem cell22_2454407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 7].length) (baseStart_2454407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454407 prefixEnd_2454407 := by exact prefixLift 2454407
  have htrace : WordTrace (prefixWord ++ tailWord_2454407) baseStart_2454407 baseEnd_2454407 := by
    simpa [prefixWord, tailWord_2454407, baseEnd_2454407] using wordTrace_append hprefix tailTrace_2454407
  have hstable : (prefixWord ++ tailWord_2454407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454407).length < 2 ^ (prefixWord ++ tailWord_2454407).sum := by decide
  have hdescent : baseEnd_2454407 < baseStart_2454407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454499 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 2, 4]
def baseStart_2454499 : Nat := 118140960795 + 2454499 * 2 ^ 59
def prefixEnd_2454499 : Nat := 4983230072969 + 3 ^ 40 * 2454499 * 2
def baseEnd_2454499 : Nat := 840225168653398330049647

theorem tailTrace_2454499 : CollatzResearch.WordTrace tailWord_2454499 prefixEnd_2454499 840225168653398330049647 := by
  unfold tailWord_2454499
  simp only [CollatzResearch.WordTrace]
  refine ⟨89522933134776792900486551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59681955423184528600324367 89522933134776792900486551)
  ·
    refine ⟨134284399702165189350729827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89522933134776792900486551 134284399702165189350729827)
    ·
      refine ⟨201426599553247784026094741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134284399702165189350729827 201426599553247784026094741)
      ·
        refine ⟨9441871854058489876223191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 201426599553247784026094741 9441871854058489876223191)
        ·
          refine ⟨14162807781087734814334787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9441871854058489876223191 14162807781087734814334787)
          ·
            refine ⟨21244211671631602221502181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14162807781087734814334787 21244211671631602221502181)
            ·
              refine ⟨3983289688430925416531659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21244211671631602221502181 3983289688430925416531659)
              ·
                refine ⟨5974934532646388124797489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3983289688430925416531659 5974934532646388124797489)
                ·
                  refine ⟨4481200899484791093598117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5974934532646388124797489 4481200899484791093598117)
                  ·
                    refine ⟨840225168653398330049647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4481200899484791093598117 840225168653398330049647)
                    ·
                      rfl

theorem cell22_2454499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 4].length) (baseStart_2454499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454499 prefixEnd_2454499 := by exact prefixLift 2454499
  have htrace : WordTrace (prefixWord ++ tailWord_2454499) baseStart_2454499 baseEnd_2454499 := by
    simpa [prefixWord, tailWord_2454499, baseEnd_2454499] using wordTrace_append hprefix tailTrace_2454499
  have hstable : (prefixWord ++ tailWord_2454499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454499).length < 2 ^ (prefixWord ++ tailWord_2454499).sum := by decide
  have hdescent : baseEnd_2454499 < baseStart_2454499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454501 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 1, 5]
def baseStart_2454501 : Nat := 118140960795 + 2454501 * 2 ^ 59
def prefixEnd_2454501 : Nat := 4983230072969 + 3 ^ 40 * 2454501 * 2
def baseEnd_2454501 : Nat := 840225853294270991499641

theorem tailTrace_2454501 : CollatzResearch.WordTrace tailWord_2454501 prefixEnd_2454501 840225853294270991499641 := by
  unfold tailWord_2454501
  simp only [CollatzResearch.WordTrace]
  refine ⟨89523006080769547242059357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59682004053846364828039571 89523006080769547242059357)
  ·
    refine ⟨33571127280288580215772259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89523006080769547242059357 33571127280288580215772259)
    ·
      refine ⟨50356690920432870323658389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33571127280288580215772259 50356690920432870323658389)
      ·
        refine ⟨2360469886895290796421487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50356690920432870323658389 2360469886895290796421487)
        ·
          refine ⟨3540704830342936194632231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2360469886895290796421487 3540704830342936194632231)
          ·
            refine ⟨5311057245514404291948347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3540704830342936194632231 5311057245514404291948347)
            ·
              refine ⟨7966585868271606437922521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5311057245514404291948347 7966585868271606437922521)
              ·
                refine ⟨5974939401203704828441891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7966585868271606437922521 5974939401203704828441891)
                ·
                  refine ⟨8962409101805557242662837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5974939401203704828441891 8962409101805557242662837)
                  ·
                    refine ⟨840225853294270991499641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8962409101805557242662837 840225853294270991499641)
                    ·
                      rfl

theorem cell22_2454501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_2454501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454501 prefixEnd_2454501 := by exact prefixLift 2454501
  have htrace : WordTrace (prefixWord ++ tailWord_2454501) baseStart_2454501 baseEnd_2454501 := by
    simpa [prefixWord, tailWord_2454501, baseEnd_2454501] using wordTrace_append hprefix tailTrace_2454501
  have hstable : (prefixWord ++ tailWord_2454501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454501).length < 2 ^ (prefixWord ++ tailWord_2454501).sum := by decide
  have hdescent : baseEnd_2454501 < baseStart_2454501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454514 : List Nat := [3, 2, 1, 5, 1, 10]
def baseStart_2454514 : Nat := 118140960795 + 2454514 * 2 ^ 59
def prefixEnd_2454514 : Nat := 4983230072969 + 3 ^ 40 * 2454514 * 2
def baseEnd_2454514 : Nat := 10373213622962262850921

theorem tailTrace_2454514 : CollatzResearch.WordTrace tailWord_2454514 prefixEnd_2454514 10373213622962262850921 := by
  unfold tailWord_2454514
  simp only [CollatzResearch.WordTrace]
  refine ⟨22380870057430612615570649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59682320153148300308188397 22380870057430612615570649)
  ·
    refine ⟨16785652543072959461677987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22380870057430612615570649 16785652543072959461677987)
    ·
      refine ⟨25178478814609439192516981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16785652543072959461677987 25178478814609439192516981)
      ·
        refine ⟨2360482388869634924298467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25178478814609439192516981 2360482388869634924298467)
        ·
          refine ⟨3540723583304452386447701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2360482388869634924298467 3540723583304452386447701)
          ·
            refine ⟨10373213622962262850921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3540723583304452386447701 10373213622962262850921)
            ·
              rfl

theorem cell22_2454514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 10].length) (baseStart_2454514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454514 prefixEnd_2454514 := by exact prefixLift 2454514
  have htrace : WordTrace (prefixWord ++ tailWord_2454514) baseStart_2454514 baseEnd_2454514 := by
    simpa [prefixWord, tailWord_2454514, baseEnd_2454514] using wordTrace_append hprefix tailTrace_2454514
  have hstable : (prefixWord ++ tailWord_2454514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454514).length < 2 ^ (prefixWord ++ tailWord_2454514).sum := by decide
  have hdescent : baseEnd_2454514 < baseStart_2454514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454518 : List Nat := [5, 1, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_2454518 : Nat := 118140960795 + 2454518 * 2 ^ 59
def prefixEnd_2454518 : Nat := 4983230072969 + 3 ^ 40 * 2454518 * 2
def baseEnd_2454518 : Nat := 840231672741688613824589

theorem tailTrace_2454518 : CollatzResearch.WordTrace tailWord_2454518 prefixEnd_2454518 840231672741688613824589 := by
  unfold tailWord_2454518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5595226632606747446589263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59682417414471972763618805 5595226632606747446589263)
  ·
    refine ⟨8392839948910121169883895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5595226632606747446589263 8392839948910121169883895)
    ·
      refine ⟨12589259923365181754825843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8392839948910121169883895 12589259923365181754825843)
      ·
        refine ⟨18883889885047772632238765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12589259923365181754825843 18883889885047772632238765)
        ·
          refine ⟨7081458706892914737089537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18883889885047772632238765 7081458706892914737089537)
          ·
            refine ⟨5311094030169686052817153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7081458706892914737089537 5311094030169686052817153)
            ·
              refine ⟨3983320522627264539612865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5311094030169686052817153 3983320522627264539612865)
              ·
                refine ⟨2987490391970448404709649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3983320522627264539612865 2987490391970448404709649)
                ·
                  refine ⟨2240617793977836303532237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2987490391970448404709649 2240617793977836303532237)
                  ·
                    refine ⟨840231672741688613824589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2240617793977836303532237 840231672741688613824589)
                    ·
                      rfl

theorem cell22_2454518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_2454518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454518 prefixEnd_2454518 := by exact prefixLift 2454518
  have htrace : WordTrace (prefixWord ++ tailWord_2454518) baseStart_2454518 baseEnd_2454518 := by
    simpa [prefixWord, tailWord_2454518, baseEnd_2454518] using wordTrace_append hprefix tailTrace_2454518
  have hstable : (prefixWord ++ tailWord_2454518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454518).length < 2 ^ (prefixWord ++ tailWord_2454518).sum := by decide
  have hdescent : baseEnd_2454518 < baseStart_2454518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454563 : List Nat := [1, 1, 1, 4, 3, 3, 2, 3, 1, 3]
def baseStart_2454563 : Nat := 118140960795 + 2454563 * 2 ^ 59
def prefixEnd_2454563 : Nat := 4983230072969 + 3 ^ 40 * 2454563 * 2
def baseEnd_2454563 : Nat := 840247077161323496449451

theorem tailTrace_2454563 : CollatzResearch.WordTrace tailWord_2454563 prefixEnd_2454563 840247077161323496449451 := by
  unfold tailWord_2454563
  simp only [CollatzResearch.WordTrace]
  refine ⟨89525267406544931830816343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59683511604363287887210895 89525267406544931830816343)
  ·
    refine ⟨134287901109817397746224515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89525267406544931830816343 134287901109817397746224515)
    ·
      refine ⟨201431851664726096619336773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134287901109817397746224515 201431851664726096619336773)
      ·
        refine ⟨37768472187136143116125645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201431851664726096619336773 37768472187136143116125645)
        ·
          refine ⟨14163177070176053668547117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37768472187136143116125645 14163177070176053668547117)
          ·
            refine ⟨5311191401316020125705169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14163177070176053668547117 5311191401316020125705169)
            ·
              refine ⟨3983393550987015094278877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5311191401316020125705169 3983393550987015094278877)
              ·
                refine ⟨1493772581620130660354579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3983393550987015094278877 1493772581620130660354579)
                ·
                  refine ⟨2240658872430195990531869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493772581620130660354579 2240658872430195990531869)
                  ·
                    refine ⟨840247077161323496449451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2240658872430195990531869 840247077161323496449451)
                    ·
                      rfl

theorem cell22_2454563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 1, 3].length) (baseStart_2454563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454563 prefixEnd_2454563 := by exact prefixLift 2454563
  have htrace : WordTrace (prefixWord ++ tailWord_2454563) baseStart_2454563 baseEnd_2454563 := by
    simpa [prefixWord, tailWord_2454563, baseEnd_2454563] using wordTrace_append hprefix tailTrace_2454563
  have hstable : (prefixWord ++ tailWord_2454563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454563).length < 2 ^ (prefixWord ++ tailWord_2454563).sum := by decide
  have hdescent : baseEnd_2454563 < baseStart_2454563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454574 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2454574 : Nat := 118140960795 + 2454574 * 2 ^ 59
def prefixEnd_2454574 : Nat := 4983230072969 + 3 ^ 40 * 2454574 * 2
def baseEnd_2454574 : Nat := 840250842686123134424417

theorem tailTrace_2454574 : CollatzResearch.WordTrace tailWord_2454574 prefixEnd_2454574 840250842686123134424417 := by
  unfold tailWord_2454574
  simp only [CollatzResearch.WordTrace]
  refine ⟨11190708576188135088683347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59683779073003387139644517 11190708576188135088683347)
  ·
    refine ⟨16786062864282202633025021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11190708576188135088683347 16786062864282202633025021)
    ·
      refine ⟨6294773574105825987384383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16786062864282202633025021 6294773574105825987384383)
      ·
        refine ⟨9442160361158738981076575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6294773574105825987384383 9442160361158738981076575)
        ·
          refine ⟨14163240541738108471614863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9442160361158738981076575 14163240541738108471614863)
          ·
            refine ⟨21244860812607162707422295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14163240541738108471614863 21244860812607162707422295)
            ·
              refine ⟨31867291218910744061133443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21244860812607162707422295 31867291218910744061133443)
              ·
                refine ⟨47800936828366116091700165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31867291218910744061133443 47800936828366116091700165)
                ·
                  refine ⟨8962675655318646767193781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47800936828366116091700165 8962675655318646767193781)
                  ·
                    refine ⟨840250842686123134424417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8962675655318646767193781 840250842686123134424417)
                    ·
                      rfl

theorem cell22_2454574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2454574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454574 prefixEnd_2454574 := by exact prefixLift 2454574
  have htrace : WordTrace (prefixWord ++ tailWord_2454574) baseStart_2454574 baseEnd_2454574 := by
    simpa [prefixWord, tailWord_2454574, baseEnd_2454574] using wordTrace_append hprefix tailTrace_2454574
  have hstable : (prefixWord ++ tailWord_2454574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454574).length < 2 ^ (prefixWord ++ tailWord_2454574).sum := by decide
  have hdescent : baseEnd_2454574 < baseStart_2454574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454580 : List Nat := [2, 5, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_2454580 : Nat := 118140960795 + 2454580 * 2 ^ 59
def prefixEnd_2454580 : Nat := 4983230072969 + 3 ^ 40 * 2454580 * 2
def baseEnd_2454580 : Nat := 840252896608741118774399

theorem tailTrace_2454580 : CollatzResearch.WordTrace tailWord_2454580 prefixEnd_2454580 840252896608741118774399 := by
  unfold tailWord_2454580
  simp only [CollatzResearch.WordTrace]
  refine ⟨44762943723741671867092597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59683924964988895822790129 44762943723741671867092597)
  ·
    refine ⟨4196525974100781737539931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44762943723741671867092597 4196525974100781737539931)
    ·
      refine ⟨6294788961151172606309897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4196525974100781737539931 6294788961151172606309897)
      ·
        refine ⟨4721091720863379454732423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6294788961151172606309897 4721091720863379454732423)
        ·
          refine ⟨7081637581295069182098635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4721091720863379454732423 7081637581295069182098635)
          ·
            refine ⟨10622456371942603773147953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7081637581295069182098635 10622456371942603773147953)
            ·
              refine ⟨7966842278956952829860965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10622456371942603773147953 7966842278956952829860965)
              ·
                refine ⟨1493782927304428655598931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7966842278956952829860965 1493782927304428655598931)
                ·
                  refine ⟨2240674390956642983398397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493782927304428655598931 2240674390956642983398397)
                  ·
                    refine ⟨840252896608741118774399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2240674390956642983398397 840252896608741118774399)
                    ·
                      rfl

theorem cell22_2454580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_2454580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454580 prefixEnd_2454580 := by exact prefixLift 2454580
  have htrace : WordTrace (prefixWord ++ tailWord_2454580) baseStart_2454580 baseEnd_2454580 := by
    simpa [prefixWord, tailWord_2454580, baseEnd_2454580] using wordTrace_append hprefix tailTrace_2454580
  have hstable : (prefixWord ++ tailWord_2454580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454580).length < 2 ^ (prefixWord ++ tailWord_2454580).sum := by decide
  have hdescent : baseEnd_2454580 < baseStart_2454580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454593 : List Nat := [1, 2, 5, 1, 3, 1, 3, 1, 5]
def baseStart_2454593 : Nat := 118140960795 + 2454593 * 2 ^ 59
def prefixEnd_2454593 : Nat := 4983230072969 + 3 ^ 40 * 2454593 * 2
def baseEnd_2454593 : Nat := 280085782258137806066453

theorem tailTrace_2454593 : CollatzResearch.WordTrace tailWord_2454593 prefixEnd_2454593 280085782258137806066453 := by
  unfold tailWord_2454593
  simp only [CollatzResearch.WordTrace]
  refine ⟨89526361596436246954408433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59684241064290831302938955 89526361596436246954408433)
  ·
    refine ⟨67144771197327185215806325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89526361596436246954408433 67144771197327185215806325)
    ·
      refine ⟨6294822299749423613981843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67144771197327185215806325 6294822299749423613981843)
      ·
        refine ⟨9442233449624135420972765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6294822299749423613981843 9442233449624135420972765)
        ·
          refine ⟨3540837543609050782864787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9442233449624135420972765 3540837543609050782864787)
          ·
            refine ⟨5311256315413576174297181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3540837543609050782864787 5311256315413576174297181)
            ·
              refine ⟨1991721118280091065361443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5311256315413576174297181 1991721118280091065361443)
              ·
                refine ⟨2987581677420136598042165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1991721118280091065361443 2987581677420136598042165)
                ·
                  refine ⟨280085782258137806066453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2987581677420136598042165 280085782258137806066453)
                  ·
                    rfl

theorem cell22_2454593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 5].length) (baseStart_2454593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454593 prefixEnd_2454593 := by exact prefixLift 2454593
  have htrace : WordTrace (prefixWord ++ tailWord_2454593) baseStart_2454593 baseEnd_2454593 := by
    simpa [prefixWord, tailWord_2454593, baseEnd_2454593] using wordTrace_append hprefix tailTrace_2454593
  have hstable : (prefixWord ++ tailWord_2454593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454593).length < 2 ^ (prefixWord ++ tailWord_2454593).sum := by decide
  have hdescent : baseEnd_2454593 < baseStart_2454593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454606 : List Nat := [4, 1, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_2454606 : Nat := 118140960795 + 2454606 * 2 ^ 59
def prefixEnd_2454606 : Nat := 4983230072969 + 3 ^ 40 * 2454606 * 2
def baseEnd_2454606 : Nat := 840261796940085717624319

theorem tailTrace_2454606 : CollatzResearch.WordTrace tailWord_2454606 prefixEnd_2454606 840261796940085717624319 := by
  unfold tailWord_2454606
  simp only [CollatzResearch.WordTrace]
  refine ⟨11190854468173643771828959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59684557163592766783087781 11190854468173643771828959)
  ·
    refine ⟨16786281702260465657743439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11190854468173643771828959 16786281702260465657743439)
    ·
      refine ⟨25179422553390698486615159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16786281702260465657743439 25179422553390698486615159)
      ·
        refine ⟨37769133830086047729922739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25179422553390698486615159 37769133830086047729922739)
        ·
          refine ⟨56653700745129071594884109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37769133830086047729922739 56653700745129071594884109)
          ·
            refine ⟨21245137779423401848081541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56653700745129071594884109 21245137779423401848081541)
            ·
              refine ⟨3983463333641887846515289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21245137779423401848081541 3983463333641887846515289)
              ·
                refine ⟨2987597500231415884886467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3983463333641887846515289 2987597500231415884886467)
                ·
                  refine ⟨4481396250347123827329701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2987597500231415884886467 4481396250347123827329701)
                  ·
                    refine ⟨840261796940085717624319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4481396250347123827329701 840261796940085717624319)
                    ·
                      rfl

theorem cell22_2454606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_2454606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454606 prefixEnd_2454606 := by exact prefixLift 2454606
  have htrace : WordTrace (prefixWord ++ tailWord_2454606) baseStart_2454606 baseEnd_2454606 := by
    simpa [prefixWord, tailWord_2454606, baseEnd_2454606] using wordTrace_append hprefix tailTrace_2454606
  have hstable : (prefixWord ++ tailWord_2454606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454606).length < 2 ^ (prefixWord ++ tailWord_2454606).sum := by decide
  have hdescent : baseEnd_2454606 < baseStart_2454606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454614 : List Nat := [5, 2, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2454614 : Nat := 118140960795 + 2454614 * 2 ^ 59
def prefixEnd_2454614 : Nat := 4983230072969 + 3 ^ 40 * 2454614 * 2
def baseEnd_2454614 : Nat := 840264535503576363424295

theorem tailTrace_2454614 : CollatzResearch.WordTrace tailWord_2454614 prefixEnd_2454614 840264535503576363424295 := by
  unfold tailWord_2454614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5595445470585010471307681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59684751686240111693948597 5595445470585010471307681)
  ·
    refine ⟨4196584102938757853480761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5595445470585010471307681 4196584102938757853480761)
    ·
      refine ⟨3147438077204068390110571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4196584102938757853480761 3147438077204068390110571)
      ·
        refine ⟨4721157115806102585165857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3147438077204068390110571 4721157115806102585165857)
        ·
          refine ⟨3540867836854576938874393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4721157115806102585165857 3540867836854576938874393)
          ·
            refine ⟨2655650877640932704155795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3540867836854576938874393 2655650877640932704155795)
            ·
              refine ⟨3983476316461399056233693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2655650877640932704155795 3983476316461399056233693)
              ·
                refine ⟨1493803618673024646087635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3983476316461399056233693 1493803618673024646087635)
                ·
                  refine ⟨2240705428009536969131453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493803618673024646087635 2240705428009536969131453)
                  ·
                    refine ⟨840264535503576363424295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2240705428009536969131453 840264535503576363424295)
                    ·
                      rfl

theorem cell22_2454614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2454614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454614 prefixEnd_2454614 := by exact prefixLift 2454614
  have htrace : WordTrace (prefixWord ++ tailWord_2454614) baseStart_2454614 baseEnd_2454614 := by
    simpa [prefixWord, tailWord_2454614, baseEnd_2454614] using wordTrace_append hprefix tailTrace_2454614
  have hstable : (prefixWord ++ tailWord_2454614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454614).length < 2 ^ (prefixWord ++ tailWord_2454614).sum := by decide
  have hdescent : baseEnd_2454614 < baseStart_2454614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454636 : List Nat := [2, 2, 1, 1, 3, 2, 2, 4, 2, 3]
def baseStart_2454636 : Nat := 118140960795 + 2454636 * 2 ^ 59
def prefixEnd_2454636 : Nat := 4983230072969 + 3 ^ 40 * 2454636 * 2
def baseEnd_2454636 : Nat := 840272066553175639374227

theorem tailTrace_2454636 : CollatzResearch.WordTrace tailWord_2454636 prefixEnd_2454636 840272066553175639374227 := by
  unfold tailWord_2454636
  simp only [CollatzResearch.WordTrace]
  refine ⟨44763964967640232649111881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59685286623520310198815841 44763964967640232649111881)
  ·
    refine ⟨33572973725730174486833911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44763964967640232649111881 33572973725730174486833911)
    ·
      refine ⟨50359460588595261730250867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33572973725730174486833911 50359460588595261730250867)
      ·
        refine ⟨75539190882892892595376301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50359460588595261730250867 75539190882892892595376301)
        ·
          refine ⟨28327196581084834723266113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75539190882892892595376301 28327196581084834723266113)
          ·
            refine ⟨21245397435813626042449585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28327196581084834723266113 21245397435813626042449585)
            ·
              refine ⟨15934048076860219531837189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21245397435813626042449585 15934048076860219531837189)
              ·
                refine ⟨2987634014411291162219473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15934048076860219531837189 2987634014411291162219473)
                ·
                  refine ⟨2240725510808468371664605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2987634014411291162219473 2240725510808468371664605)
                  ·
                    refine ⟨840272066553175639374227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2240725510808468371664605 840272066553175639374227)
                    ·
                      rfl

theorem cell22_2454636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_2454636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454636 prefixEnd_2454636 := by exact prefixLift 2454636
  have htrace : WordTrace (prefixWord ++ tailWord_2454636) baseStart_2454636 baseEnd_2454636 := by
    simpa [prefixWord, tailWord_2454636, baseEnd_2454636] using wordTrace_append hprefix tailTrace_2454636
  have hstable : (prefixWord ++ tailWord_2454636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454636).length < 2 ^ (prefixWord ++ tailWord_2454636).sum := by decide
  have hdescent : baseEnd_2454636 < baseStart_2454636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454771 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 1, 5]
def baseStart_2454771 : Nat := 118140960795 + 2454771 * 2 ^ 59
def prefixEnd_2454771 : Nat := 4983230072969 + 3 ^ 40 * 2454771 * 2
def baseEnd_2454771 : Nat := 840318279812080287248813

theorem tailTrace_2454771 : CollatzResearch.WordTrace tailWord_2454771 prefixEnd_2454771 840318279812080287248813 := by
  unfold tailWord_2454771
  simp only [CollatzResearch.WordTrace]
  refine ⟨89532853789791383354388167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59688569193194255569592111 89532853789791383354388167)
  ·
    refine ⟨134299280684687075031582251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89532853789791383354388167 134299280684687075031582251)
    ·
      refine ⟨201448921027030612547373377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134299280684687075031582251 201448921027030612547373377)
      ·
        refine ⟨151086690770272959410530033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201448921027030612547373377 151086690770272959410530033)
        ·
          refine ⟨113315018077704719557897525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151086690770272959410530033 113315018077704719557897525)
          ·
            refine ⟨10623282944784817458552893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113315018077704719557897525 10623282944784817458552893)
            ·
              refine ⟨3983731104294306546957335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10623282944784817458552893 3983731104294306546957335)
              ·
                refine ⟨5975596656441459820436003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3983731104294306546957335 5975596656441459820436003)
                ·
                  refine ⟨8963394984662189730654005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5975596656441459820436003 8963394984662189730654005)
                  ·
                    refine ⟨840318279812080287248813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8963394984662189730654005 840318279812080287248813)
                    ·
                      rfl

theorem cell22_2454771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 5].length) (baseStart_2454771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454771 prefixEnd_2454771 := by exact prefixLift 2454771
  have htrace : WordTrace (prefixWord ++ tailWord_2454771) baseStart_2454771 baseEnd_2454771 := by
    simpa [prefixWord, tailWord_2454771, baseEnd_2454771] using wordTrace_append hprefix tailTrace_2454771
  have hstable : (prefixWord ++ tailWord_2454771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454771).length < 2 ^ (prefixWord ++ tailWord_2454771).sum := by decide
  have hdescent : baseEnd_2454771 < baseStart_2454771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454788 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_2454788 : Nat := 118140960795 + 2454788 * 2 ^ 59
def prefixEnd_2454788 : Nat := 4983230072969 + 3 ^ 40 * 2454788 * 2
def baseEnd_2454788 : Nat := 840324099259497909573761

theorem tailTrace_2454788 : CollatzResearch.WordTrace tailWord_2454788 prefixEnd_2454788 840324099259497909573761 := by
  unfold tailWord_2454788
  simp only [CollatzResearch.WordTrace]
  refine ⟨44766736915364897628878509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59688982553819863505171345 44766736915364897628878509)
  ·
    refine ⟨16787526343261836610829441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44766736915364897628878509 16787526343261836610829441)
    ·
      refine ⟨12590644757446377458122081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16787526343261836610829441 12590644757446377458122081)
      ·
        refine ⟨9442983568084783093591561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12590644757446377458122081 9442983568084783093591561)
        ·
          refine ⟨7082237676063587320193671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9442983568084783093591561 7082237676063587320193671)
          ·
            refine ⟨10623356514095380980290507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7082237676063587320193671 10623356514095380980290507)
            ·
              refine ⟨15935034771143071470435761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10623356514095380980290507 15935034771143071470435761)
              ·
                refine ⟨11951276078357303602826821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15935034771143071470435761 11951276078357303602826821)
                ·
                  refine ⟨2240864264691994425530029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11951276078357303602826821 2240864264691994425530029)
                  ·
                    refine ⟨840324099259497909573761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2240864264691994425530029 840324099259497909573761)
                    ·
                      rfl

theorem cell22_2454788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_2454788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454788 prefixEnd_2454788 := by exact prefixLift 2454788
  have htrace : WordTrace (prefixWord ++ tailWord_2454788) baseStart_2454788 baseEnd_2454788 := by
    simpa [prefixWord, tailWord_2454788, baseEnd_2454788] using wordTrace_append hprefix tailTrace_2454788
  have hstable : (prefixWord ++ tailWord_2454788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454788).length < 2 ^ (prefixWord ++ tailWord_2454788).sum := by decide
  have hdescent : baseEnd_2454788 < baseStart_2454788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454818 : List Nat := [3, 3, 1, 1, 4, 1, 2, 7]
def baseStart_2454818 : Nat := 118140960795 + 2454818 * 2 ^ 59
def prefixEnd_2454818 : Nat := 4983230072969 + 3 ^ 40 * 2454818 * 2
def baseEnd_2454818 : Nat := 93370485430287536813741

theorem tailTrace_2454818 : CollatzResearch.WordTrace tailWord_2454818 prefixEnd_2454818 93370485430287536813741 := by
  unfold tailWord_2454818
  simp only [CollatzResearch.WordTrace]
  refine ⟨22383642005155277595337277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59689712013747406920899405 22383642005155277595337277)
  ·
    refine ⟨8393865751933229098251479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22383642005155277595337277 8393865751933229098251479)
    ·
      refine ⟨12590798627899843647377219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8393865751933229098251479 12590798627899843647377219)
      ·
        refine ⟨18886197941849765471065829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12590798627899843647377219 18886197941849765471065829)
        ·
          refine ⟨3541162114096831025824843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18886197941849765471065829 3541162114096831025824843)
          ·
            refine ⟨5311743171145246538737265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3541162114096831025824843 5311743171145246538737265)
            ·
              refine ⟨3983807378358934904052949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5311743171145246538737265 3983807378358934904052949)
              ·
                refine ⟨93370485430287536813741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3983807378358934904052949 93370485430287536813741)
                ·
                  rfl

theorem cell22_2454818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_2454818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454818 prefixEnd_2454818 := by exact prefixLift 2454818
  have htrace : WordTrace (prefixWord ++ tailWord_2454818) baseStart_2454818 baseEnd_2454818 := by
    simpa [prefixWord, tailWord_2454818, baseEnd_2454818] using wordTrace_append hprefix tailTrace_2454818
  have hstable : (prefixWord ++ tailWord_2454818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454818).length < 2 ^ (prefixWord ++ tailWord_2454818).sum := by decide
  have hdescent : baseEnd_2454818 < baseStart_2454818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454893 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_2454893 : Nat := 118140960795 + 2454893 * 2 ^ 59
def prefixEnd_2454893 : Nat := 4983230072969 + 3 ^ 40 * 2454893 * 2
def baseEnd_2454893 : Nat := 840360042905312635698439

theorem tailTrace_2454893 : CollatzResearch.WordTrace tailWord_2454893 prefixEnd_2454893 840360042905312635698439 := by
  unfold tailWord_2454893
  simp only [CollatzResearch.WordTrace]
  refine ⟨89537303495349398190329333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59691535663566265460219555 89537303495349398190329333)
  ·
    refine ⟨8394122202689006080343375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89537303495349398190329333 8394122202689006080343375)
    ·
      refine ⟨12591183304033509120515063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8394122202689006080343375 12591183304033509120515063)
      ·
        refine ⟨18886774956050263680772595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12591183304033509120515063 18886774956050263680772595)
        ·
          refine ⟨28330162434075395521158893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18886774956050263680772595 28330162434075395521158893)
          ·
            refine ⟨10623810912778273320434585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28330162434075395521158893 10623810912778273320434585)
            ·
              refine ⟨7967858184583704990325939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10623810912778273320434585 7967858184583704990325939)
              ·
                refine ⟨11951787276875557485488909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7967858184583704990325939 11951787276875557485488909)
                ·
                  refine ⟨4481920228828334057058341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11951787276875557485488909 4481920228828334057058341)
                  ·
                    refine ⟨840360042905312635698439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4481920228828334057058341 840360042905312635698439)
                    ·
                      rfl

theorem cell22_2454893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_2454893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454893 prefixEnd_2454893 := by exact prefixLift 2454893
  have htrace : WordTrace (prefixWord ++ tailWord_2454893) baseStart_2454893 baseEnd_2454893 := by
    simpa [prefixWord, tailWord_2454893, baseEnd_2454893] using wordTrace_append hprefix tailTrace_2454893
  have hstable : (prefixWord ++ tailWord_2454893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454893).length < 2 ^ (prefixWord ++ tailWord_2454893).sum := by decide
  have hdescent : baseEnd_2454893 < baseStart_2454893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454923 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 4, 3]
def baseStart_2454923 : Nat := 118140960795 + 2454923 * 2 ^ 59
def prefixEnd_2454923 : Nat := 4983230072969 + 3 ^ 40 * 2454923 * 2
def baseEnd_2454923 : Nat := 840370312518402557448347

theorem tailTrace_2454923 : CollatzResearch.WordTrace tailWord_2454923 prefixEnd_2454923 840370312518402557448347 := by
  unfold tailWord_2454923
  simp only [CollatzResearch.WordTrace]
  refine ⟨89538397685240713313921423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59692265123493808875947615 89538397685240713313921423)
  ·
    refine ⟨134307596527861069970882135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89538397685240713313921423 134307596527861069970882135)
    ·
      refine ⟨201461394791791604956323203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134307596527861069970882135 201461394791791604956323203)
      ·
        refine ⟨302192092187687407434484805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201461394791791604956323203 302192092187687407434484805)
        ·
          refine ⟨56661017285191388893965901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 302192092187687407434484805 56661017285191388893965901)
          ·
            refine ⟨21247881481946770835237213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56661017285191388893965901 21247881481946770835237213)
            ·
              refine ⟨7967955555730039063213955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21247881481946770835237213 7967955555730039063213955)
              ·
                refine ⟨11951933333595058594820933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7967955555730039063213955 11951933333595058594820933)
                ·
                  refine ⟨2240987500049073486528925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11951933333595058594820933 2240987500049073486528925)
                  ·
                    refine ⟨840370312518402557448347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2240987500049073486528925 840370312518402557448347)
                    ·
                      rfl

theorem cell22_2454923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 3].length) (baseStart_2454923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454923 prefixEnd_2454923 := by exact prefixLift 2454923
  have htrace : WordTrace (prefixWord ++ tailWord_2454923) baseStart_2454923 baseEnd_2454923 := by
    simpa [prefixWord, tailWord_2454923, baseEnd_2454923] using wordTrace_append hprefix tailTrace_2454923
  have hstable : (prefixWord ++ tailWord_2454923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454923).length < 2 ^ (prefixWord ++ tailWord_2454923).sum := by decide
  have hdescent : baseEnd_2454923 < baseStart_2454923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2454968 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 5, 3]
def baseStart_2454968 : Nat := 118140960795 + 2454968 * 2 ^ 59
def prefixEnd_2454968 : Nat := 4983230072969 + 3 ^ 40 * 2454968 * 2
def baseEnd_2454968 : Nat := 840385716938037440073209

theorem tailTrace_2454968 : CollatzResearch.WordTrace tailWord_2454968 prefixEnd_2454968 840385716938037440073209 := by
  unfold tailWord_2454968
  simp only [CollatzResearch.WordTrace]
  refine ⟨44770019485038842999654779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59693359313385123999539705 44770019485038842999654779)
  ·
    refine ⟨67155029227558264499482169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44770019485038842999654779 67155029227558264499482169)
    ·
      refine ⟨50366271920668698374611627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67155029227558264499482169 50366271920668698374611627)
      ·
        refine ⟨75549407881003047561917441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50366271920668698374611627 75549407881003047561917441)
        ·
          refine ⟨56662055910752285671438081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75549407881003047561917441 56662055910752285671438081)
          ·
            refine ⟨42496541933064214253578561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56662055910752285671438081 42496541933064214253578561)
            ·
              refine ⟨31872406449798160690183921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42496541933064214253578561 31872406449798160690183921)
              ·
                refine ⟨23904304837348620517637941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31872406449798160690183921 23904304837348620517637941)
                ·
                  refine ⟨2241028578501433173528557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23904304837348620517637941 2241028578501433173528557)
                  ·
                    refine ⟨840385716938037440073209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2241028578501433173528557 840385716938037440073209)
                    ·
                      rfl

theorem cell22_2454968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_2454968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2454968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2454968 prefixEnd_2454968 := by exact prefixLift 2454968
  have htrace : WordTrace (prefixWord ++ tailWord_2454968) baseStart_2454968 baseEnd_2454968 := by
    simpa [prefixWord, tailWord_2454968, baseEnd_2454968] using wordTrace_append hprefix tailTrace_2454968
  have hstable : (prefixWord ++ tailWord_2454968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2454968).length < 2 ^ (prefixWord ++ tailWord_2454968).sum := by decide
  have hdescent : baseEnd_2454968 < baseStart_2454968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2454968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455070 : List Nat := [4, 3, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2455070 : Nat := 118140960795 + 2455070 * 2 ^ 59
def prefixEnd_2455070 : Nat := 4983230072969 + 3 ^ 40 * 2455070 * 2
def baseEnd_2455070 : Nat := 840420633622543174022897

theorem tailTrace_2455070 : CollatzResearch.WordTrace tailWord_2455070 prefixEnd_2455070 840420633622543174022897 := by
  unfold tailWord_2455070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11192969901963519677440333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59695839477138771613015109 11192969901963519677440333)
  ·
    refine ⟨4197363713236319879040125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11192969901963519677440333 4197363713236319879040125)
    ·
      refine ⟨1574011392463619954640047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4197363713236319879040125 1574011392463619954640047)
      ·
        refine ⟨2361017088695429931960071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574011392463619954640047 2361017088695429931960071)
        ·
          refine ⟨3541525633043144897940107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2361017088695429931960071 3541525633043144897940107)
          ·
            refine ⟨5312288449564717346910161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3541525633043144897940107 5312288449564717346910161)
            ·
              refine ⟨3984216337173538010182621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5312288449564717346910161 3984216337173538010182621)
              ·
                refine ⟨1494081126440076753818483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3984216337173538010182621 1494081126440076753818483)
                ·
                  refine ⟨2241121689660115130727725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494081126440076753818483 2241121689660115130727725)
                  ·
                    refine ⟨840420633622543174022897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2241121689660115130727725 840420633622543174022897)
                    ·
                      rfl

theorem cell22_2455070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2455070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455070 prefixEnd_2455070 := by exact prefixLift 2455070
  have htrace : WordTrace (prefixWord ++ tailWord_2455070) baseStart_2455070 baseEnd_2455070 := by
    simpa [prefixWord, tailWord_2455070, baseEnd_2455070] using wordTrace_append hprefix tailTrace_2455070
  have hstable : (prefixWord ++ tailWord_2455070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455070).length < 2 ^ (prefixWord ++ tailWord_2455070).sum := by decide
  have hdescent : baseEnd_2455070 < baseStart_2455070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455120 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 3, 3]
def baseStart_2455120 : Nat := 118140960795 + 2455120 * 2 ^ 59
def prefixEnd_2455120 : Nat := 4983230072969 + 3 ^ 40 * 2455120 * 2
def baseEnd_2455120 : Nat := 840437749644359710272743

theorem tailTrace_2455120 : CollatzResearch.WordTrace tailWord_2455120 prefixEnd_2455120 840437749644359710272743 := by
  unfold tailWord_2455120
  simp only [CollatzResearch.WordTrace]
  refine ⟨44772791432763507979421407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59697055243684677305895209 44772791432763507979421407)
  ·
    refine ⟨67159187149145261969132111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44772791432763507979421407 67159187149145261969132111)
    ·
      refine ⟨100738780723717892953698167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67159187149145261969132111 100738780723717892953698167)
      ·
        refine ⟨151108171085576839430547251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100738780723717892953698167 151108171085576839430547251)
        ·
          refine ⟨226662256628365259145820877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151108171085576839430547251 226662256628365259145820877)
          ·
            refine ⟨84998346235636972179682829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226662256628365259145820877 84998346235636972179682829)
            ·
              refine ⟨31874379838363864567381061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84998346235636972179682829 31874379838363864567381061)
              ·
                refine ⟨5976446219693224606383949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31874379838363864567381061 5976446219693224606383949)
                ·
                  refine ⟨2241167332384959227393981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5976446219693224606383949 2241167332384959227393981)
                  ·
                    refine ⟨840437749644359710272743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2241167332384959227393981 840437749644359710272743)
                    ·
                      rfl

theorem cell22_2455120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 3, 3].length) (baseStart_2455120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455120 prefixEnd_2455120 := by exact prefixLift 2455120
  have htrace : WordTrace (prefixWord ++ tailWord_2455120) baseStart_2455120 baseEnd_2455120 := by
    simpa [prefixWord, tailWord_2455120, baseEnd_2455120] using wordTrace_append hprefix tailTrace_2455120
  have hstable : (prefixWord ++ tailWord_2455120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455120).length < 2 ^ (prefixWord ++ tailWord_2455120).sum := by decide
  have hdescent : baseEnd_2455120 < baseStart_2455120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455122 : List Nat := [3, 2, 2, 1, 2, 4, 2, 6]
def baseStart_2455122 : Nat := 118140960795 + 2455122 * 2 ^ 59
def prefixEnd_2455122 : Nat := 4983230072969 + 3 ^ 40 * 2455122 * 2
def baseEnd_2455122 : Nat := 93382048253914707969193

theorem tailTrace_2455122 : CollatzResearch.WordTrace tailWord_2455122 prefixEnd_2455122 93382048253914707969193 := by
  unfold tailWord_2455122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22386413952879942575103905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59697103874346513533610413 22386413952879942575103905)
  ·
    refine ⟨16789810464659956931327929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22386413952879942575103905 16789810464659956931327929)
    ·
      refine ⟨12592357848494967698495947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16789810464659956931327929 12592357848494967698495947)
      ·
        refine ⟨18888536772742451547743921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12592357848494967698495947 18888536772742451547743921)
        ·
          refine ⟨14166402579556838660807941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18888536772742451547743921 14166402579556838660807941)
          ·
            refine ⟨2656200483666907248901489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14166402579556838660807941 2656200483666907248901489)
            ·
              refine ⟨1992150362750180436676117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2656200483666907248901489 1992150362750180436676117)
              ·
                refine ⟨93382048253914707969193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1992150362750180436676117 93382048253914707969193)
                ·
                  rfl

theorem cell22_2455122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 6].length) (baseStart_2455122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455122 prefixEnd_2455122 := by exact prefixLift 2455122
  have htrace : WordTrace (prefixWord ++ tailWord_2455122) baseStart_2455122 baseEnd_2455122 := by
    simpa [prefixWord, tailWord_2455122, baseEnd_2455122] using wordTrace_append hprefix tailTrace_2455122
  have hstable : (prefixWord ++ tailWord_2455122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455122).length < 2 ^ (prefixWord ++ tailWord_2455122).sum := by decide
  have hdescent : baseEnd_2455122 < baseStart_2455122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455154 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_2455154 : Nat := 118140960795 + 2455154 * 2 ^ 59
def prefixEnd_2455154 : Nat := 4983230072969 + 3 ^ 40 * 2455154 * 2
def baseEnd_2455154 : Nat := 840449388539194954922639

theorem tailTrace_2455154 : CollatzResearch.WordTrace tailWord_2455154 prefixEnd_2455154 840449388539194954922639 := by
  unfold tailWord_2455154
  simp only [CollatzResearch.WordTrace]
  refine ⟨22386705736850959941395129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59697881964935893177053677 22386705736850959941395129)
  ·
    refine ⟨16790029302638219956046347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22386705736850959941395129 16790029302638219956046347)
    ·
      refine ⟨25185043953957329934069521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16790029302638219956046347 25185043953957329934069521)
      ·
        refine ⟨18888782965467997450552141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25185043953957329934069521 18888782965467997450552141)
        ·
          refine ⟨7083293612050499043957053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18888782965467997450552141 7083293612050499043957053)
          ·
            refine ⟨2656235104518937141483895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7083293612050499043957053 2656235104518937141483895)
            ·
              refine ⟨3984352656778405712225843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2656235104518937141483895 3984352656778405712225843)
              ·
                refine ⟨5976528985167608568338765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3984352656778405712225843 5976528985167608568338765)
                ·
                  refine ⟨2241198369437853213127037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5976528985167608568338765 2241198369437853213127037)
                  ·
                    refine ⟨840449388539194954922639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2241198369437853213127037 840449388539194954922639)
                    ·
                      rfl

theorem cell22_2455154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_2455154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455154 prefixEnd_2455154 := by exact prefixLift 2455154
  have htrace : WordTrace (prefixWord ++ tailWord_2455154) baseStart_2455154 baseEnd_2455154 := by
    simpa [prefixWord, tailWord_2455154, baseEnd_2455154] using wordTrace_append hprefix tailTrace_2455154
  have hstable : (prefixWord ++ tailWord_2455154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455154).length < 2 ^ (prefixWord ++ tailWord_2455154).sum := by decide
  have hdescent : baseEnd_2455154 < baseStart_2455154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455180 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_2455180 : Nat := 118140960795 + 2455180 * 2 ^ 59
def prefixEnd_2455180 : Nat := 4983230072969 + 3 ^ 40 * 2455180 * 2
def baseEnd_2455180 : Nat := 840458288870539553772559

theorem tailTrace_2455180 : CollatzResearch.WordTrace tailWord_2455180 prefixEnd_2455180 840458288870539553772559 := by
  unfold tailWord_2455180
  simp only [CollatzResearch.WordTrace]
  refine ⟨44773885622654823103013497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59698514163539764137351329 44773885622654823103013497)
  ·
    refine ⟨33580414216991117327260123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44773885622654823103013497 33580414216991117327260123)
    ·
      refine ⟨50370621325486675990890185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33580414216991117327260123 50370621325486675990890185)
      ·
        refine ⟨37777965994115006993167639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50370621325486675990890185 37777965994115006993167639)
        ·
          refine ⟨56666948991172510489751459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37777965994115006993167639 56666948991172510489751459)
          ·
            refine ⟨85000423486758765734627189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56666948991172510489751459 85000423486758765734627189)
            ·
              refine ⟨7968789701883634287621299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85000423486758765734627189 7968789701883634287621299)
              ·
                refine ⟨11953184552825451431431949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7968789701883634287621299 11953184552825451431431949)
                ·
                  refine ⟨4482444207309544286786981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11953184552825451431431949 4482444207309544286786981)
                  ·
                    refine ⟨840458288870539553772559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4482444207309544286786981 840458288870539553772559)
                    ·
                      rfl

theorem cell22_2455180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_2455180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455180 prefixEnd_2455180 := by exact prefixLift 2455180
  have htrace : WordTrace (prefixWord ++ tailWord_2455180) baseStart_2455180 baseEnd_2455180 := by
    simpa [prefixWord, tailWord_2455180, baseEnd_2455180] using wordTrace_append hprefix tailTrace_2455180
  have hstable : (prefixWord ++ tailWord_2455180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455180).length < 2 ^ (prefixWord ++ tailWord_2455180).sum := by decide
  have hdescent : baseEnd_2455180 < baseStart_2455180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455225 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 4, 4]
def baseStart_2455225 : Nat := 118140960795 + 2455225 * 2 ^ 59
def prefixEnd_2455225 : Nat := 4983230072969 + 3 ^ 40 * 2455225 * 2
def baseEnd_2455225 : Nat := 840473693290174436397421

theorem tailTrace_2455225 : CollatzResearch.WordTrace tailWord_2455225 prefixEnd_2455225 840473693290174436397421 := by
  unfold tailWord_2455225
  simp only [CollatzResearch.WordTrace]
  refine ⟨89549412530146618891415129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59699608353431079260943419 89549412530146618891415129)
  ·
    refine ⟨67162059397609964168561347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89549412530146618891415129 67162059397609964168561347)
    ·
      refine ⟨100743089096414946252842021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67162059397609964168561347 100743089096414946252842021)
      ·
        refine ⟨18889329205577802422407879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100743089096414946252842021 18889329205577802422407879)
        ·
          refine ⟨28333993808366703633611819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18889329205577802422407879 28333993808366703633611819)
          ·
            refine ⟨42500990712550055450417729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28333993808366703633611819 42500990712550055450417729)
            ·
              refine ⟨31875743034412541587813297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42500990712550055450417729 31875743034412541587813297)
              ·
                refine ⟨23906807275809406190859973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31875743034412541587813297 23906807275809406190859973)
                ·
                  refine ⟨4482526364214263660786245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23906807275809406190859973 4482526364214263660786245)
                  ·
                    refine ⟨840473693290174436397421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4482526364214263660786245 840473693290174436397421)
                    ·
                      rfl

theorem cell22_2455225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_2455225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455225 prefixEnd_2455225 := by exact prefixLift 2455225
  have htrace : WordTrace (prefixWord ++ tailWord_2455225) baseStart_2455225 baseEnd_2455225 := by
    simpa [prefixWord, tailWord_2455225, baseEnd_2455225] using wordTrace_append hprefix tailTrace_2455225
  have hstable : (prefixWord ++ tailWord_2455225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455225).length < 2 ^ (prefixWord ++ tailWord_2455225).sum := by decide
  have hdescent : baseEnd_2455225 < baseStart_2455225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455242 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 1, 6]
def baseStart_2455242 : Nat := 118140960795 + 2455242 * 2 ^ 59
def prefixEnd_2455242 : Nat := 4983230072969 + 3 ^ 40 * 2455242 * 2
def baseEnd_2455242 : Nat := 840479512737592058722369

theorem tailTrace_2455242 : CollatzResearch.WordTrace tailWord_2455242 prefixEnd_2455242 840479512737592058722369 := by
  unfold tailWord_2455242
  simp only [CollatzResearch.WordTrace]
  refine ⟨22387508142771257698695995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59700021714056687196522653 22387508142771257698695995)
  ·
    refine ⟨33581262214156886548043993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22387508142771257698695995 33581262214156886548043993)
    ·
      refine ⟨25185946660617664911032995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33581262214156886548043993 25185946660617664911032995)
      ·
        refine ⟨37778919990926497366549493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25185946660617664911032995 37778919990926497366549493)
        ·
          refine ⟨3541773749149359128114015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37778919990926497366549493 3541773749149359128114015)
          ·
            refine ⟨5312660623724038692171023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3541773749149359128114015 5312660623724038692171023)
            ·
              refine ⟨7968990935586058038256535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5312660623724038692171023 7968990935586058038256535)
              ·
                refine ⟨11953486403379087057384803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7968990935586058038256535 11953486403379087057384803)
                ·
                  refine ⟨17930229605068630586077205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11953486403379087057384803 17930229605068630586077205)
                  ·
                    refine ⟨840479512737592058722369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17930229605068630586077205 840479512737592058722369)
                    ·
                      rfl

theorem cell22_2455242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_2455242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455242 prefixEnd_2455242 := by exact prefixLift 2455242
  have htrace : WordTrace (prefixWord ++ tailWord_2455242) baseStart_2455242 baseEnd_2455242 := by
    simpa [prefixWord, tailWord_2455242, baseEnd_2455242] using wordTrace_append hprefix tailTrace_2455242
  have hstable : (prefixWord ++ tailWord_2455242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455242).length < 2 ^ (prefixWord ++ tailWord_2455242).sum := by decide
  have hdescent : baseEnd_2455242 < baseStart_2455242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455261 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_2455261 : Nat := 118140960795 + 2455261 * 2 ^ 59
def prefixEnd_2455261 : Nat := 4983230072969 + 3 ^ 40 * 2455261 * 2
def baseEnd_2455261 : Nat := 840486016825882342497311

theorem tailTrace_2455261 : CollatzResearch.WordTrace tailWord_2455261 prefixEnd_2455261 840486016825882342497311 := by
  unfold tailWord_2455261
  simp only [CollatzResearch.WordTrace]
  refine ⟨89550725558016197039725637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59700483705344131359817091 89550725558016197039725637)
  ·
    refine ⟨16790761042128036944948557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89550725558016197039725637 16790761042128036944948557)
    ·
      refine ⟨6296535390798013854355709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16790761042128036944948557 6296535390798013854355709)
      ·
        refine ⟨2361200771549255195383391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6296535390798013854355709 2361200771549255195383391)
        ·
          refine ⟨3541801157323882793075087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2361200771549255195383391 3541801157323882793075087)
          ·
            refine ⟨5312701735985824189612631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3541801157323882793075087 5312701735985824189612631)
            ·
              refine ⟨7969052603978736284418947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5312701735985824189612631 7969052603978736284418947)
              ·
                refine ⟨11953578905968104426628421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7969052603978736284418947 11953578905968104426628421)
                ·
                  refine ⟨2241296044869019579992829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11953578905968104426628421 2241296044869019579992829)
                  ·
                    refine ⟨840486016825882342497311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2241296044869019579992829 840486016825882342497311)
                    ·
                      rfl

theorem cell22_2455261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_2455261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455261 prefixEnd_2455261 := by exact prefixLift 2455261
  have htrace : WordTrace (prefixWord ++ tailWord_2455261) baseStart_2455261 baseEnd_2455261 := by
    simpa [prefixWord, tailWord_2455261, baseEnd_2455261] using wordTrace_append hprefix tailTrace_2455261
  have hstable : (prefixWord ++ tailWord_2455261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455261).length < 2 ^ (prefixWord ++ tailWord_2455261).sum := by decide
  have hdescent : baseEnd_2455261 < baseStart_2455261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455306 : List Nat := [3, 1, 2, 2, 1, 3, 3, 3, 1, 3]
def baseStart_2455306 : Nat := 118140960795 + 2455306 * 2 ^ 59
def prefixEnd_2455306 : Nat := 4983230072969 + 3 ^ 40 * 2455306 * 2
def baseEnd_2455306 : Nat := 840501421245517225122173

theorem tailTrace_2455306 : CollatzResearch.WordTrace tailWord_2455306 prefixEnd_2455306 840501421245517225122173 := by
  unfold tailWord_2455306
  simp only [CollatzResearch.WordTrace]
  refine ⟨22388091710713292431278443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59701577895235446483409181 22388091710713292431278443)
  ·
    refine ⟨33582137566069938646917665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22388091710713292431278443 33582137566069938646917665)
    ·
      refine ⟨25186603174552453985188249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33582137566069938646917665 25186603174552453985188249)
      ·
        refine ⟨18889952380914340488891187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25186603174552453985188249 18889952380914340488891187)
        ·
          refine ⟨28334928571371510733336781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18889952380914340488891187 28334928571371510733336781)
          ·
            refine ⟨10625598214264316525001293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28334928571371510733336781 10625598214264316525001293)
            ·
              refine ⟨3984599330349118696875485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10625598214264316525001293 3984599330349118696875485)
              ·
                refine ⟨1494224748880919511328307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3984599330349118696875485 1494224748880919511328307)
                ·
                  refine ⟨2241337123321379266992461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494224748880919511328307 2241337123321379266992461)
                  ·
                    refine ⟨840501421245517225122173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2241337123321379266992461 840501421245517225122173)
                    ·
                      rfl

theorem cell22_2455306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_2455306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455306 prefixEnd_2455306 := by exact prefixLift 2455306
  have htrace : WordTrace (prefixWord ++ tailWord_2455306) baseStart_2455306 baseEnd_2455306 := by
    simpa [prefixWord, tailWord_2455306, baseEnd_2455306] using wordTrace_append hprefix tailTrace_2455306
  have hstable : (prefixWord ++ tailWord_2455306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455306).length < 2 ^ (prefixWord ++ tailWord_2455306).sum := by decide
  have hdescent : baseEnd_2455306 < baseStart_2455306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455336 : List Nat := [2, 1, 5, 1, 1, 4, 2, 1, 5]
def baseStart_2455336 : Nat := 118140960795 + 2455336 * 2 ^ 59
def prefixEnd_2455336 : Nat := 4983230072969 + 3 ^ 40 * 2455336 * 2
def baseEnd_2455336 : Nat := 280170563619535715624027

theorem tailTrace_2455336 : CollatzResearch.WordTrace tailWord_2455336 prefixEnd_2455336 280170563619535715624027 := by
  unfold tailWord_2455336
  simp only [CollatzResearch.WordTrace]
  refine ⟨44776730516372242424352931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59702307355162989899137241 44776730516372242424352931)
  ·
    refine ⟨67165095774558363636529397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44776730516372242424352931 67165095774558363636529397)
    ·
      refine ⟨6296727728864846590924631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67165095774558363636529397 6296727728864846590924631)
      ·
        refine ⟨9445091593297269886386947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6296727728864846590924631 9445091593297269886386947)
        ·
          refine ⟨14167637389945904829580421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9445091593297269886386947 14167637389945904829580421)
          ·
            refine ⟨2656432010614857155546329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14167637389945904829580421 2656432010614857155546329)
            ·
              refine ⟨1992324007961142866659747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2656432010614857155546329 1992324007961142866659747)
              ·
                refine ⟨2988486011941714299989621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1992324007961142866659747 2988486011941714299989621)
                ·
                  refine ⟨280170563619535715624027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2988486011941714299989621 280170563619535715624027)
                  ·
                    rfl

theorem cell22_2455336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 5].length) (baseStart_2455336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455336 prefixEnd_2455336 := by exact prefixLift 2455336
  have htrace : WordTrace (prefixWord ++ tailWord_2455336) baseStart_2455336 baseEnd_2455336 := by
    simpa [prefixWord, tailWord_2455336, baseEnd_2455336] using wordTrace_append hprefix tailTrace_2455336
  have hstable : (prefixWord ++ tailWord_2455336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455336).length < 2 ^ (prefixWord ++ tailWord_2455336).sum := by decide
  have hdescent : baseEnd_2455336 < baseStart_2455336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455349 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 3, 4]
def baseStart_2455349 : Nat := 118140960795 + 2455349 * 2 ^ 59
def prefixEnd_2455349 : Nat := 4983230072969 + 3 ^ 40 * 2455349 * 2
def baseEnd_2455349 : Nat := 840516141024279446297041

theorem tailTrace_2455349 : CollatzResearch.WordTrace tailWord_2455349 prefixEnd_2455349 840516141024279446297041 := by
  unfold tailWord_2455349
  simp only [CollatzResearch.WordTrace]
  refine ⟨89553935181697388068929101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59702623454464925379286067 89553935181697388068929101)
  ·
    refine ⟨33582725693136520525848413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89553935181697388068929101 33582725693136520525848413)
    ·
      refine ⟨12593522134926195197193155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33582725693136520525848413 12593522134926195197193155)
      ·
        refine ⟨18890283202389292795789733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12593522134926195197193155 18890283202389292795789733)
        ·
          refine ⟨3541928100447992399210575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18890283202389292795789733 3541928100447992399210575)
          ·
            refine ⟨5312892150671988598815863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3541928100447992399210575 5312892150671988598815863)
            ·
              refine ⟨7969338226007982898223795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5312892150671988598815863 7969338226007982898223795)
              ·
                refine ⟨11954007339011974347335693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7969338226007982898223795 11954007339011974347335693)
                ·
                  refine ⟨4482752752129490380250885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11954007339011974347335693 4482752752129490380250885)
                  ·
                    refine ⟨840516141024279446297041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4482752752129490380250885 840516141024279446297041)
                    ·
                      rfl

theorem cell22_2455349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_2455349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455349 prefixEnd_2455349 := by exact prefixLift 2455349
  have htrace : WordTrace (prefixWord ++ tailWord_2455349) baseStart_2455349 baseEnd_2455349 := by
    simpa [prefixWord, tailWord_2455349, baseEnd_2455349] using wordTrace_append hprefix tailTrace_2455349
  have hstable : (prefixWord ++ tailWord_2455349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455349).length < 2 ^ (prefixWord ++ tailWord_2455349).sum := by decide
  have hdescent : baseEnd_2455349 < baseStart_2455349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455381 : List Nat := [1, 3, 2, 2, 2, 2, 4, 2, 4]
def baseStart_2455381 : Nat := 118140960795 + 2455381 * 2 ^ 59
def prefixEnd_2455381 : Nat := 4983230072969 + 3 ^ 40 * 2455381 * 2
def baseEnd_2455381 : Nat := 280175698426080676498981

theorem tailTrace_2455381 : CollatzResearch.WordTrace tailWord_2455381 prefixEnd_2455381 280175698426080676498981 := by
  unfold tailWord_2455381
  simp only [CollatzResearch.WordTrace]
  refine ⟨89555102317581457534093997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59703401545054305022729331 89555102317581457534093997)
  ·
    refine ⟨33583163369093046575285249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89555102317581457534093997 33583163369093046575285249)
    ·
      refine ⟨25187372526819784931463937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33583163369093046575285249 25187372526819784931463937)
      ·
        refine ⟨18890529395114838698597953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25187372526819784931463937 18890529395114838698597953)
        ·
          refine ⟨14167897046336129023948465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18890529395114838698597953 14167897046336129023948465)
          ·
            refine ⟨10625922784752096767961349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14167897046336129023948465 10625922784752096767961349)
            ·
              refine ⟨1992360522141018143992753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10625922784752096767961349 1992360522141018143992753)
              ·
                refine ⟨1494270391605763607994565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1992360522141018143992753 1494270391605763607994565)
                ·
                  refine ⟨280175698426080676498981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1494270391605763607994565 280175698426080676498981)
                  ·
                    rfl

theorem cell22_2455381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_2455381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455381 prefixEnd_2455381 := by exact prefixLift 2455381
  have htrace : WordTrace (prefixWord ++ tailWord_2455381) baseStart_2455381 baseEnd_2455381 := by
    simpa [prefixWord, tailWord_2455381, baseEnd_2455381] using wordTrace_append hprefix tailTrace_2455381
  have hstable : (prefixWord ++ tailWord_2455381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455381).length < 2 ^ (prefixWord ++ tailWord_2455381).sum := by decide
  have hdescent : baseEnd_2455381 < baseStart_2455381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455392 : List Nat := [2, 1, 1, 3, 3, 2, 3, 7]
def baseStart_2455392 : Nat := 118140960795 + 2455392 * 2 ^ 59
def prefixEnd_2455392 : Nat := 4983230072969 + 3 ^ 40 * 2455392 * 2
def baseEnd_2455392 : Nat := 93392317867004629719101

theorem tailTrace_2455392 : CollatzResearch.WordTrace tailWord_2455392 prefixEnd_2455392 93392317867004629719101 := by
  unfold tailWord_2455392
  simp only [CollatzResearch.WordTrace]
  refine ⟨44777751760270803206372215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59703669013694404275162953 44777751760270803206372215)
  ·
    refine ⟨67166627640406204809558323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44777751760270803206372215 67166627640406204809558323)
    ·
      refine ⟨100749941460609307214337485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67166627640406204809558323 100749941460609307214337485)
      ·
        refine ⟨37781228047728490205376557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100749941460609307214337485 37781228047728490205376557)
        ·
          refine ⟨14167960517898183827016209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37781228047728490205376557 14167960517898183827016209)
          ·
            refine ⟨10625970388423637870262157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14167960517898183827016209 10625970388423637870262157)
            ·
              refine ⟨3984738895658864201348309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10625970388423637870262157 3984738895658864201348309)
              ·
                refine ⟨93392317867004629719101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3984738895658864201348309 93392317867004629719101)
                ·
                  rfl

theorem cell22_2455392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 7].length) (baseStart_2455392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455392 prefixEnd_2455392 := by exact prefixLift 2455392
  have htrace : WordTrace (prefixWord ++ tailWord_2455392) baseStart_2455392 baseEnd_2455392 := by
    simpa [prefixWord, tailWord_2455392, baseEnd_2455392] using wordTrace_append hprefix tailTrace_2455392
  have hstable : (prefixWord ++ tailWord_2455392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455392).length < 2 ^ (prefixWord ++ tailWord_2455392).sum := by decide
  have hdescent : baseEnd_2455392 < baseStart_2455392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455441 : List Nat := [1, 2, 2, 1, 1, 1, 6, 4, 1, 3]
def baseStart_2455441 : Nat := 118140960795 + 2455441 * 2 ^ 59
def prefixEnd_2455441 : Nat := 4983230072969 + 3 ^ 40 * 2455441 * 2
def baseEnd_2455441 : Nat := 840547634504421872996759

theorem tailTrace_2455441 : CollatzResearch.WordTrace tailWord_2455441 prefixEnd_2455441 840547634504421872996759 := by
  unfold tailWord_2455441
  simp only [CollatzResearch.WordTrace]
  refine ⟨89557290697364087781278177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59704860464909391854185451 89557290697364087781278177)
  ·
    refine ⟨67167968023023065835958633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89557290697364087781278177 67167968023023065835958633)
    ·
      refine ⟨50375976017267299376968975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67167968023023065835958633 50375976017267299376968975)
      ·
        refine ⟨75563964025900949065453463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50375976017267299376968975 75563964025900949065453463)
        ·
          refine ⟨113345946038851423598180195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75563964025900949065453463 113345946038851423598180195)
          ·
            refine ⟨170018919058277135397270293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113345946038851423598180195 170018919058277135397270293)
            ·
              refine ⟨7969636830856740721747045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 170018919058277135397270293 7969636830856740721747045)
              ·
                refine ⟨1494306905785638885327571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7969636830856740721747045 1494306905785638885327571)
                ·
                  refine ⟨2241460358678458327991357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494306905785638885327571 2241460358678458327991357)
                  ·
                    refine ⟨840547634504421872996759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2241460358678458327991357 840547634504421872996759)
                    ·
                      rfl

theorem cell22_2455441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_2455441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455441 prefixEnd_2455441 := by exact prefixLift 2455441
  have htrace : WordTrace (prefixWord ++ tailWord_2455441) baseStart_2455441 baseEnd_2455441 := by
    simpa [prefixWord, tailWord_2455441, baseEnd_2455441] using wordTrace_append hprefix tailTrace_2455441
  have hstable : (prefixWord ++ tailWord_2455441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455441).length < 2 ^ (prefixWord ++ tailWord_2455441).sum := by decide
  have hdescent : baseEnd_2455441 < baseStart_2455441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455497 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 3, 5]
def baseStart_2455497 : Nat := 118140960795 + 2455497 * 2 ^ 59
def prefixEnd_2455497 : Nat := 4983230072969 + 3 ^ 40 * 2455497 * 2
def baseEnd_2455497 : Nat := 840566804448856393596587

theorem tailTrace_2455497 : CollatzResearch.WordTrace tailWord_2455497 prefixEnd_2455497 840566804448856393596587 := by
  unfold tailWord_2455497
  simp only [CollatzResearch.WordTrace]
  refine ⟨89559333185161209345316745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59706222123440806230211163 89559333185161209345316745)
  ·
    refine ⟨67169499888870907008987559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89559333185161209345316745 67169499888870907008987559)
    ·
      refine ⟨100754249833306360513481339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67169499888870907008987559 100754249833306360513481339)
      ·
        refine ⟨151131374749959540770222009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100754249833306360513481339 151131374749959540770222009)
        ·
          refine ⟨113348531062469655577666507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151131374749959540770222009 113348531062469655577666507)
          ·
            refine ⟨170022796593704483366499761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113348531062469655577666507 170022796593704483366499761)
            ·
              refine ⟨127517097445278362524874821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170022796593704483366499761 127517097445278362524874821)
              ·
                refine ⟨23909455770989692973414029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127517097445278362524874821 23909455770989692973414029)
                ·
                  refine ⟨8966045914121134865030261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23909455770989692973414029 8966045914121134865030261)
                  ·
                    refine ⟨840566804448856393596587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8966045914121134865030261 840566804448856393596587)
                    ·
                      rfl

theorem cell22_2455497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_2455497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455497 prefixEnd_2455497 := by exact prefixLift 2455497
  have htrace : WordTrace (prefixWord ++ tailWord_2455497) baseStart_2455497 baseEnd_2455497 := by
    simpa [prefixWord, tailWord_2455497, baseEnd_2455497] using wordTrace_append hprefix tailTrace_2455497
  have hstable : (prefixWord ++ tailWord_2455497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455497).length < 2 ^ (prefixWord ++ tailWord_2455497).sum := by decide
  have hdescent : baseEnd_2455497 < baseStart_2455497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455550 : List Nat := [4, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_2455550 : Nat := 118140960795 + 2455550 * 2 ^ 59
def prefixEnd_2455550 : Nat := 4983230072969 + 3 ^ 40 * 2455550 * 2
def baseEnd_2455550 : Nat := 280194982477327307340475

theorem tailTrace_2455550 : CollatzResearch.WordTrace tailWord_2455550 prefixEnd_2455550 280194982477327307340475 := by
  unfold tailWord_2455550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11195158281746149924624513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59707510835979466264664069 11195158281746149924624513)
  ·
    refine ⟨8396368711309612443468385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11195158281746149924624513 8396368711309612443468385)
    ·
      refine ⟨6297276533482209332601289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8396368711309612443468385 6297276533482209332601289)
      ·
        refine ⟨4722957400111656999450967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6297276533482209332601289 4722957400111656999450967)
        ·
          refine ⟨7084436100167485499176451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4722957400111656999450967 7084436100167485499176451)
          ·
            refine ⟨10626654150251228248764677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7084436100167485499176451 10626654150251228248764677)
            ·
              refine ⟨1992497653172105296643377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10626654150251228248764677 1992497653172105296643377)
              ·
                refine ⟨1494373239879078972482533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1992497653172105296643377 1494373239879078972482533)
                ·
                  refine ⟨280194982477327307340475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1494373239879078972482533 280194982477327307340475)
                  ·
                    rfl

theorem cell22_2455550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_2455550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455550 prefixEnd_2455550 := by exact prefixLift 2455550
  have htrace : WordTrace (prefixWord ++ tailWord_2455550) baseStart_2455550 baseEnd_2455550 := by
    simpa [prefixWord, tailWord_2455550, baseEnd_2455550] using wordTrace_append hprefix tailTrace_2455550
  have hstable : (prefixWord ++ tailWord_2455550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455550).length < 2 ^ (prefixWord ++ tailWord_2455550).sum := by decide
  have hdescent : baseEnd_2455550 < baseStart_2455550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455576 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 3, 3]
def baseStart_2455576 : Nat := 118140960795 + 2455576 * 2 ^ 59
def prefixEnd_2455576 : Nat := 4983230072969 + 3 ^ 40 * 2455576 * 2
def baseEnd_2455576 : Nat := 840593847763326520871345

theorem tailTrace_2455576 : CollatzResearch.WordTrace tailWord_2455576 prefixEnd_2455576 840593847763326520871345 := by
  unfold tailWord_2455576
  simp only [CollatzResearch.WordTrace]
  refine ⟨44781107275937502918721291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59708143034583337224961721 44781107275937502918721291)
  ·
    refine ⟨67171660913906254378081937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44781107275937502918721291 67171660913906254378081937)
    ·
      refine ⟨50378745685429690783561453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67171660913906254378081937 50378745685429690783561453)
      ·
        refine ⟨18892029632036134043835545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50378745685429690783561453 18892029632036134043835545)
        ·
          refine ⟨14169022224027100532876659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18892029632036134043835545 14169022224027100532876659)
          ·
            refine ⟨21253533336040650799314989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14169022224027100532876659 21253533336040650799314989)
            ·
              refine ⟨7970075001015244049743121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21253533336040650799314989 7970075001015244049743121)
              ·
                refine ⟨5977556250761433037307341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7970075001015244049743121 5977556250761433037307341)
                ·
                  refine ⟨2241583594035537388990253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5977556250761433037307341 2241583594035537388990253)
                  ·
                    refine ⟨840593847763326520871345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2241583594035537388990253 840593847763326520871345)
                    ·
                      rfl

theorem cell22_2455576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_2455576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455576 prefixEnd_2455576 := by exact prefixLift 2455576
  have htrace : WordTrace (prefixWord ++ tailWord_2455576) baseStart_2455576 baseEnd_2455576 := by
    simpa [prefixWord, tailWord_2455576, baseEnd_2455576] using wordTrace_append hprefix tailTrace_2455576
  have hstable : (prefixWord ++ tailWord_2455576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455576).length < 2 ^ (prefixWord ++ tailWord_2455576).sum := by decide
  have hdescent : baseEnd_2455576 < baseStart_2455576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455606 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_2455606 : Nat := 118140960795 + 2455606 * 2 ^ 59
def prefixEnd_2455606 : Nat := 4983230072969 + 3 ^ 40 * 2455606 * 2
def baseEnd_2455606 : Nat := 280201372458805480873751

theorem tailTrace_2455606 : CollatzResearch.WordTrace tailWord_2455606 prefixEnd_2455606 280201372458805480873751 := by
  unfold tailWord_2455606
  simp only [CollatzResearch.WordTrace]
  refine ⟨5597706796360395060064667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59708872494510880640689781 5597706796360395060064667)
  ·
    refine ⟨8396560194540592590097001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5597706796360395060064667 8396560194540592590097001)
    ·
      refine ⟨6297420145905444442572751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8396560194540592590097001 6297420145905444442572751)
      ·
        refine ⟨9446130218858166663859127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6297420145905444442572751 9446130218858166663859127)
        ·
          refine ⟨14169195328287249995788691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9446130218858166663859127 14169195328287249995788691)
          ·
            refine ⟨21253792992430874993683037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14169195328287249995788691 21253792992430874993683037)
            ·
              refine ⟨7970172372161578122631139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21253792992430874993683037 7970172372161578122631139)
              ·
                refine ⟨11955258558242367183946709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7970172372161578122631139 11955258558242367183946709)
                ·
                  refine ⟨280201372458805480873751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11955258558242367183946709 280201372458805480873751)
                  ·
                    rfl

theorem cell22_2455606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_2455606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455606 prefixEnd_2455606 := by exact prefixLift 2455606
  have htrace : WordTrace (prefixWord ++ tailWord_2455606) baseStart_2455606 baseEnd_2455606 := by
    simpa [prefixWord, tailWord_2455606, baseEnd_2455606] using wordTrace_append hprefix tailTrace_2455606
  have hstable : (prefixWord ++ tailWord_2455606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455606).length < 2 ^ (prefixWord ++ tailWord_2455606).sum := by decide
  have hdescent : baseEnd_2455606 < baseStart_2455606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455619 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 3, 4]
def baseStart_2455619 : Nat := 118140960795 + 2455619 * 2 ^ 59
def prefixEnd_2455619 : Nat := 4983230072969 + 3 ^ 40 * 2455619 * 2
def baseEnd_2455619 : Nat := 840608567542088742046213

theorem tailTrace_2455619 : CollatzResearch.WordTrace tailWord_2455619 prefixEnd_2455619 840608567542088742046213 := by
  unfold tailWord_2455619
  simp only [CollatzResearch.WordTrace]
  refine ⟨89563782890719224181257911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59709188593812816120838607 89563782890719224181257911)
  ·
    refine ⟨134345674336078836271886867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89563782890719224181257911 134345674336078836271886867)
    ·
      refine ⟨201518511504118254407830301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134345674336078836271886867 201518511504118254407830301)
      ·
        refine ⟨75569441814044345402936363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201518511504118254407830301 75569441814044345402936363)
        ·
          refine ⟨113354162721066518104404545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75569441814044345402936363 113354162721066518104404545)
          ·
            refine ⟨85015622040799888578303409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113354162721066518104404545 85015622040799888578303409)
            ·
              refine ⟨63761716530599916433727557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85015622040799888578303409 63761716530599916433727557)
              ·
                refine ⟨11955321849487484331323917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63761716530599916433727557 11955321849487484331323917)
                ·
                  refine ⟨4483245693557806624246469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11955321849487484331323917 4483245693557806624246469)
                  ·
                    refine ⟨840608567542088742046213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4483245693557806624246469 840608567542088742046213)
                    ·
                      rfl

theorem cell22_2455619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 4].length) (baseStart_2455619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455619 prefixEnd_2455619 := by exact prefixLift 2455619
  have htrace : WordTrace (prefixWord ++ tailWord_2455619) baseStart_2455619 baseEnd_2455619 := by
    simpa [prefixWord, tailWord_2455619, baseEnd_2455619] using wordTrace_append hprefix tailTrace_2455619
  have hstable : (prefixWord ++ tailWord_2455619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455619).length < 2 ^ (prefixWord ++ tailWord_2455619).sum := by decide
  have hdescent : baseEnd_2455619 < baseStart_2455619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455649 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 3, 5]
def baseStart_2455649 : Nat := 118140960795 + 2455649 * 2 ^ 59
def prefixEnd_2455649 : Nat := 4983230072969 + 3 ^ 40 * 2455649 * 2
def baseEnd_2455649 : Nat := 840618837155178663796121

theorem tailTrace_2455649 : CollatzResearch.WordTrace tailWord_2455649 prefixEnd_2455649 840618837155178663796121 := by
  unfold tailWord_2455649
  simp only [CollatzResearch.WordTrace]
  refine ⟨89564877080610539304850001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59709918053740359536566667 89564877080610539304850001)
  ·
    refine ⟨67173657810457904478637501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89564877080610539304850001 67173657810457904478637501)
    ·
      refine ⟨25190121678921714179489063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67173657810457904478637501 25190121678921714179489063)
      ·
        refine ⟨37785182518382571269233595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25190121678921714179489063 37785182518382571269233595)
        ·
          refine ⟨56677773777573856903850393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37785182518382571269233595 56677773777573856903850393)
          ·
            refine ⟨42508330333180392677887795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56677773777573856903850393 42508330333180392677887795)
            ·
              refine ⟨63762495499770589016831693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42508330333180392677887795 63762495499770589016831693)
              ·
                refine ⟨23910935812413970881311885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63762495499770589016831693 23910935812413970881311885)
                ·
                  refine ⟨8966600929655239080491957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23910935812413970881311885 8966600929655239080491957)
                  ·
                    refine ⟨840618837155178663796121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8966600929655239080491957 840618837155178663796121)
                    ·
                      rfl

theorem cell22_2455649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_2455649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455649 prefixEnd_2455649 := by exact prefixLift 2455649
  have htrace : WordTrace (prefixWord ++ tailWord_2455649) baseStart_2455649 baseEnd_2455649 := by
    simpa [prefixWord, tailWord_2455649, baseEnd_2455649] using wordTrace_append hprefix tailTrace_2455649
  have hstable : (prefixWord ++ tailWord_2455649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455649).length < 2 ^ (prefixWord ++ tailWord_2455649).sum := by decide
  have hdescent : baseEnd_2455649 < baseStart_2455649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455683 : List Nat := [1, 1, 1, 3, 3, 4, 1, 3, 2, 3]
def baseStart_2455683 : Nat := 118140960795 + 2455683 * 2 ^ 59
def prefixEnd_2455683 : Nat := 4983230072969 + 3 ^ 40 * 2455683 * 2
def baseEnd_2455683 : Nat := 840630476050013908446017

theorem tailTrace_2455683 : CollatzResearch.WordTrace tailWord_2455683 prefixEnd_2455683 840630476050013908446017 := by
  unfold tailWord_2455683
  simp only [CollatzResearch.WordTrace]
  refine ⟨89566117162487363111587703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59710744774991575407725135 89566117162487363111587703)
  ·
    refine ⟨134349175743731044667381555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89566117162487363111587703 134349175743731044667381555)
    ·
      refine ⟨201523763615596567001072333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134349175743731044667381555 201523763615596567001072333)
      ·
        refine ⟨75571411355848712625402125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201523763615596567001072333 75571411355848712625402125)
        ·
          refine ⟨28339279258443267234525797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75571411355848712625402125 28339279258443267234525797)
          ·
            refine ⟨5313614860958112606473587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28339279258443267234525797 5313614860958112606473587)
            ·
              refine ⟨7970422291437168909710381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5313614860958112606473587 7970422291437168909710381)
              ·
                refine ⟨2988908359288938341141393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7970422291437168909710381 2988908359288938341141393)
                ·
                  refine ⟨2241681269466703755856045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2988908359288938341141393 2241681269466703755856045)
                  ·
                    refine ⟨840630476050013908446017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2241681269466703755856045 840630476050013908446017)
                    ·
                      rfl

theorem cell22_2455683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 3].length) (baseStart_2455683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455683 prefixEnd_2455683 := by exact prefixLift 2455683
  have htrace : WordTrace (prefixWord ++ tailWord_2455683) baseStart_2455683 baseEnd_2455683 := by
    simpa [prefixWord, tailWord_2455683, baseEnd_2455683] using wordTrace_append hprefix tailTrace_2455683
  have hstable : (prefixWord ++ tailWord_2455683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455683).length < 2 ^ (prefixWord ++ tailWord_2455683).sum := by decide
  have hdescent : baseEnd_2455683 < baseStart_2455683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455698 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2455698 : Nat := 118140960795 + 2455698 * 2 ^ 59
def prefixEnd_2455698 : Nat := 4983230072969 + 3 ^ 40 * 2455698 * 2
def baseEnd_2455698 : Nat := 840635610856558869320971

theorem tailTrace_2455698 : CollatzResearch.WordTrace tailWord_2455698 prefixEnd_2455698 840635610856558869320971 := by
  unfold tailWord_2455698
  simp only [CollatzResearch.WordTrace]
  refine ⟨22391666064358255168345937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59711109504955347115589165 22391666064358255168345937)
  ·
    refine ⟨16793749548268691376259453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22391666064358255168345937 16793749548268691376259453)
    ·
      refine ⟨6297656080600759266097295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16793749548268691376259453 6297656080600759266097295)
      ·
        refine ⟨9446484120901138899145943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6297656080600759266097295 9446484120901138899145943)
        ·
          refine ⟨14169726181351708348718915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9446484120901138899145943 14169726181351708348718915)
          ·
            refine ⟨21254589272027562523078373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14169726181351708348718915 21254589272027562523078373)
            ·
              refine ⟨3985235488505167973077195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21254589272027562523078373 3985235488505167973077195)
              ·
                refine ⟨5977853232757751959615793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3985235488505167973077195 5977853232757751959615793)
                ·
                  refine ⟨4483389924568313969711845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5977853232757751959615793 4483389924568313969711845)
                  ·
                    refine ⟨840635610856558869320971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4483389924568313969711845 840635610856558869320971)
                    ·
                      rfl

theorem cell22_2455698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2455698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455698 prefixEnd_2455698 := by exact prefixLift 2455698
  have htrace : WordTrace (prefixWord ++ tailWord_2455698) baseStart_2455698 baseEnd_2455698 := by
    simpa [prefixWord, tailWord_2455698, baseEnd_2455698] using wordTrace_append hprefix tailTrace_2455698
  have hstable : (prefixWord ++ tailWord_2455698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455698).length < 2 ^ (prefixWord ++ tailWord_2455698).sum := by decide
  have hdescent : baseEnd_2455698 < baseStart_2455698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455700 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_2455700 : Nat := 118140960795 + 2455700 * 2 ^ 59
def prefixEnd_2455700 : Nat := 4983230072969 + 3 ^ 40 * 2455700 * 2
def baseEnd_2455700 : Nat := 840636295497431530770965

theorem tailTrace_2455700 : CollatzResearch.WordTrace tailWord_2455700 prefixEnd_2455700 840636295497431530770965 := by
  unfold tailWord_2455700
  simp only [CollatzResearch.WordTrace]
  refine ⟨44783368601712887507478277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59711158135617183343304369 44783368601712887507478277)
  ·
    refine ⟨8396881612821166407652177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44783368601712887507478277 8396881612821166407652177)
    ·
      refine ⟨6297661209615874805739133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8396881612821166407652177 6297661209615874805739133)
      ·
        refine ⟨2361622953605953052152175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6297661209615874805739133 2361622953605953052152175)
        ·
          refine ⟨3542434430408929578228263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2361622953605953052152175 3542434430408929578228263)
          ·
            refine ⟨5313651645613394367342395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3542434430408929578228263 5313651645613394367342395)
            ·
              refine ⟨7970477468420091551013593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5313651645613394367342395 7970477468420091551013593)
              ·
                refine ⟨5977858101315068663260195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7970477468420091551013593 5977858101315068663260195)
                ·
                  refine ⟨8966787151972602994890293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5977858101315068663260195 8966787151972602994890293)
                  ·
                    refine ⟨840636295497431530770965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8966787151972602994890293 840636295497431530770965)
                    ·
                      rfl

theorem cell22_2455700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_2455700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455700 prefixEnd_2455700 := by exact prefixLift 2455700
  have htrace : WordTrace (prefixWord ++ tailWord_2455700) baseStart_2455700 baseEnd_2455700 := by
    simpa [prefixWord, tailWord_2455700, baseEnd_2455700] using wordTrace_append hprefix tailTrace_2455700
  have hstable : (prefixWord ++ tailWord_2455700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455700).length < 2 ^ (prefixWord ++ tailWord_2455700).sum := by decide
  have hdescent : baseEnd_2455700 < baseStart_2455700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455719 : List Nat := [1, 1, 6, 2, 3, 1, 2, 2, 4]
def baseStart_2455719 : Nat := 118140960795 + 2455719 * 2 ^ 59
def prefixEnd_2455719 : Nat := 4983230072969 + 3 ^ 40 * 2455719 * 2
def baseEnd_2455719 : Nat := 280214266528573938181969

theorem tailTrace_2455719 : CollatzResearch.WordTrace tailWord_2455719 prefixEnd_2455719 280214266528573938181969 := by
  unfold tailWord_2455719
  simp only [CollatzResearch.WordTrace]
  refine ⟨89567430190356941259898211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59711620126904627506598807 89567430190356941259898211)
  ·
    refine ⟨134351145285535411889847317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89567430190356941259898211 134351145285535411889847317)
    ·
      refine ⟨6297709935259472432336593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 134351145285535411889847317 6297709935259472432336593)
      ·
        refine ⟨4723282451444604324252445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6297709935259472432336593 4723282451444604324252445)
        ·
          refine ⟨1771230919291726621594667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4723282451444604324252445 1771230919291726621594667)
          ·
            refine ⟨2656846378937589932392001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771230919291726621594667 2656846378937589932392001)
            ·
              refine ⟨1992634784203192449294001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2656846378937589932392001 1992634784203192449294001)
              ·
                refine ⟨1494476088152394336970501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1992634784203192449294001 1494476088152394336970501)
                ·
                  refine ⟨280214266528573938181969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1494476088152394336970501 280214266528573938181969)
                  ·
                    rfl

theorem cell22_2455719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 4].length) (baseStart_2455719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455719 prefixEnd_2455719 := by exact prefixLift 2455719
  have htrace : WordTrace (prefixWord ++ tailWord_2455719) baseStart_2455719 baseEnd_2455719 := by
    simpa [prefixWord, tailWord_2455719, baseEnd_2455719] using wordTrace_append hprefix tailTrace_2455719
  have hstable : (prefixWord ++ tailWord_2455719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455719).length < 2 ^ (prefixWord ++ tailWord_2455719).sum := by decide
  have hdescent : baseEnd_2455719 < baseStart_2455719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455724 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 11]
def baseStart_2455724 : Nat := 118140960795 + 2455724 * 2 ^ 59
def prefixEnd_2455724 : Nat := 4983230072969 + 3 ^ 40 * 2455724 * 2
def baseEnd_2455724 : Nat := 280214837062634489390297

theorem tailTrace_2455724 : CollatzResearch.WordTrace tailWord_2455724 prefixEnd_2455724 280214837062634489390297 := by
  unfold tailWord_2455724
  simp only [CollatzResearch.WordTrace]
  refine ⟨44783806277669413556915113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59711741703559218075886817 44783806277669413556915113)
  ·
    refine ⟨33587854708252060167686335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44783806277669413556915113 33587854708252060167686335)
    ·
      refine ⟨50381782062378090251529503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33587854708252060167686335 50381782062378090251529503)
      ·
        refine ⟨75572673093567135377294255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50381782062378090251529503 75572673093567135377294255)
        ·
          refine ⟨113359009640350703065941383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75572673093567135377294255 113359009640350703065941383)
          ·
            refine ⟨170038514460526054598912075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113359009640350703065941383 170038514460526054598912075)
            ·
              refine ⟨255057771690789081898368113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170038514460526054598912075 255057771690789081898368113)
              ·
                refine ⟨191293328768091811423776085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255057771690789081898368113 191293328768091811423776085)
                ·
                  refine ⟨280214837062634489390297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 191293328768091811423776085 280214837062634489390297)
                  ·
                    rfl

theorem cell22_2455724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_2455724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455724 prefixEnd_2455724 := by exact prefixLift 2455724
  have htrace : WordTrace (prefixWord ++ tailWord_2455724) baseStart_2455724 baseEnd_2455724 := by
    simpa [prefixWord, tailWord_2455724, baseEnd_2455724] using wordTrace_append hprefix tailTrace_2455724
  have hstable : (prefixWord ++ tailWord_2455724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455724).length < 2 ^ (prefixWord ++ tailWord_2455724).sum := by decide
  have hdescent : baseEnd_2455724 < baseStart_2455724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455762 : List Nat := [3, 2, 2, 2, 1, 3, 2, 3, 1, 3]
def baseStart_2455762 : Nat := 118140960795 + 2455762 * 2 ^ 59
def prefixEnd_2455762 : Nat := 4983230072969 + 3 ^ 40 * 2455762 * 2
def baseEnd_2455762 : Nat := 840657519364484035720775

theorem tailTrace_2455762 : CollatzResearch.WordTrace tailWord_2455762 prefixEnd_2455762 840657519364484035720775 := by
  unfold tailWord_2455762
  simp only [CollatzResearch.WordTrace]
  refine ⟨22392249632300289900928385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59712665686134106402475693 22392249632300289900928385)
  ·
    refine ⟨16794187224225217425696289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22392249632300289900928385 16794187224225217425696289)
    ·
      refine ⟨12595640418168913069272217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16794187224225217425696289 12595640418168913069272217)
      ·
        refine ⟨9446730313626684801954163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12595640418168913069272217 9446730313626684801954163)
        ·
          refine ⟨14170095470440027202931245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9446730313626684801954163 14170095470440027202931245)
          ·
            refine ⟨5313785801415010201099217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14170095470440027202931245 5313785801415010201099217)
            ·
              refine ⟨3985339351061257650824413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5313785801415010201099217 3985339351061257650824413)
              ·
                refine ⟨1494502256647971619059155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3985339351061257650824413 1494502256647971619059155)
                ·
                  refine ⟨2241753384971957428588733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494502256647971619059155 2241753384971957428588733)
                  ·
                    refine ⟨840657519364484035720775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2241753384971957428588733 840657519364484035720775)
                    ·
                      rfl

theorem cell22_2455762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_2455762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455762 prefixEnd_2455762 := by exact prefixLift 2455762
  have htrace : WordTrace (prefixWord ++ tailWord_2455762) baseStart_2455762 baseEnd_2455762 := by
    simpa [prefixWord, tailWord_2455762, baseEnd_2455762] using wordTrace_append hprefix tailTrace_2455762
  have hstable : (prefixWord ++ tailWord_2455762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455762).length < 2 ^ (prefixWord ++ tailWord_2455762).sum := by decide
  have hdescent : baseEnd_2455762 < baseStart_2455762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455773 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2455773 : Nat := 118140960795 + 2455773 * 2 ^ 59
def prefixEnd_2455773 : Nat := 4983230072969 + 3 ^ 40 * 2455773 * 2
def baseEnd_2455773 : Nat := 840661284889283673695741

theorem tailTrace_2455773 : CollatzResearch.WordTrace tailWord_2455773 prefixEnd_2455773 840661284889283673695741 := by
  unfold tailWord_2455773
  simp only [CollatzResearch.WordTrace]
  refine ⟨89569399732161308482363973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59712933154774205654909315 89569399732161308482363973)
  ·
    refine ⟨16794262449780245340443245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89569399732161308482363973 16794262449780245340443245)
    ·
      refine ⟨6297848418667592002666217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16794262449780245340443245 6297848418667592002666217)
      ·
        refine ⟨4723386314000694001999663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6297848418667592002666217 4723386314000694001999663)
        ·
          refine ⟨7085079471001041002999495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4723386314000694001999663 7085079471001041002999495)
          ·
            refine ⟨10627619206501561504499243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7085079471001041002999495 10627619206501561504499243)
            ·
              refine ⟨15941428809752342256748865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10627619206501561504499243 15941428809752342256748865)
              ·
                refine ⟨11956071607314256692561649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15941428809752342256748865 11956071607314256692561649)
                ·
                  refine ⟨8967053705485692519421237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11956071607314256692561649 8967053705485692519421237)
                  ·
                    refine ⟨840661284889283673695741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8967053705485692519421237 840661284889283673695741)
                    ·
                      rfl

theorem cell22_2455773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2455773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455773 prefixEnd_2455773 := by exact prefixLift 2455773
  have htrace : WordTrace (prefixWord ++ tailWord_2455773) baseStart_2455773 baseEnd_2455773 := by
    simpa [prefixWord, tailWord_2455773, baseEnd_2455773] using wordTrace_append hprefix tailTrace_2455773
  have hstable : (prefixWord ++ tailWord_2455773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455773).length < 2 ^ (prefixWord ++ tailWord_2455773).sum := by decide
  have hdescent : baseEnd_2455773 < baseStart_2455773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455801 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 1, 5]
def baseStart_2455801 : Nat := 118140960795 + 2455801 * 2 ^ 59
def prefixEnd_2455801 : Nat := 4983230072969 + 3 ^ 40 * 2455801 * 2
def baseEnd_2455801 : Nat := 840670869861500933995655

theorem tailTrace_2455801 : CollatzResearch.WordTrace tailWord_2455801 prefixEnd_2455801 840670869861500933995655 := by
  unfold tailWord_2455801
  simp only [CollatzResearch.WordTrace]
  refine ⟨89570420976059869264383257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59713613984039912842922171 89570420976059869264383257)
  ·
    refine ⟨67177815732044901948287443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89570420976059869264383257 67177815732044901948287443)
    ·
      refine ⟨100766723598067352922431165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67177815732044901948287443 100766723598067352922431165)
      ·
        refine ⟨37787521349275257345911687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100766723598067352922431165 37787521349275257345911687)
        ·
          refine ⟨56681282023912886018867531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37787521349275257345911687 56681282023912886018867531)
          ·
            refine ⟨85021923035869329028301297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56681282023912886018867531 85021923035869329028301297)
            ·
              refine ⟨63766442276901996771225973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85021923035869329028301297 63766442276901996771225973)
              ·
                refine ⟨5978103963459562197302435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63766442276901996771225973 5978103963459562197302435)
                ·
                  refine ⟨8967155945189343295953653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5978103963459562197302435 8967155945189343295953653)
                  ·
                    refine ⟨840670869861500933995655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8967155945189343295953653 840670869861500933995655)
                    ·
                      rfl

theorem cell22_2455801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_2455801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455801 prefixEnd_2455801 := by exact prefixLift 2455801
  have htrace : WordTrace (prefixWord ++ tailWord_2455801) baseStart_2455801 baseEnd_2455801 := by
    simpa [prefixWord, tailWord_2455801, baseEnd_2455801] using wordTrace_append hprefix tailTrace_2455801
  have hstable : (prefixWord ++ tailWord_2455801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455801).length < 2 ^ (prefixWord ++ tailWord_2455801).sum := by decide
  have hdescent : baseEnd_2455801 < baseStart_2455801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455818 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 4, 3]
def baseStart_2455818 : Nat := 118140960795 + 2455818 * 2 ^ 59
def prefixEnd_2455818 : Nat := 4983230072969 + 3 ^ 40 * 2455818 * 2
def baseEnd_2455818 : Nat := 840676689308918556320603

theorem tailTrace_2455818 : CollatzResearch.WordTrace tailWord_2455818 prefixEnd_2455818 840676689308918556320603 := by
  unfold tailWord_2455818
  simp only [CollatzResearch.WordTrace]
  refine ⟨22392760254249570291938027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59714027344665520778501405 22392760254249570291938027)
  ·
    refine ⟨33589140381374355437907041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22392760254249570291938027 33589140381374355437907041)
    ·
      refine ⟨25191855286030766578430281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33589140381374355437907041 25191855286030766578430281)
      ·
        refine ⟨18893891464523074933822711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25191855286030766578430281 18893891464523074933822711)
        ·
          refine ⟨28340837196784612400734067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18893891464523074933822711 28340837196784612400734067)
          ·
            refine ⟨42511255795176918601101101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28340837196784612400734067 42511255795176918601101101)
            ·
              refine ⟨15941720923191344475412913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42511255795176918601101101 15941720923191344475412913)
              ·
                refine ⟨11956290692393508356559685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15941720923191344475412913 11956290692393508356559685)
                ·
                  refine ⟨2241804504823782816854941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11956290692393508356559685 2241804504823782816854941)
                  ·
                    refine ⟨840676689308918556320603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2241804504823782816854941 840676689308918556320603)
                    ·
                      rfl

theorem cell22_2455818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_2455818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455818 prefixEnd_2455818 := by exact prefixLift 2455818
  have htrace : WordTrace (prefixWord ++ tailWord_2455818) baseStart_2455818 baseEnd_2455818 := by
    simpa [prefixWord, tailWord_2455818, baseEnd_2455818] using wordTrace_append hprefix tailTrace_2455818
  have hstable : (prefixWord ++ tailWord_2455818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455818).length < 2 ^ (prefixWord ++ tailWord_2455818).sum := by decide
  have hdescent : baseEnd_2455818 < baseStart_2455818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455831 : List Nat := [1, 1, 3, 4, 1, 2, 10]
def baseStart_2455831 : Nat := 118140960795 + 2455831 * 2 ^ 59
def prefixEnd_2455831 : Nat := 4983230072969 + 3 ^ 40 * 2455831 * 2
def baseEnd_2455831 : Nat := 31136338499058920583169

theorem tailTrace_2455831 : CollatzResearch.WordTrace tailWord_2455831 prefixEnd_2455831 31136338499058920583169 := by
  unfold tailWord_2455831
  simp only [CollatzResearch.WordTrace]
  refine ⟨89571515165951184387975347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59714343443967456258650231 89571515165951184387975347)
  ·
    refine ⟨134357272748926776581963021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89571515165951184387975347 134357272748926776581963021)
    ·
      refine ⟨50383977280847541218236133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134357272748926776581963021 50383977280847541218236133)
      ·
        refine ⟨9446995740158913978419275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50383977280847541218236133 9446995740158913978419275)
        ·
          refine ⟨14170493610238370967628913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9446995740158913978419275 14170493610238370967628913)
          ·
            refine ⟨10627870207678778225721685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14170493610238370967628913 10627870207678778225721685)
            ·
              refine ⟨31136338499058920583169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10627870207678778225721685 31136338499058920583169)
              ·
                rfl

theorem cell22_2455831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 10].length) (baseStart_2455831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455831 prefixEnd_2455831 := by exact prefixLift 2455831
  have htrace : WordTrace (prefixWord ++ tailWord_2455831) baseStart_2455831 baseEnd_2455831 := by
    simpa [prefixWord, tailWord_2455831, baseEnd_2455831] using wordTrace_append hprefix tailTrace_2455831
  have hstable : (prefixWord ++ tailWord_2455831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455831).length < 2 ^ (prefixWord ++ tailWord_2455831).sum := by decide
  have hdescent : baseEnd_2455831 < baseStart_2455831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455837 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 6]
def baseStart_2455837 : Nat := 118140960795 + 2455837 * 2 ^ 59
def prefixEnd_2455837 : Nat := 4983230072969 + 3 ^ 40 * 2455837 * 2
def baseEnd_2455837 : Nat := 280227731132402946698515

theorem tailTrace_2455837 : CollatzResearch.WordTrace tailWord_2455837 prefixEnd_2455837 280227731132402946698515 := by
  unfold tailWord_2455837
  simp only [CollatzResearch.WordTrace]
  refine ⟨89571734003929447412693765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59714489335952964941795843 89571734003929447412693765)
  ·
    refine ⟨16794700125736771389880081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89571734003929447412693765 16794700125736771389880081)
    ·
      refine ⟨12596025094302578542410061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16794700125736771389880081 12596025094302578542410061)
      ·
        refine ⟨4723509410363466953403773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12596025094302578542410061 4723509410363466953403773)
        ·
          refine ⟨1771316028886300107526415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4723509410363466953403773 1771316028886300107526415)
          ·
            refine ⟨2656974043329450161289623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771316028886300107526415 2656974043329450161289623)
            ·
              refine ⟨3985461064994175241934435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2656974043329450161289623 3985461064994175241934435)
              ·
                refine ⟨5978191597491262862901653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3985461064994175241934435 5978191597491262862901653)
                ·
                  refine ⟨280227731132402946698515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5978191597491262862901653 280227731132402946698515)
                  ·
                    rfl

theorem cell22_2455837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_2455837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455837 prefixEnd_2455837 := by exact prefixLift 2455837
  have htrace : WordTrace (prefixWord ++ tailWord_2455837) baseStart_2455837 baseEnd_2455837 := by
    simpa [prefixWord, tailWord_2455837, baseEnd_2455837] using wordTrace_append hprefix tailTrace_2455837
  have hstable : (prefixWord ++ tailWord_2455837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455837).length < 2 ^ (prefixWord ++ tailWord_2455837).sum := by decide
  have hdescent : baseEnd_2455837 < baseStart_2455837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455863 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 3, 3]
def baseStart_2455863 : Nat := 118140960795 + 2455863 * 2 ^ 59
def prefixEnd_2455863 : Nat := 4983230072969 + 3 ^ 40 * 2455863 * 2
def baseEnd_2455863 : Nat := 840692093728553438945465

theorem tailTrace_2455863 : CollatzResearch.WordTrace tailWord_2455863 prefixEnd_2455863 840692093728553438945465 := by
  unfold tailWord_2455863
  simp only [CollatzResearch.WordTrace]
  refine ⟨89572682301835253853140243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59715121534556835902093495 89572682301835253853140243)
  ·
    refine ⟨134359023452752880779710365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89572682301835253853140243 134359023452752880779710365)
    ·
      refine ⟨50384633794782330292391387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134359023452752880779710365 50384633794782330292391387)
      ·
        refine ⟨75576950692173495438587081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50384633794782330292391387 75576950692173495438587081)
        ·
          refine ⟨56682713019130121578940311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75576950692173495438587081 56682713019130121578940311)
          ·
            refine ⟨85024069528695182368410467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56682713019130121578940311 85024069528695182368410467)
            ·
              refine ⟨127536104293042773552615701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85024069528695182368410467 127536104293042773552615701)
              ·
                refine ⟨5978254888736380010278861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 127536104293042773552615701 5978254888736380010278861)
                ·
                  refine ⟨2241845583276142503854573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5978254888736380010278861 2241845583276142503854573)
                  ·
                    refine ⟨840692093728553438945465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2241845583276142503854573 840692093728553438945465)
                    ·
                      rfl

theorem cell22_2455863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_2455863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455863 prefixEnd_2455863 := by exact prefixLift 2455863
  have htrace : WordTrace (prefixWord ++ tailWord_2455863) baseStart_2455863 baseEnd_2455863 := by
    simpa [prefixWord, tailWord_2455863, baseEnd_2455863] using wordTrace_append hprefix tailTrace_2455863
  have hstable : (prefixWord ++ tailWord_2455863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455863).length < 2 ^ (prefixWord ++ tailWord_2455863).sum := by decide
  have hdescent : baseEnd_2455863 < baseStart_2455863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455908 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_2455908 : Nat := 118140960795 + 2455908 * 2 ^ 59
def prefixEnd_2455908 : Nat := 4983230072969 + 3 ^ 40 * 2455908 * 2
def baseEnd_2455908 : Nat := 840707498148188321570327

theorem tailTrace_2455908 : CollatzResearch.WordTrace tailWord_2455908 prefixEnd_2455908 840707498148188321570327 := by
  unfold tailWord_2455908
  simp only [CollatzResearch.WordTrace]
  refine ⟨44787161793336113269264189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59716215724448151025685585 44787161793336113269264189)
  ·
    refine ⟨16795185672501042475974071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44787161793336113269264189 16795185672501042475974071)
    ·
      refine ⟨25192778508751563713961107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16795185672501042475974071 25192778508751563713961107)
      ·
        refine ⟨37789167763127345570941661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25192778508751563713961107 37789167763127345570941661)
        ·
          refine ⟨14170937911172754589103123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37789167763127345570941661 14170937911172754589103123)
          ·
            refine ⟨21256406866759131883654685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14170937911172754589103123 21256406866759131883654685)
            ·
              refine ⟨7971152575034674456370507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21256406866759131883654685 7971152575034674456370507)
              ·
                refine ⟨11956728862552011684555761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7971152575034674456370507 11956728862552011684555761)
                ·
                  refine ⟨8967546646914008763416821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11956728862552011684555761 8967546646914008763416821)
                  ·
                    refine ⟨840707498148188321570327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8967546646914008763416821 840707498148188321570327)
                    ·
                      rfl

theorem cell22_2455908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_2455908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455908 prefixEnd_2455908 := by exact prefixLift 2455908
  have htrace : WordTrace (prefixWord ++ tailWord_2455908) baseStart_2455908 baseEnd_2455908 := by
    simpa [prefixWord, tailWord_2455908, baseEnd_2455908] using wordTrace_append hprefix tailTrace_2455908
  have hstable : (prefixWord ++ tailWord_2455908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455908).length < 2 ^ (prefixWord ++ tailWord_2455908).sum := by decide
  have hdescent : baseEnd_2455908 < baseStart_2455908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455940 : List Nat := [2, 3, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_2455940 : Nat := 118140960795 + 2455940 * 2 ^ 59
def prefixEnd_2455940 : Nat := 4983230072969 + 3 ^ 40 * 2455940 * 2
def baseEnd_2455940 : Nat := 840718452402150904770229

theorem tailTrace_2455940 : CollatzResearch.WordTrace tailWord_2455940 prefixEnd_2455940 840718452402150904770229 := by
  unfold tailWord_2455940
  simp only [CollatzResearch.WordTrace]
  refine ⟨44787745361278148001846637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59716993815037530669128849 44787745361278148001846637)
  ·
    refine ⟨16795404510479305500692489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44787745361278148001846637 16795404510479305500692489)
    ·
      refine ⟨12596553382859479125519367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16795404510479305500692489 12596553382859479125519367)
      ·
        refine ⟨18894830074289218688279051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12596553382859479125519367 18894830074289218688279051)
        ·
          refine ⟨28342245111433828032418577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18894830074289218688279051 28342245111433828032418577)
          ·
            refine ⟨21256683833575371024313933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28342245111433828032418577 21256683833575371024313933)
            ·
              refine ⟨7971256437590764134117725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21256683833575371024313933 7971256437590764134117725)
              ·
                refine ⟨2989221164096536550294147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7971256437590764134117725 2989221164096536550294147)
                ·
                  refine ⟨4483831746144804825441221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2989221164096536550294147 4483831746144804825441221)
                  ·
                    refine ⟨840718452402150904770229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4483831746144804825441221 840718452402150904770229)
                    ·
                      rfl

theorem cell22_2455940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_2455940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455940 prefixEnd_2455940 := by exact prefixLift 2455940
  have htrace : WordTrace (prefixWord ++ tailWord_2455940) baseStart_2455940 baseEnd_2455940 := by
    simpa [prefixWord, tailWord_2455940, baseEnd_2455940] using wordTrace_append hprefix tailTrace_2455940
  have hstable : (prefixWord ++ tailWord_2455940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455940).length < 2 ^ (prefixWord ++ tailWord_2455940).sum := by decide
  have hdescent : baseEnd_2455940 < baseStart_2455940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455968 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 1, 6]
def baseStart_2455968 : Nat := 118140960795 + 2455968 * 2 ^ 59
def prefixEnd_2455968 : Nat := 4983230072969 + 3 ^ 40 * 2455968 * 2
def baseEnd_2455968 : Nat := 840728037374368165070143

theorem tailTrace_2455968 : CollatzResearch.WordTrace tailWord_2455968 prefixEnd_2455968 840728037374368165070143 := by
  unfold tailWord_2455968
  simp only [CollatzResearch.WordTrace]
  refine ⟨44788255983227428392856279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59717674644303237857141705 44788255983227428392856279)
  ·
    refine ⟨67182383974841142589284419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44788255983227428392856279 67182383974841142589284419)
    ·
      refine ⟨100773575962261713883926629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67182383974841142589284419 100773575962261713883926629)
      ·
        refine ⟨18895045492924071353236243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100773575962261713883926629 18895045492924071353236243)
        ·
          refine ⟨28342568239386107029854365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18895045492924071353236243 28342568239386107029854365)
          ·
            refine ⟨10628463089769790136195387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28342568239386107029854365 10628463089769790136195387)
            ·
              refine ⟨15942694634654685204293081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10628463089769790136195387 15942694634654685204293081)
              ·
                refine ⟨11957020975991013903219811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15942694634654685204293081 11957020975991013903219811)
                ·
                  refine ⟨17935531463986520854829717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11957020975991013903219811 17935531463986520854829717)
                  ·
                    refine ⟨840728037374368165070143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17935531463986520854829717 840728037374368165070143)
                    ·
                      rfl

theorem cell22_2455968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_2455968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455968 prefixEnd_2455968 := by exact prefixLift 2455968
  have htrace : WordTrace (prefixWord ++ tailWord_2455968) baseStart_2455968 baseEnd_2455968 := by
    simpa [prefixWord, tailWord_2455968, baseEnd_2455968] using wordTrace_append hprefix tailTrace_2455968
  have hstable : (prefixWord ++ tailWord_2455968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455968).length < 2 ^ (prefixWord ++ tailWord_2455968).sum := by decide
  have hdescent : baseEnd_2455968 < baseStart_2455968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2455989 : List Nat := [1, 3, 3, 2, 3, 2, 1, 3, 4]
def baseStart_2455989 : Nat := 118140960795 + 2455989 * 2 ^ 59
def prefixEnd_2455989 : Nat := 4983230072969 + 3 ^ 40 * 2455989 * 2
def baseEnd_2455989 : Nat := 280245075367843703431693

theorem tailTrace_2455989 : CollatzResearch.WordTrace tailWord_2455989 prefixEnd_2455989 280245075367843703431693 := by
  unfold tailWord_2455989
  simp only [CollatzResearch.WordTrace]
  refine ⟨89577277899378777372227021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59718185266252518248151347 89577277899378777372227021)
  ·
    refine ⟨33591479212267041514585133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89577277899378777372227021 33591479212267041514585133)
    ·
      refine ⟨12596804704600140567969425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33591479212267041514585133 12596804704600140567969425)
      ·
        refine ⟨9447603528450105425977069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12596804704600140567969425 9447603528450105425977069)
        ·
          refine ⟨3542851323168789534741401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9447603528450105425977069 3542851323168789534741401)
          ·
            refine ⟨2657138492376592151056051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3542851323168789534741401 2657138492376592151056051)
            ·
              refine ⟨3985707738564888226584077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657138492376592151056051 3985707738564888226584077)
              ·
                refine ⟨1494640401961833084969029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3985707738564888226584077 1494640401961833084969029)
                ·
                  refine ⟨280245075367843703431693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1494640401961833084969029 280245075367843703431693)
                  ·
                    rfl

theorem cell22_2455989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_2455989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2455989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2455989 prefixEnd_2455989 := by exact prefixLift 2455989
  have htrace : WordTrace (prefixWord ++ tailWord_2455989) baseStart_2455989 baseEnd_2455989 := by
    simpa [prefixWord, tailWord_2455989, baseEnd_2455989] using wordTrace_append hprefix tailTrace_2455989
  have hstable : (prefixWord ++ tailWord_2455989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2455989).length < 2 ^ (prefixWord ++ tailWord_2455989).sum := by decide
  have hdescent : baseEnd_2455989 < baseStart_2455989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2455989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456075 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 3, 4]
def baseStart_2456075 : Nat := 118140960795 + 2456075 * 2 ^ 59
def prefixEnd_2456075 : Nat := 4983230072969 + 3 ^ 40 * 2456075 * 2
def baseEnd_2456075 : Nat := 840764665661055552644815

theorem tailTrace_2456075 : CollatzResearch.WordTrace tailWord_2456075 prefixEnd_2456075 840764665661055552644815 := by
  unfold tailWord_2456075
  simp only [CollatzResearch.WordTrace]
  refine ⟨89580414577067214059857679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59720276384711476039905119 89580414577067214059857679)
  ·
    refine ⟨134370621865600821089786519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89580414577067214059857679 134370621865600821089786519)
    ·
      refine ⟨201555932798401231634679779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134370621865600821089786519 201555932798401231634679779)
      ·
        refine ⟨302333899197601847452019669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201555932798401231634679779 302333899197601847452019669)
        ·
          refine ⟨7085950762443793299656711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 302333899197601847452019669 7085950762443793299656711)
          ·
            refine ⟨10628926143665689949485067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7085950762443793299656711 10628926143665689949485067)
            ·
              refine ⟨15943389215498534924227601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10628926143665689949485067 15943389215498534924227601)
              ·
                refine ⟨11957541911623901193170701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15943389215498534924227601 11957541911623901193170701)
                ·
                  refine ⟨4484078216858962947439013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11957541911623901193170701 4484078216858962947439013)
                  ·
                    refine ⟨840764665661055552644815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4484078216858962947439013 840764665661055552644815)
                    ·
                      rfl

theorem cell22_2456075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 4].length) (baseStart_2456075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456075 prefixEnd_2456075 := by exact prefixLift 2456075
  have htrace : WordTrace (prefixWord ++ tailWord_2456075) baseStart_2456075 baseEnd_2456075 := by
    simpa [prefixWord, tailWord_2456075, baseEnd_2456075] using wordTrace_append hprefix tailTrace_2456075
  have hstable : (prefixWord ++ tailWord_2456075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456075).length < 2 ^ (prefixWord ++ tailWord_2456075).sum := by decide
  have hdescent : baseEnd_2456075 < baseStart_2456075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456120 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 4, 4]
def baseStart_2456120 : Nat := 118140960795 + 2456120 * 2 ^ 59
def prefixEnd_2456120 : Nat := 4983230072969 + 3 ^ 40 * 2456120 * 2
def baseEnd_2456120 : Nat := 840780070080690435269677

theorem tailTrace_2456120 : CollatzResearch.WordTrace tailWord_2456120 prefixEnd_2456120 840780070080690435269677 := by
  unfold tailWord_2456120
  simp only [CollatzResearch.WordTrace]
  refine ⟨44791027930952093372622907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59721370574602791163497209 44791027930952093372622907)
  ·
    refine ⟨67186541896428140058934361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44791027930952093372622907 67186541896428140058934361)
    ·
      refine ⟨50389906422321105044200771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67186541896428140058934361 50389906422321105044200771)
      ·
        refine ⟨75584859633481657566301157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50389906422321105044200771 75584859633481657566301157)
        ·
          refine ⟨14172161181277810793681467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75584859633481657566301157 14172161181277810793681467)
          ·
            refine ⟨21258241771916716190522201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14172161181277810793681467 21258241771916716190522201)
            ·
              refine ⟨15943681328937537142891651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21258241771916716190522201 15943681328937537142891651)
              ·
                refine ⟨23915521993406305714337477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15943681328937537142891651 23915521993406305714337477)
                ·
                  refine ⟨4484160373763682321438277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23915521993406305714337477 4484160373763682321438277)
                  ·
                    refine ⟨840780070080690435269677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4484160373763682321438277 840780070080690435269677)
                    ·
                      rfl

theorem cell22_2456120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_2456120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456120 prefixEnd_2456120 := by exact prefixLift 2456120
  have htrace : WordTrace (prefixWord ++ tailWord_2456120) baseStart_2456120 baseEnd_2456120 := by
    simpa [prefixWord, tailWord_2456120, baseEnd_2456120] using wordTrace_append hprefix tailTrace_2456120
  have hstable : (prefixWord ++ tailWord_2456120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456120).length < 2 ^ (prefixWord ++ tailWord_2456120).sum := by decide
  have hdescent : baseEnd_2456120 < baseStart_2456120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456122 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 4, 3]
def baseStart_2456122 : Nat := 118140960795 + 2456122 * 2 ^ 59
def prefixEnd_2456122 : Nat := 4983230072969 + 3 ^ 40 * 2456122 * 2
def baseEnd_2456122 : Nat := 840780754721563096719671

theorem tailTrace_2456122 : CollatzResearch.WordTrace tailWord_2456122 prefixEnd_2456122 840780754721563096719671 := by
  unfold tailWord_2456122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22395532201974235271704655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59721419205264627391212413 22395532201974235271704655)
  ·
    refine ⟨33593298302961352907556983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22395532201974235271704655 33593298302961352907556983)
    ·
      refine ⟨50389947454442029361335475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33593298302961352907556983 50389947454442029361335475)
      ·
        refine ⟨75584921181663044042003213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50389947454442029361335475 75584921181663044042003213)
        ·
          refine ⟨28344345443123641515751205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75584921181663044042003213 28344345443123641515751205)
          ·
            refine ⟨5314564770585682784203351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28344345443123641515751205 5314564770585682784203351)
            ·
              refine ⟨7971847155878524176305027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5314564770585682784203351 7971847155878524176305027)
              ·
                refine ⟨11957770733817786264457541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7971847155878524176305027 11957770733817786264457541)
                ·
                  refine ⟨2242082012590834924585789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11957770733817786264457541 2242082012590834924585789)
                  ·
                    refine ⟨840780754721563096719671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2242082012590834924585789 840780754721563096719671)
                    ·
                      rfl

theorem cell22_2456122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_2456122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456122 prefixEnd_2456122 := by exact prefixLift 2456122
  have htrace : WordTrace (prefixWord ++ tailWord_2456122) baseStart_2456122 baseEnd_2456122 := by
    simpa [prefixWord, tailWord_2456122, baseEnd_2456122] using wordTrace_append hprefix tailTrace_2456122
  have hstable : (prefixWord ++ tailWord_2456122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456122).length < 2 ^ (prefixWord ++ tailWord_2456122).sum := by decide
  have hdescent : baseEnd_2456122 < baseStart_2456122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456195 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 2, 5]
def baseStart_2456195 : Nat := 118140960795 + 2456195 * 2 ^ 59
def prefixEnd_2456195 : Nat := 4983230072969 + 3 ^ 40 * 2456195 * 2
def baseEnd_2456195 : Nat := 840805744113415239644447

theorem tailTrace_2456195 : CollatzResearch.WordTrace tailWord_2456195 prefixEnd_2456195 840805744113415239644447 := by
  unfold tailWord_2456195
  simp only [CollatzResearch.WordTrace]
  refine ⟨89584791336632474554226039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59723194224421649702817359 89584791336632474554226039)
  ·
    refine ⟨134377187004948711831339059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89584791336632474554226039 134377187004948711831339059)
    ·
      refine ⟨201565780507423067747008589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134377187004948711831339059 201565780507423067747008589)
      ·
        refine ⟨75587167690283650405128221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201565780507423067747008589 75587167690283650405128221)
        ·
          refine ⟨28345187883856368901923083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75587167690283650405128221 28345187883856368901923083)
          ·
            refine ⟨42517781825784553352884625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28345187883856368901923083 42517781825784553352884625)
            ·
              refine ⟨31888336369338415014663469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42517781825784553352884625 31888336369338415014663469)
              ·
                refine ⟨11958126138501905630498801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31888336369338415014663469 11958126138501905630498801)
                ·
                  refine ⟨8968594603876429222874101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11958126138501905630498801 8968594603876429222874101)
                  ·
                    refine ⟨840805744113415239644447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8968594603876429222874101 840805744113415239644447)
                    ·
                      rfl

theorem cell22_2456195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 5].length) (baseStart_2456195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456195 prefixEnd_2456195 := by exact prefixLift 2456195
  have htrace : WordTrace (prefixWord ++ tailWord_2456195) baseStart_2456195 baseEnd_2456195 := by
    simpa [prefixWord, tailWord_2456195, baseEnd_2456195] using wordTrace_append hprefix tailTrace_2456195
  have hstable : (prefixWord ++ tailWord_2456195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456195).length < 2 ^ (prefixWord ++ tailWord_2456195).sum := by decide
  have hdescent : baseEnd_2456195 < baseStart_2456195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456197 : List Nat := [1, 3, 1, 1, 4, 3, 1, 3, 5]
def baseStart_2456197 : Nat := 118140960795 + 2456197 * 2 ^ 59
def prefixEnd_2456197 : Nat := 4983230072969 + 3 ^ 40 * 2456197 * 2
def baseEnd_2456197 : Nat := 280268809584762633698147

theorem tailTrace_2456197 : CollatzResearch.WordTrace tailWord_2456197 prefixEnd_2456197 280268809584762633698147 := by
  unfold tailWord_2456197
  simp only [CollatzResearch.WordTrace]
  refine ⟨89584864282625228895798845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59723242855083485930532563 89584864282625228895798845)
  ·
    refine ⟨33594324105984460835924567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89584864282625228895798845 33594324105984460835924567)
    ·
      refine ⟨50391486158976691253886851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33594324105984460835924567 50391486158976691253886851)
      ·
        refine ⟨75587229238465036880830277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50391486158976691253886851 75587229238465036880830277)
        ·
          refine ⟨14172605482212194415155677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75587229238465036880830277 14172605482212194415155677)
          ·
            refine ⟨5314727055829572905683379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14172605482212194415155677 5314727055829572905683379)
            ·
              refine ⟨7972090583744359358525069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5314727055829572905683379 7972090583744359358525069)
              ·
                refine ⟨2989533968904134759446901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7972090583744359358525069 2989533968904134759446901)
                ·
                  refine ⟨280268809584762633698147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2989533968904134759446901 280268809584762633698147)
                  ·
                    rfl

theorem cell22_2456197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_2456197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456197 prefixEnd_2456197 := by exact prefixLift 2456197
  have htrace : WordTrace (prefixWord ++ tailWord_2456197) baseStart_2456197 baseEnd_2456197 := by
    simpa [prefixWord, tailWord_2456197, baseEnd_2456197] using wordTrace_append hprefix tailTrace_2456197
  have hstable : (prefixWord ++ tailWord_2456197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456197).length < 2 ^ (prefixWord ++ tailWord_2456197).sum := by decide
  have hdescent : baseEnd_2456197 < baseStart_2456197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456231 : List Nat := [1, 1, 6, 3, 1, 1, 2, 2, 5]
def baseStart_2456231 : Nat := 118140960795 + 2456231 * 2 ^ 59
def prefixEnd_2456231 : Nat := 4983230072969 + 3 ^ 40 * 2456231 * 2
def baseEnd_2456231 : Nat := 280272689216374381914779

theorem tailTrace_2456231 : CollatzResearch.WordTrace tailWord_2456231 prefixEnd_2456231 280272689216374381914779 := by
  unfold tailWord_2456231
  simp only [CollatzResearch.WordTrace]
  refine ⟨89586104364502052702536547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59724069576334701801691031 89586104364502052702536547)
  ·
    refine ⟨134379156546753079053804821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89586104364502052702536547 134379156546753079053804821)
    ·
      refine ⟨6299022963129050580647101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 134379156546753079053804821 6299022963129050580647101)
      ·
        refine ⟨2362133611173393967742663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6299022963129050580647101 2362133611173393967742663)
        ·
          refine ⟨3543200416760090951613995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2362133611173393967742663 3543200416760090951613995)
          ·
            refine ⟨5314800625140136427420993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3543200416760090951613995 5314800625140136427420993)
            ·
              refine ⟨3986100468855102320565745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5314800625140136427420993 3986100468855102320565745)
              ·
                refine ⟨2989575351641326740424309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3986100468855102320565745 2989575351641326740424309)
                ·
                  refine ⟨280272689216374381914779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2989575351641326740424309 280272689216374381914779)
                  ·
                    rfl

theorem cell22_2456231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 5].length) (baseStart_2456231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456231 prefixEnd_2456231 := by exact prefixLift 2456231
  have htrace : WordTrace (prefixWord ++ tailWord_2456231) baseStart_2456231 baseEnd_2456231 := by
    simpa [prefixWord, tailWord_2456231, baseEnd_2456231] using wordTrace_append hprefix tailTrace_2456231
  have hstable : (prefixWord ++ tailWord_2456231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456231).length < 2 ^ (prefixWord ++ tailWord_2456231).sum := by decide
  have hdescent : baseEnd_2456231 < baseStart_2456231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456240 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 5, 5]
def baseStart_2456240 : Nat := 118140960795 + 2456240 * 2 ^ 59
def prefixEnd_2456240 : Nat := 4983230072969 + 3 ^ 40 * 2456240 * 2
def baseEnd_2456240 : Nat := 840821148533050122269309

theorem tailTrace_2456240 : CollatzResearch.WordTrace tailWord_2456240 prefixEnd_2456240 840821148533050122269309 := by
  unfold tailWord_2456240
  simp only [CollatzResearch.WordTrace]
  refine ⟨44793216310734723619807087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59724288414312964826409449 44793216310734723619807087)
  ·
    refine ⟨67189824466102085429710631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44793216310734723619807087 67189824466102085429710631)
    ·
      refine ⟨100784736699153128144565947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67189824466102085429710631 100784736699153128144565947)
      ·
        refine ⟨151177105048729692216848921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100784736699153128144565947 151177105048729692216848921)
        ·
          refine ⟨113382828786547269162636691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151177105048729692216848921 113382828786547269162636691)
          ·
            refine ⟨170074243179820903743955037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113382828786547269162636691 170074243179820903743955037)
            ·
              refine ⟨63777841192432838903983139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170074243179820903743955037 63777841192432838903983139)
              ·
                refine ⟨95666761788649258355974709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63777841192432838903983139 95666761788649258355974709)
                ·
                  refine ⟨8968758917685867970872629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95666761788649258355974709 8968758917685867970872629)
                  ·
                    refine ⟨840821148533050122269309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8968758917685867970872629 840821148533050122269309)
                    ·
                      rfl

theorem cell22_2456240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_2456240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456240 prefixEnd_2456240 := by exact prefixLift 2456240
  have htrace : WordTrace (prefixWord ++ tailWord_2456240) baseStart_2456240 baseEnd_2456240 := by
    simpa [prefixWord, tailWord_2456240, baseEnd_2456240] using wordTrace_append hprefix tailTrace_2456240
  have hstable : (prefixWord ++ tailWord_2456240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456240).length < 2 ^ (prefixWord ++ tailWord_2456240).sum := by decide
  have hdescent : baseEnd_2456240 < baseStart_2456240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456246 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2456246 : Nat := 118140960795 + 2456246 * 2 ^ 59
def prefixEnd_2456246 : Nat := 4983230072969 + 3 ^ 40 * 2456246 * 2
def baseEnd_2456246 : Nat := 840823202455668106619291

theorem tailTrace_2456246 : CollatzResearch.WordTrace tailWord_2456246 prefixEnd_2456246 840823202455668106619291 := by
  unfold tailWord_2456246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5599165716215481891520787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59724434306298473509555061 5599165716215481891520787)
  ·
    refine ⟨8398748574323222837281181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5599165716215481891520787 8398748574323222837281181)
    ·
      refine ⟨3149530715371208563980443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8398748574323222837281181 3149530715371208563980443)
      ·
        refine ⟨4724296073056812845970665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3149530715371208563980443 4724296073056812845970665)
        ·
          refine ⟨3543222054792609634477999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4724296073056812845970665 3543222054792609634477999)
          ·
            refine ⟨5314833082188914451716999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3543222054792609634477999 5314833082188914451716999)
            ·
              refine ⟨7972249623283371677575499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5314833082188914451716999 7972249623283371677575499)
              ·
                refine ⟨11958374434925057516363249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7972249623283371677575499 11958374434925057516363249)
                ·
                  refine ⟨8968780826193793137272437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11958374434925057516363249 8968780826193793137272437)
                  ·
                    refine ⟨840823202455668106619291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8968780826193793137272437 840823202455668106619291)
                    ·
                      rfl

theorem cell22_2456246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2456246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456246 prefixEnd_2456246 := by exact prefixLift 2456246
  have htrace : WordTrace (prefixWord ++ tailWord_2456246) baseStart_2456246 baseEnd_2456246 := by
    simpa [prefixWord, tailWord_2456246, baseEnd_2456246] using wordTrace_append hprefix tailTrace_2456246
  have hstable : (prefixWord ++ tailWord_2456246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456246).length < 2 ^ (prefixWord ++ tailWord_2456246).sum := by decide
  have hdescent : baseEnd_2456246 < baseStart_2456246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456291 : List Nat := [1, 1, 1, 7, 1, 1, 3, 2, 2, 3]
def baseStart_2456291 : Nat := 118140960795 + 2456291 * 2 ^ 59
def prefixEnd_2456291 : Nat := 4983230072969 + 3 ^ 40 * 2456291 * 2
def baseEnd_2456291 : Nat := 840838606875302989244153

theorem tailTrace_2456291 : CollatzResearch.WordTrace tailWord_2456291 prefixEnd_2456291 840838606875302989244153 := by
  unfold tailWord_2456291
  simp only [CollatzResearch.WordTrace]
  refine ⟨89588292744284682949720727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59725528496189788633147151 89588292744284682949720727)
  ·
    refine ⟨134382439116427024424581091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89588292744284682949720727 134382439116427024424581091)
    ·
      refine ⟨201573658674640536636871637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134382439116427024424581091 201573658674640536636871637)
      ·
        refine ⟨4724382625186887577426679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 201573658674640536636871637 4724382625186887577426679)
        ·
          refine ⟨7086573937780331366140019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4724382625186887577426679 7086573937780331366140019)
          ·
            refine ⟨10629860906670497049210029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7086573937780331366140019 10629860906670497049210029)
            ·
              refine ⟨3986197840001436393453761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10629860906670497049210029 3986197840001436393453761)
              ·
                refine ⟨2989648380001077295090321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3986197840001436393453761 2989648380001077295090321)
                ·
                  refine ⟨2242236285000807971317741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2989648380001077295090321 2242236285000807971317741)
                  ·
                    refine ⟨840838606875302989244153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2242236285000807971317741 840838606875302989244153)
                    ·
                      rfl

theorem cell22_2456291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 3].length) (baseStart_2456291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456291 prefixEnd_2456291 := by exact prefixLift 2456291
  have htrace : WordTrace (prefixWord ++ tailWord_2456291) baseStart_2456291 baseEnd_2456291 := by
    simpa [prefixWord, tailWord_2456291, baseEnd_2456291] using wordTrace_append hprefix tailTrace_2456291
  have hstable : (prefixWord ++ tailWord_2456291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456291).length < 2 ^ (prefixWord ++ tailWord_2456291).sum := by decide
  have hdescent : baseEnd_2456291 < baseStart_2456291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456353 : List Nat := [1, 2, 3, 2, 1, 2, 5, 2, 1, 3]
def baseStart_2456353 : Nat := 118140960795 + 2456353 * 2 ^ 59
def prefixEnd_2456353 : Nat := 4983230072969 + 3 ^ 40 * 2456353 * 2
def baseEnd_2456353 : Nat := 840859830742355494193963

theorem tailTrace_2456353 : CollatzResearch.WordTrace tailWord_2456353 prefixEnd_2456353 840859830742355494193963 := by
  unfold tailWord_2456353
  simp only [CollatzResearch.WordTrace]
  refine ⟨89590554070060067538477713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59727036046706711692318475 89590554070060067538477713)
  ·
    refine ⟨67192915552545050653858285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89590554070060067538477713 67192915552545050653858285)
    ·
      refine ⟨25197343332204393995196857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67192915552545050653858285 25197343332204393995196857)
      ·
        refine ⟨18898007499153295496397643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25197343332204393995196857 18898007499153295496397643)
        ·
          refine ⟨28347011248729943244596465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18898007499153295496397643 28347011248729943244596465)
          ·
            refine ⟨21260258436547457433447349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28347011248729943244596465 21260258436547457433447349)
            ·
              refine ⟨1993149228426324134385689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21260258436547457433447349 1993149228426324134385689)
              ·
                refine ⟨1494861921319743100789267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1993149228426324134385689 1494861921319743100789267)
                ·
                  refine ⟨2242292881979614651183901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494861921319743100789267 2242292881979614651183901)
                  ·
                    refine ⟨840859830742355494193963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2242292881979614651183901 840859830742355494193963)
                    ·
                      rfl

theorem cell22_2456353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_2456353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456353 prefixEnd_2456353 := by exact prefixLift 2456353
  have htrace : WordTrace (prefixWord ++ tailWord_2456353) baseStart_2456353 baseEnd_2456353 := by
    simpa [prefixWord, tailWord_2456353, baseEnd_2456353] using wordTrace_append hprefix tailTrace_2456353
  have hstable : (prefixWord ++ tailWord_2456353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456353).length < 2 ^ (prefixWord ++ tailWord_2456353).sum := by decide
  have hdescent : baseEnd_2456353 < baseStart_2456353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456366 : List Nat := [4, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_2456366 : Nat := 118140960795 + 2456366 * 2 ^ 59
def prefixEnd_2456366 : Nat := 4983230072969 + 3 ^ 40 * 2456366 * 2
def baseEnd_2456366 : Nat := 280288093636009264539641

theorem tailTrace_2456366 : CollatzResearch.WordTrace tailWord_2456366 prefixEnd_2456366 280288093636009264539641 := by
  unfold tailWord_2456366
  simp only [CollatzResearch.WordTrace]
  refine ⟨11198878527376621344837619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59727352146008647172467301 11198878527376621344837619)
  ·
    refine ⟨16798317791064932017256429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11198878527376621344837619 16798317791064932017256429)
    ·
      refine ⟨6299369171649349506471161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16798317791064932017256429 6299369171649349506471161)
      ·
        refine ⟨4724526878737012129853371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6299369171649349506471161 4724526878737012129853371)
        ·
          refine ⟨7086790318105518194780057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4724526878737012129853371 7086790318105518194780057)
          ·
            refine ⟨5315092738579138646085043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7086790318105518194780057 5315092738579138646085043)
            ·
              refine ⟨7972639107868707969127565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5315092738579138646085043 7972639107868707969127565)
              ·
                refine ⟨2989739665450765488422837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7972639107868707969127565 2989739665450765488422837)
                ·
                  refine ⟨280288093636009264539641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2989739665450765488422837 280288093636009264539641)
                  ·
                    rfl

theorem cell22_2456366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_2456366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456366 prefixEnd_2456366 := by exact prefixLift 2456366
  have htrace : WordTrace (prefixWord ++ tailWord_2456366) baseStart_2456366 baseEnd_2456366 := by
    simpa [prefixWord, tailWord_2456366, baseEnd_2456366] using wordTrace_append hprefix tailTrace_2456366
  have hstable : (prefixWord ++ tailWord_2456366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456366).length < 2 ^ (prefixWord ++ tailWord_2456366).sum := by decide
  have hdescent : baseEnd_2456366 < baseStart_2456366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456441 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 2, 4]
def baseStart_2456441 : Nat := 118140960795 + 2456441 * 2 ^ 59
def prefixEnd_2456441 : Nat := 4983230072969 + 3 ^ 40 * 2456441 * 2
def baseEnd_2456441 : Nat := 840889954940752597993693

theorem tailTrace_2456441 : CollatzResearch.WordTrace tailWord_2456441 prefixEnd_2456441 840889954940752597993693 := by
  unfold tailWord_2456441
  simp only [CollatzResearch.WordTrace]
  refine ⟨89593763693741258567681177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59729175795827505711787451 89593763693741258567681177)
  ·
    refine ⟨67195322770305943925760883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89593763693741258567681177 67195322770305943925760883)
    ·
      refine ⟨100792984155458915888641325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67195322770305943925760883 100792984155458915888641325)
      ·
        refine ⟨37797369058297093458240497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100792984155458915888641325 37797369058297093458240497)
        ·
          refine ⟨28348026793722820093680373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37797369058297093458240497 28348026793722820093680373)
          ·
            refine ⟨2657627511911514383782535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28348026793722820093680373 2657627511911514383782535)
            ·
              refine ⟨3986441267867271575673803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657627511911514383782535 3986441267867271575673803)
              ·
                refine ⟨5979661901800907363510705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3986441267867271575673803 5979661901800907363510705)
                ·
                  refine ⟨4484746426350680522633029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5979661901800907363510705 4484746426350680522633029)
                  ·
                    refine ⟨840889954940752597993693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4484746426350680522633029 840889954940752597993693)
                    ·
                      rfl

theorem cell22_2456441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 4].length) (baseStart_2456441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456441 prefixEnd_2456441 := by exact prefixLift 2456441
  have htrace : WordTrace (prefixWord ++ tailWord_2456441) baseStart_2456441 baseEnd_2456441 := by
    simpa [prefixWord, tailWord_2456441, baseEnd_2456441] using wordTrace_append hprefix tailTrace_2456441
  have hstable : (prefixWord ++ tailWord_2456441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456441).length < 2 ^ (prefixWord ++ tailWord_2456441).sum := by decide
  have hdescent : baseEnd_2456441 < baseStart_2456441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456471 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 3, 3]
def baseStart_2456471 : Nat := 118140960795 + 2456471 * 2 ^ 59
def prefixEnd_2456471 : Nat := 4983230072969 + 3 ^ 40 * 2456471 * 2
def baseEnd_2456471 : Nat := 840900224553842519743601

theorem tailTrace_2456471 : CollatzResearch.WordTrace tailWord_2456471 prefixEnd_2456471 840900224553842519743601 := by
  unfold tailWord_2456471
  simp only [CollatzResearch.WordTrace]
  refine ⟨89594857883632573691273267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59729905255755049127515511 89594857883632573691273267)
  ·
    refine ⟨134392286825448860536909901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89594857883632573691273267 134392286825448860536909901)
    ·
      refine ⟨50397107559543322701341213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134392286825448860536909901 50397107559543322701341213)
      ·
        refine ⟨18898915334828746013002955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50397107559543322701341213 18898915334828746013002955)
        ·
          refine ⟨28348373002243119019504433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18898915334828746013002955 28348373002243119019504433)
          ·
            refine ⟨21261279751682339264628325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28348373002243119019504433 21261279751682339264628325)
            ·
              refine ⟨3986489953440438612117811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21261279751682339264628325 3986489953440438612117811)
              ·
                refine ⟨5979734930160657918176717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3986489953440438612117811 5979734930160657918176717)
                ·
                  refine ⟨2242400598810246719316269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5979734930160657918176717 2242400598810246719316269)
                  ·
                    refine ⟨840900224553842519743601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2242400598810246719316269 840900224553842519743601)
                    ·
                      rfl

theorem cell22_2456471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_2456471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456471 prefixEnd_2456471 := by exact prefixLift 2456471
  have htrace : WordTrace (prefixWord ++ tailWord_2456471) baseStart_2456471 baseEnd_2456471 := by
    simpa [prefixWord, tailWord_2456471, baseEnd_2456471] using wordTrace_append hprefix tailTrace_2456471
  have hstable : (prefixWord ++ tailWord_2456471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456471).length < 2 ^ (prefixWord ++ tailWord_2456471).sum := by decide
  have hdescent : baseEnd_2456471 < baseStart_2456471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456505 : List Nat := [1, 2, 1, 4, 2, 4, 1, 3, 1, 3]
def baseStart_2456505 : Nat := 118140960795 + 2456505 * 2 ^ 59
def prefixEnd_2456505 : Nat := 4983230072969 + 3 ^ 40 * 2456505 * 2
def baseEnd_2456505 : Nat := 840911863448677764393497

theorem tailTrace_2456505 : CollatzResearch.WordTrace tailWord_2456505 prefixEnd_2456505 840911863448677764393497 := by
  unfold tailWord_2456505
  simp only [CollatzResearch.WordTrace]
  refine ⟨89596097965509397498010969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59730731977006264998673979 89596097965509397498010969)
  ·
    refine ⟨67197073474132048123508227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89596097965509397498010969 67197073474132048123508227)
    ·
      refine ⟨100795610211198072185262341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67197073474132048123508227 100795610211198072185262341)
      ·
        refine ⟨18899176914599638534736689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100795610211198072185262341 18899176914599638534736689)
        ·
          refine ⟨14174382685949728901052517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18899176914599638534736689 14174382685949728901052517)
          ·
            refine ⟨2657696753615574168947347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14174382685949728901052517 2657696753615574168947347)
            ·
              refine ⟨3986545130423361253421021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657696753615574168947347 3986545130423361253421021)
              ·
                refine ⟨1494954423908760470032883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3986545130423361253421021 1494954423908760470032883)
                ·
                  refine ⟨2242431635863140705049325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494954423908760470032883 2242431635863140705049325)
                  ·
                    refine ⟨840911863448677764393497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2242431635863140705049325 840911863448677764393497)
                    ·
                      rfl

theorem cell22_2456505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 1, 3].length) (baseStart_2456505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456505 prefixEnd_2456505 := by exact prefixLift 2456505
  have htrace : WordTrace (prefixWord ++ tailWord_2456505) baseStart_2456505 baseEnd_2456505 := by
    simpa [prefixWord, tailWord_2456505, baseEnd_2456505] using wordTrace_append hprefix tailTrace_2456505
  have hstable : (prefixWord ++ tailWord_2456505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456505).length < 2 ^ (prefixWord ++ tailWord_2456505).sum := by decide
  have hdescent : baseEnd_2456505 < baseStart_2456505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456561 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 1, 5]
def baseStart_2456561 : Nat := 118140960795 + 2456561 * 2 ^ 59
def prefixEnd_2456561 : Nat := 4983230072969 + 3 ^ 40 * 2456561 * 2
def baseEnd_2456561 : Nat := 840931033393112284993325

theorem tailTrace_2456561 : CollatzResearch.WordTrace tailWord_2456561 prefixEnd_2456561 840931033393112284993325 := by
  unfold tailWord_2456561
  simp only [CollatzResearch.WordTrace]
  refine ⟨89598140453306519062049537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59732093635537679374699691 89598140453306519062049537)
  ·
    refine ⟨67198605339979889296537153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89598140453306519062049537 67198605339979889296537153)
    ·
      refine ⟨50398954004984916972402865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67198605339979889296537153 50398954004984916972402865)
      ·
        refine ⟨37799215503738687729302149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50398954004984916972402865 37799215503738687729302149)
        ·
          refine ⟨7087352906951003949244153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37799215503738687729302149 7087352906951003949244153)
          ·
            refine ⟨5315514680213252961933115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7087352906951003949244153 5315514680213252961933115)
            ·
              refine ⟨7973272020319879442899673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5315514680213252961933115 7973272020319879442899673)
              ·
                refine ⟨5979954015239909582174755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7973272020319879442899673 5979954015239909582174755)
                ·
                  refine ⟨8969931022859864373262133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5979954015239909582174755 8969931022859864373262133)
                  ·
                    refine ⟨840931033393112284993325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8969931022859864373262133 840931033393112284993325)
                    ·
                      rfl

theorem cell22_2456561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_2456561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456561 prefixEnd_2456561 := by exact prefixLift 2456561
  have htrace : WordTrace (prefixWord ++ tailWord_2456561) baseStart_2456561 baseEnd_2456561 := by
    simpa [prefixWord, tailWord_2456561, baseEnd_2456561] using wordTrace_append hprefix tailTrace_2456561
  have hstable : (prefixWord ++ tailWord_2456561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456561).length < 2 ^ (prefixWord ++ tailWord_2456561).sum := by decide
  have hdescent : baseEnd_2456561 < baseStart_2456561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456619 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 7]
def baseStart_2456619 : Nat := 118140960795 + 2456619 * 2 ^ 59
def prefixEnd_2456619 : Nat := 4983230072969 + 3 ^ 40 * 2456619 * 2
def baseEnd_2456619 : Nat := 280316962659473155681049

theorem tailTrace_2456619 : CollatzResearch.WordTrace tailWord_2456619 prefixEnd_2456619 280316962659473155681049 := by
  unfold tailWord_2456619
  simp only [CollatzResearch.WordTrace]
  refine ⟨89600255887096394967660911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59733503924730929978440607 89600255887096394967660911)
  ·
    refine ⟨134400383830644592451491367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89600255887096394967660911 134400383830644592451491367)
    ·
      refine ⟨201600575745966888677237051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134400383830644592451491367 201600575745966888677237051)
      ·
        refine ⟨302400863618950333015855577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201600575745966888677237051 302400863618950333015855577)
        ·
          refine ⟨226800647714212749761891683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302400863618950333015855577 226800647714212749761891683)
          ·
            refine ⟨340200971571319124642837525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226800647714212749761891683 340200971571319124642837525)
            ·
              refine ⟨15946920542405583967633009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 340200971571319124642837525 15946920542405583967633009)
              ·
                refine ⟨11960190406804187975724757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15946920542405583967633009 11960190406804187975724757)
                ·
                  refine ⟨280316962659473155681049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11960190406804187975724757 280316962659473155681049)
                  ·
                    rfl

theorem cell22_2456619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 7].length) (baseStart_2456619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456619 prefixEnd_2456619 := by exact prefixLift 2456619
  have htrace : WordTrace (prefixWord ++ tailWord_2456619) baseStart_2456619 baseEnd_2456619 := by
    simpa [prefixWord, tailWord_2456619, baseEnd_2456619] using wordTrace_append hprefix tailTrace_2456619
  have hstable : (prefixWord ++ tailWord_2456619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456619).length < 2 ^ (prefixWord ++ tailWord_2456619).sum := by decide
  have hdescent : baseEnd_2456619 < baseStart_2456619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456636 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 7]
def baseStart_2456636 : Nat := 118140960795 + 2456636 * 2 ^ 59
def prefixEnd_2456636 : Nat := 4983230072969 + 3 ^ 40 * 2456636 * 2
def baseEnd_2456636 : Nat := 280318902475279029789365

theorem tailTrace_2456636 : CollatzResearch.WordTrace tailWord_2456636 prefixEnd_2456636 280318902475279029789365 := by
  unfold tailWord_2456636
  simp only [CollatzResearch.WordTrace]
  refine ⟨44800437964017403435514881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59733917285356537914019841 44800437964017403435514881)
  ·
    refine ⟨33600328473013052576636161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44800437964017403435514881 33600328473013052576636161)
    ·
      refine ⟨25200246354759789432477121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33600328473013052576636161 25200246354759789432477121)
      ·
        refine ⟨18900184766069842074357841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25200246354759789432477121 18900184766069842074357841)
        ·
          refine ⟨14175138574552381555768381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18900184766069842074357841 14175138574552381555768381)
          ·
            refine ⟨5315676965457143083413143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14175138574552381555768381 5315676965457143083413143)
            ·
              refine ⟨7973515448185714625119715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5315676965457143083413143 7973515448185714625119715)
              ·
                refine ⟨11960273172278571937679573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7973515448185714625119715 11960273172278571937679573)
                ·
                  refine ⟨280318902475279029789365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11960273172278571937679573 280318902475279029789365)
                  ·
                    rfl

theorem cell22_2456636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_2456636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456636 prefixEnd_2456636 := by exact prefixLift 2456636
  have htrace : WordTrace (prefixWord ++ tailWord_2456636) baseStart_2456636 baseEnd_2456636 := by
    simpa [prefixWord, tailWord_2456636, baseEnd_2456636] using wordTrace_append hprefix tailTrace_2456636
  have hstable : (prefixWord ++ tailWord_2456636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456636).length < 2 ^ (prefixWord ++ tailWord_2456636).sum := by decide
  have hdescent : baseEnd_2456636 < baseStart_2456636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456649 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 2, 8]
def baseStart_2456649 : Nat := 118140960795 + 2456649 * 2 ^ 59
def prefixEnd_2456649 : Nat := 4983230072969 + 3 ^ 40 * 2456649 * 2
def baseEnd_2456649 : Nat := 840961157591509388793055

theorem tailTrace_2456649 : CollatzResearch.WordTrace tailWord_2456649 prefixEnd_2456649 840961157591509388793055 := by
  unfold tailWord_2456649
  simp only [CollatzResearch.WordTrace]
  refine ⟨89601350076987710091253001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59734233384658473394168667 89601350076987710091253001)
  ·
    refine ⟨67201012557740782568439751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89601350076987710091253001 67201012557740782568439751)
    ·
      refine ⟨100801518836611173852659627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67201012557740782568439751 100801518836611173852659627)
      ·
        refine ⟨151202278254916760778989441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100801518836611173852659627 151202278254916760778989441)
        ·
          refine ⟨113401708691187570584242081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151202278254916760778989441 113401708691187570584242081)
          ·
            refine ⟨85051281518390677938181561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113401708691187570584242081 85051281518390677938181561)
            ·
              refine ⟨63788461138793008453636171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85051281518390677938181561 63788461138793008453636171)
              ·
                refine ⟨95682691708189512680454257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63788461138793008453636171 95682691708189512680454257)
                ·
                  refine ⟨71762018781142134510340693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95682691708189512680454257 71762018781142134510340693)
                  ·
                    refine ⟨840961157591509388793055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71762018781142134510340693 840961157591509388793055)
                    ·
                      rfl

theorem cell22_2456649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_2456649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456649 prefixEnd_2456649 := by exact prefixLift 2456649
  have htrace : WordTrace (prefixWord ++ tailWord_2456649) baseStart_2456649 baseEnd_2456649 := by
    simpa [prefixWord, tailWord_2456649, baseEnd_2456649] using wordTrace_append hprefix tailTrace_2456649
  have hstable : (prefixWord ++ tailWord_2456649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456649).length < 2 ^ (prefixWord ++ tailWord_2456649).sum := by decide
  have hdescent : baseEnd_2456649 < baseStart_2456649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456670 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2456670 : Nat := 118140960795 + 2456670 * 2 ^ 59
def prefixEnd_2456670 : Nat := 4983230072969 + 3 ^ 40 * 2456670 * 2
def baseEnd_2456670 : Nat := 280322782106890778005997

theorem tailTrace_2456670 : CollatzResearch.WordTrace tailWord_2456670 prefixEnd_2456670 280322782106890778005997 := by
  unfold tailWord_2456670
  simp only [CollatzResearch.WordTrace]
  refine ⟨11200264501238953834720933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59734744006607753785178309 11200264501238953834720933)
  ·
    refine ⟨2100049593982303844010175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11200264501238953834720933 2100049593982303844010175)
    ·
      refine ⟨3150074390973455766015263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2100049593982303844010175 3150074390973455766015263)
      ·
        refine ⟨4725111586460183649022895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3150074390973455766015263 4725111586460183649022895)
        ·
          refine ⟨7087667379690275473534343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4725111586460183649022895 7087667379690275473534343)
          ·
            refine ⟨10631501069535413210301515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7087667379690275473534343 10631501069535413210301515)
            ·
              refine ⟨15947251604303119815452273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10631501069535413210301515 15947251604303119815452273)
              ·
                refine ⟨11960438703227339861589205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15947251604303119815452273 11960438703227339861589205)
                ·
                  refine ⟨280322782106890778005997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11960438703227339861589205 280322782106890778005997)
                  ·
                    rfl

theorem cell22_2456670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2456670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456670 prefixEnd_2456670 := by exact prefixLift 2456670
  have htrace : WordTrace (prefixWord ++ tailWord_2456670) baseStart_2456670 baseEnd_2456670 := by
    simpa [prefixWord, tailWord_2456670, baseEnd_2456670] using wordTrace_append hprefix tailTrace_2456670
  have hstable : (prefixWord ++ tailWord_2456670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456670).length < 2 ^ (prefixWord ++ tailWord_2456670).sum := by decide
  have hdescent : baseEnd_2456670 < baseStart_2456670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456674 : List Nat := [3, 3, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_2456674 : Nat := 118140960795 + 2456674 * 2 ^ 59
def prefixEnd_2456674 : Nat := 4983230072969 + 3 ^ 40 * 2456674 * 2
def baseEnd_2456674 : Nat := 840969715602417656917979

theorem tailTrace_2456674 : CollatzResearch.WordTrace tailWord_2456674 prefixEnd_2456674 840969715602417656917979 := by
  unfold tailWord_2456674
  simp only [CollatzResearch.WordTrace]
  refine ⟨22400565475474284840228269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59734841267931426240608717 22400565475474284840228269)
  ·
    refine ⟨8400212053302856815085601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22400565475474284840228269 8400212053302856815085601)
    ·
      refine ⟨6300159039977142611314201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8400212053302856815085601 6300159039977142611314201)
      ·
        refine ⟨4725119279982856958485651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6300159039977142611314201 4725119279982856958485651)
        ·
          refine ⟨7087678919974285437728477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4725119279982856958485651 7087678919974285437728477)
          ·
            refine ⟨2657879594990357039148179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7087678919974285437728477 2657879594990357039148179)
            ·
              refine ⟨3986819392485535558722269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657879594990357039148179 3986819392485535558722269)
              ·
                refine ⟨1495057272182075834520851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3986819392485535558722269 1495057272182075834520851)
                ·
                  refine ⟨2242585908273113751781277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495057272182075834520851 2242585908273113751781277)
                  ·
                    refine ⟨840969715602417656917979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2242585908273113751781277 840969715602417656917979)
                    ·
                      rfl

theorem cell22_2456674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_2456674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456674 prefixEnd_2456674 := by exact prefixLift 2456674
  have htrace : WordTrace (prefixWord ++ tailWord_2456674) baseStart_2456674 baseEnd_2456674 := by
    simpa [prefixWord, tailWord_2456674, baseEnd_2456674] using wordTrace_append hprefix tailTrace_2456674
  have hstable : (prefixWord ++ tailWord_2456674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456674).length < 2 ^ (prefixWord ++ tailWord_2456674).sum := by decide
  have hdescent : baseEnd_2456674 < baseStart_2456674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456711 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 6, 4]
def baseStart_2456711 : Nat := 118140960795 + 2456711 * 2 ^ 59
def prefixEnd_2456711 : Nat := 4983230072969 + 3 ^ 40 * 2456711 * 2
def baseEnd_2456711 : Nat := 840982381458561893742865

theorem tailTrace_2456711 : CollatzResearch.WordTrace tailWord_2456711 prefixEnd_2456711 840982381458561893742865 := by
  unfold tailWord_2456711
  simp only [CollatzResearch.WordTrace]
  refine ⟨89603611402763094680009987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59735740935175396453339991 89603611402763094680009987)
  ·
    refine ⟨134405417104144642020014981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89603611402763094680009987 134405417104144642020014981)
    ·
      refine ⟨25201015707027120378752809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134405417104144642020014981 25201015707027120378752809)
      ·
        refine ⟨18900761780270340284064607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25201015707027120378752809 18900761780270340284064607)
        ·
          refine ⟨28351142670405510426096911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18900761780270340284064607 28351142670405510426096911)
          ·
            refine ⟨42526714005608265639145367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28351142670405510426096911 42526714005608265639145367)
            ·
              refine ⟨63790071008412398458718051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42526714005608265639145367 63790071008412398458718051)
              ·
                refine ⟨95685106512618597688077077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63790071008412398458718051 95685106512618597688077077)
                ·
                  refine ⟨4485239367778996766628613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 95685106512618597688077077 4485239367778996766628613)
                  ·
                    refine ⟨840982381458561893742865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485239367778996766628613 840982381458561893742865)
                    ·
                      rfl

theorem cell22_2456711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_2456711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456711 prefixEnd_2456711 := by exact prefixLift 2456711
  have htrace : WordTrace (prefixWord ++ tailWord_2456711) baseStart_2456711 baseEnd_2456711 := by
    simpa [prefixWord, tailWord_2456711, baseEnd_2456711] using wordTrace_append hprefix tailTrace_2456711
  have hstable : (prefixWord ++ tailWord_2456711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456711).length < 2 ^ (prefixWord ++ tailWord_2456711).sum := by decide
  have hdescent : baseEnd_2456711 < baseStart_2456711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456728 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 2, 4]
def baseStart_2456728 : Nat := 118140960795 + 2456728 * 2 ^ 59
def prefixEnd_2456728 : Nat := 4983230072969 + 3 ^ 40 * 2456728 * 2
def baseEnd_2456728 : Nat := 840988200905979516067813

theorem tailTrace_2456728 : CollatzResearch.WordTrace tailWord_2456728 prefixEnd_2456728 840988200905979516067813 := by
  unfold tailWord_2456728
  simp only [CollatzResearch.WordTrace]
  refine ⟨44802115721850753291689419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59736154295801004388919225 44802115721850753291689419)
  ·
    refine ⟨67203173582776129937534129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44802115721850753291689419 67203173582776129937534129)
    ·
      refine ⟨50402380187082097453150597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67203173582776129937534129 50402380187082097453150597)
      ·
        refine ⟨9450446285077893272465737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50402380187082097453150597 9450446285077893272465737)
        ·
          refine ⟨7087834713808419954349303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9450446285077893272465737 7087834713808419954349303)
          ·
            refine ⟨10631752070712629931523955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7087834713808419954349303 10631752070712629931523955)
            ·
              refine ⟨15947628106068944897285933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10631752070712629931523955 15947628106068944897285933)
              ·
                refine ⟨5980360539775854336482225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15947628106068944897285933 5980360539775854336482225)
                ·
                  refine ⟨4485270404831890752361669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5980360539775854336482225 4485270404831890752361669)
                  ·
                    refine ⟨840988200905979516067813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485270404831890752361669 840988200905979516067813)
                    ·
                      rfl

theorem cell22_2456728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_2456728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456728 prefixEnd_2456728 := by exact prefixLift 2456728
  have htrace : WordTrace (prefixWord ++ tailWord_2456728) baseStart_2456728 baseEnd_2456728 := by
    simpa [prefixWord, tailWord_2456728, baseEnd_2456728] using wordTrace_append hprefix tailTrace_2456728
  have hstable : (prefixWord ++ tailWord_2456728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456728).length < 2 ^ (prefixWord ++ tailWord_2456728).sum := by decide
  have hdescent : baseEnd_2456728 < baseStart_2456728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456749 : List Nat := [1, 5, 2, 1, 3, 2, 2, 2, 4]
def baseStart_2456749 : Nat := 118140960795 + 2456749 * 2 ^ 59
def prefixEnd_2456749 : Nat := 4983230072969 + 3 ^ 40 * 2456749 * 2
def baseEnd_2456749 : Nat := 280331796545047487097583

theorem tailTrace_2456749 : CollatzResearch.WordTrace tailWord_2456749 prefixEnd_2456749 280331796545047487097583 := by
  unfold tailWord_2456749
  simp only [CollatzResearch.WordTrace]
  refine ⟨89604997376625427169893301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59736664917750284779928867 89604997376625427169893301)
  ·
    refine ⟨8400468504058633797177497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89604997376625427169893301 8400468504058633797177497)
    ·
      refine ⟨6300351378043975347883123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8400468504058633797177497 6300351378043975347883123)
      ·
        refine ⟨9450527067065963021824685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6300351378043975347883123 9450527067065963021824685)
        ·
          refine ⟨3543947650149736133184257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9450527067065963021824685 3543947650149736133184257)
          ·
            refine ⟨2657960737612302099888193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3543947650149736133184257 2657960737612302099888193)
            ·
              refine ⟨1993470553209226574916145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2657960737612302099888193 1993470553209226574916145)
              ·
                refine ⟨1495102914906919931187109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1993470553209226574916145 1495102914906919931187109)
                ·
                  refine ⟨280331796545047487097583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1495102914906919931187109 280331796545047487097583)
                  ·
                    rfl

theorem cell22_2456749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_2456749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456749 prefixEnd_2456749 := by exact prefixLift 2456749
  have htrace : WordTrace (prefixWord ++ tailWord_2456749) baseStart_2456749 baseEnd_2456749 := by
    simpa [prefixWord, tailWord_2456749, baseEnd_2456749] using wordTrace_append hprefix tailTrace_2456749
  have hstable : (prefixWord ++ tailWord_2456749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456749).length < 2 ^ (prefixWord ++ tailWord_2456749).sum := by decide
  have hdescent : baseEnd_2456749 < baseStart_2456749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456833 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 6]
def baseStart_2456833 : Nat := 118140960795 + 2456833 * 2 ^ 59
def prefixEnd_2456833 : Nat := 4983230072969 + 3 ^ 40 * 2456833 * 2
def baseEnd_2456833 : Nat := 280341381517264747397497

theorem tailTrace_2456833 : CollatzResearch.WordTrace tailWord_2456833 prefixEnd_2456833 280341381517264747397497 := by
  unfold tailWord_2456833
  simp only [CollatzResearch.WordTrace]
  refine ⟨89608061108321109515951153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59738707405547406343967435 89608061108321109515951153)
  ·
    refine ⟨67206045831240832136963365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89608061108321109515951153 67206045831240832136963365)
    ·
      refine ⟨12601133593357656025680631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67206045831240832136963365 12601133593357656025680631)
      ·
        refine ⟨18901700390036484038520947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12601133593357656025680631 18901700390036484038520947)
        ·
          refine ⟨28352550585054726057781421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18901700390036484038520947 28352550585054726057781421)
          ·
            refine ⟨10632206469395522271668033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28352550585054726057781421 10632206469395522271668033)
            ·
              refine ⟨7974154852046641703751025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10632206469395522271668033 7974154852046641703751025)
              ·
                refine ⟨5980616139034981277813269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7974154852046641703751025 5980616139034981277813269)
                ·
                  refine ⟨280341381517264747397497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5980616139034981277813269 280341381517264747397497)
                  ·
                    rfl

theorem cell22_2456833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 6].length) (baseStart_2456833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456833 prefixEnd_2456833 := by exact prefixLift 2456833
  have htrace : WordTrace (prefixWord ++ tailWord_2456833) baseStart_2456833 baseEnd_2456833 := by
    simpa [prefixWord, tailWord_2456833, baseEnd_2456833] using wordTrace_append hprefix tailTrace_2456833
  have hstable : (prefixWord ++ tailWord_2456833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456833).length < 2 ^ (prefixWord ++ tailWord_2456833).sum := by decide
  have hdescent : baseEnd_2456833 < baseStart_2456833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456835 : List Nat := [1, 1, 1, 3, 2, 5, 2, 2, 1, 4]
def baseStart_2456835 : Nat := 118140960795 + 2456835 * 2 ^ 59
def prefixEnd_2456835 : Nat := 4983230072969 + 3 ^ 40 * 2456835 * 2
def baseEnd_2456835 : Nat := 841024829192666903642485

theorem tailTrace_2456835 : CollatzResearch.WordTrace tailWord_2456835 prefixEnd_2456835 841024829192666903642485 := by
  unfold tailWord_2456835
  simp only [CollatzResearch.WordTrace]
  refine ⟨89608134054313863857523959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59738756036209242571682639 89608134054313863857523959)
  ·
    refine ⟨134412201081470795786285939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89608134054313863857523959 134412201081470795786285939)
    ·
      refine ⟨201618301622206193679428909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134412201081470795786285939 201618301622206193679428909)
      ·
        refine ⟨75606863108327322629785841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201618301622206193679428909 75606863108327322629785841)
        ·
          refine ⟨56705147331245491972339381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75606863108327322629785841 56705147331245491972339381)
          ·
            refine ⟨5316107562304264872406817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56705147331245491972339381 5316107562304264872406817)
            ·
              refine ⟨3987080671728198654305113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5316107562304264872406817 3987080671728198654305113)
              ·
                refine ⟨2990310503796148990728835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3987080671728198654305113 2990310503796148990728835)
                ·
                  refine ⟨4485465755694223486093253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2990310503796148990728835 4485465755694223486093253)
                  ·
                    refine ⟨841024829192666903642485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485465755694223486093253 841024829192666903642485)
                    ·
                      rfl

theorem cell22_2456835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 4].length) (baseStart_2456835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456835 prefixEnd_2456835 := by exact prefixLift 2456835
  have htrace : WordTrace (prefixWord ++ tailWord_2456835) baseStart_2456835 baseEnd_2456835 := by
    simpa [prefixWord, tailWord_2456835, baseEnd_2456835] using wordTrace_append hprefix tailTrace_2456835
  have hstable : (prefixWord ++ tailWord_2456835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456835).length < 2 ^ (prefixWord ++ tailWord_2456835).sum := by decide
  have hdescent : baseEnd_2456835 < baseStart_2456835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456865 : List Nat := [1, 2, 3, 2, 1, 1, 1, 6, 2, 3]
def baseStart_2456865 : Nat := 118140960795 + 2456865 * 2 ^ 59
def prefixEnd_2456865 : Nat := 4983230072969 + 3 ^ 40 * 2456865 * 2
def baseEnd_2456865 : Nat := 841035098805756825392393

theorem tailTrace_2456865 : CollatzResearch.WordTrace tailWord_2456865 prefixEnd_2456865 841035098805756825392393 := by
  unfold tailWord_2456865
  simp only [CollatzResearch.WordTrace]
  refine ⟨89609228244205178981116049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59739485496136785987410699 89609228244205178981116049)
  ·
    refine ⟨67206921183153884235837037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89609228244205178981116049 67206921183153884235837037)
    ·
      refine ⟨25202595443682706588438889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67206921183153884235837037 25202595443682706588438889)
      ·
        refine ⟨18901946582762029941329167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25202595443682706588438889 18901946582762029941329167)
        ·
          refine ⟨28352919874143044911993751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18901946582762029941329167 28352919874143044911993751)
          ·
            refine ⟨42529379811214567367990627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28352919874143044911993751 42529379811214567367990627)
            ·
              refine ⟨63794069716821851051985941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42529379811214567367990627 63794069716821851051985941)
              ·
                refine ⟨2990347017976024268061841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63794069716821851051985941 2990347017976024268061841)
                ·
                  refine ⟨2242760263482018201046381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2990347017976024268061841 2242760263482018201046381)
                  ·
                    refine ⟨841035098805756825392393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2242760263482018201046381 841035098805756825392393)
                    ·
                      rfl

theorem cell22_2456865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_2456865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456865 prefixEnd_2456865 := by exact prefixLift 2456865
  have htrace : WordTrace (prefixWord ++ tailWord_2456865) baseStart_2456865 baseEnd_2456865 := by
    simpa [prefixWord, tailWord_2456865, baseEnd_2456865] using wordTrace_append hprefix tailTrace_2456865
  have hstable : (prefixWord ++ tailWord_2456865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456865).length < 2 ^ (prefixWord ++ tailWord_2456865).sum := by decide
  have hdescent : baseEnd_2456865 < baseStart_2456865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456867 : List Nat := [1, 1, 1, 4, 2, 4, 3, 2, 4]
def baseStart_2456867 : Nat := 118140960795 + 2456867 * 2 ^ 59
def prefixEnd_2456867 : Nat := 4983230072969 + 3 ^ 40 * 2456867 * 2
def baseEnd_2456867 : Nat := 280345261148876495614129

theorem tailTrace_2456867 : CollatzResearch.WordTrace tailWord_2456867 prefixEnd_2456867 280345261148876495614129 := by
  unfold tailWord_2456867
  simp only [CollatzResearch.WordTrace]
  refine ⟨89609301190197933322688855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59739534126798622215125903 89609301190197933322688855)
  ·
    refine ⟨134413951785296899984033283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89609301190197933322688855 134413951785296899984033283)
    ·
      refine ⟨201620927677945349976049925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134413951785296899984033283 201620927677945349976049925)
      ·
        refine ⟨37803923939614753120509361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201620927677945349976049925 37803923939614753120509361)
        ·
          refine ⟨28352942954711064840382021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37803923939614753120509361 28352942954711064840382021)
          ·
            refine ⟨5316176804008324657571629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28352942954711064840382021 5316176804008324657571629)
            ·
              refine ⟨1993566301503121746589361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5316176804008324657571629 1993566301503121746589361)
              ·
                refine ⟨1495174726127341309942021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1993566301503121746589361 1495174726127341309942021)
                ·
                  refine ⟨280345261148876495614129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1495174726127341309942021 280345261148876495614129)
                  ·
                    rfl

theorem cell22_2456867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 4].length) (baseStart_2456867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456867 prefixEnd_2456867 := by exact prefixLift 2456867
  have htrace : WordTrace (prefixWord ++ tailWord_2456867) baseStart_2456867 baseEnd_2456867 := by
    simpa [prefixWord, tailWord_2456867, baseEnd_2456867] using wordTrace_append hprefix tailTrace_2456867
  have hstable : (prefixWord ++ tailWord_2456867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456867).length < 2 ^ (prefixWord ++ tailWord_2456867).sum := by decide
  have hdescent : baseEnd_2456867 < baseStart_2456867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456882 : List Nat := [3, 2, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_2456882 : Nat := 118140960795 + 2456882 * 2 ^ 59
def prefixEnd_2456882 : Nat := 4983230072969 + 3 ^ 40 * 2456882 * 2
def baseEnd_2456882 : Nat := 841040918253174447717341

theorem tailTrace_2456882 : CollatzResearch.WordTrace tailWord_2456882 prefixEnd_2456882 841040918253174447717341 := by
  unfold tailWord_2456882
  simp only [CollatzResearch.WordTrace]
  refine ⟨22402462071285897721121225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59739898856762393922989933 22402462071285897721121225)
  ·
    refine ⟨16801846553464423290840919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22402462071285897721121225 16801846553464423290840919)
    ·
      refine ⟨25202769830196634936261379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16801846553464423290840919 25202769830196634936261379)
      ·
        refine ⟨37804154745294952404392069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25202769830196634936261379 37804154745294952404392069)
        ·
          refine ⟨7088279014742803575823513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37804154745294952404392069 7088279014742803575823513)
          ·
            refine ⟨5316209261057102681867635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7088279014742803575823513 5316209261057102681867635)
            ·
              refine ⟨7974313891585654022801453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5316209261057102681867635 7974313891585654022801453)
              ·
                refine ⟨2990367709344620258550545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7974313891585654022801453 2990367709344620258550545)
                ·
                  refine ⟨2242775782008465193912909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2990367709344620258550545 2242775782008465193912909)
                  ·
                    refine ⟨841040918253174447717341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2242775782008465193912909 841040918253174447717341)
                    ·
                      rfl

theorem cell22_2456882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_2456882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456882 prefixEnd_2456882 := by exact prefixLift 2456882
  have htrace : WordTrace (prefixWord ++ tailWord_2456882) baseStart_2456882 baseEnd_2456882 := by
    simpa [prefixWord, tailWord_2456882, baseEnd_2456882] using wordTrace_append hprefix tailTrace_2456882
  have hstable : (prefixWord ++ tailWord_2456882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456882).length < 2 ^ (prefixWord ++ tailWord_2456882).sum := by decide
  have hdescent : baseEnd_2456882 < baseStart_2456882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456886 : List Nat := [5, 1, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_2456886 : Nat := 118140960795 + 2456886 * 2 ^ 59
def prefixEnd_2456886 : Nat := 4983230072969 + 3 ^ 40 * 2456886 * 2
def baseEnd_2456886 : Nat := 841042287534919770617329

theorem tailTrace_2456886 : CollatzResearch.WordTrace tailWord_2456886 prefixEnd_2456886 841042287534919770617329 := by
  unfold tailWord_2456886
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600624636070568722976907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59739996118086066378420341 5600624636070568722976907)
  ·
    refine ⟨8400936954105853084465361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5600624636070568722976907 8400936954105853084465361)
    ·
      refine ⟨6300702715579389813349021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8400936954105853084465361 6300702715579389813349021)
      ·
        refine ⟨2362763518342271180005883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6300702715579389813349021 2362763518342271180005883)
        ·
          refine ⟨3544145277513406770008825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2362763518342271180005883 3544145277513406770008825)
          ·
            refine ⟨2658108958135055077506619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3544145277513406770008825 2658108958135055077506619)
            ·
              refine ⟨3987163437202582616259929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2658108958135055077506619 3987163437202582616259929)
              ·
                refine ⟨2990372577901936962194947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3987163437202582616259929 2990372577901936962194947)
                ·
                  refine ⟨4485558866852905443292421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2990372577901936962194947 4485558866852905443292421)
                  ·
                    refine ⟨841042287534919770617329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485558866852905443292421 841042287534919770617329)
                    ·
                      rfl

theorem cell22_2456886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_2456886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456886 prefixEnd_2456886 := by exact prefixLift 2456886
  have htrace : WordTrace (prefixWord ++ tailWord_2456886) baseStart_2456886 baseEnd_2456886 := by
    simpa [prefixWord, tailWord_2456886, baseEnd_2456886] using wordTrace_append hprefix tailTrace_2456886
  have hstable : (prefixWord ++ tailWord_2456886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456886).length < 2 ^ (prefixWord ++ tailWord_2456886).sum := by decide
  have hdescent : baseEnd_2456886 < baseStart_2456886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456897 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2456897 : Nat := 118140960795 + 2456897 * 2 ^ 59
def prefixEnd_2456897 : Nat := 4983230072969 + 3 ^ 40 * 2456897 * 2
def baseEnd_2456897 : Nat := 841046053059719408592295

theorem tailTrace_2456897 : CollatzResearch.WordTrace tailWord_2456897 prefixEnd_2456897 841046053059719408592295 := by
  unfold tailWord_2456897
  simp only [CollatzResearch.WordTrace]
  refine ⟨89610395380089248446280945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59740263586726165630853963 89610395380089248446280945)
  ·
    refine ⟨67207796535066936334710709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89610395380089248446280945 67207796535066936334710709)
    ·
      refine ⟨6300730925162525281379129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67207796535066936334710709 6300730925162525281379129)
      ·
        refine ⟨4725548193871893961034347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6300730925162525281379129 4725548193871893961034347)
        ·
          refine ⟨7088322290807840941551521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4725548193871893961034347 7088322290807840941551521)
          ·
            refine ⟨5316241718105880706163641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7088322290807840941551521 5316241718105880706163641)
            ·
              refine ⟨3987181288579410529622731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5316241718105880706163641 3987181288579410529622731)
              ·
                refine ⟨5980771932869115794434097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3987181288579410529622731 5980771932869115794434097)
                ·
                  refine ⟨4485578949651836845825573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5980771932869115794434097 4485578949651836845825573)
                  ·
                    refine ⟨841046053059719408592295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485578949651836845825573 841046053059719408592295)
                    ·
                      rfl

theorem cell22_2456897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2456897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456897 prefixEnd_2456897 := by exact prefixLift 2456897
  have htrace : WordTrace (prefixWord ++ tailWord_2456897) baseStart_2456897 baseEnd_2456897 := by
    simpa [prefixWord, tailWord_2456897, baseEnd_2456897] using wordTrace_append hprefix tailTrace_2456897
  have hstable : (prefixWord ++ tailWord_2456897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456897).length < 2 ^ (prefixWord ++ tailWord_2456897).sum := by decide
  have hdescent : baseEnd_2456897 < baseStart_2456897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456918 : List Nat := [5, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_2456918 : Nat := 118140960795 + 2456918 * 2 ^ 59
def prefixEnd_2456918 : Nat := 4983230072969 + 3 ^ 40 * 2456918 * 2
def baseEnd_2456918 : Nat := 280351080596294117939077

theorem tailTrace_2456918 : CollatzResearch.WordTrace tailWord_2456918 prefixEnd_2456918 280351080596294117939077 := by
  unfold tailWord_2456918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600697582063323064549713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59740774208675446021863605 5600697582063323064549713)
  ·
    refine ⟨4200523186547492298412285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5600697582063323064549713 4200523186547492298412285)
    ·
      refine ⟨1575196194955309611904607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4200523186547492298412285 1575196194955309611904607)
      ·
        refine ⟨2362794292432964417856911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1575196194955309611904607 2362794292432964417856911)
        ·
          refine ⟨3544191438649446626785367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2362794292432964417856911 3544191438649446626785367)
          ·
            refine ⟨5316287157974169940178051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544191438649446626785367 5316287157974169940178051)
            ·
              refine ⟨7974430736961254910267077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5316287157974169940178051 7974430736961254910267077)
              ·
                refine ⟨1495205763180235295675077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7974430736961254910267077 1495205763180235295675077)
                ·
                  refine ⟨280351080596294117939077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1495205763180235295675077 280351080596294117939077)
                  ·
                    rfl

theorem cell22_2456918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_2456918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456918 prefixEnd_2456918 := by exact prefixLift 2456918
  have htrace : WordTrace (prefixWord ++ tailWord_2456918) baseStart_2456918 baseEnd_2456918 := by
    simpa [prefixWord, tailWord_2456918, baseEnd_2456918] using wordTrace_append hprefix tailTrace_2456918
  have hstable : (prefixWord ++ tailWord_2456918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456918).length < 2 ^ (prefixWord ++ tailWord_2456918).sum := by decide
  have hdescent : baseEnd_2456918 < baseStart_2456918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456940 : List Nat := [2, 2, 1, 1, 5, 1, 2, 3, 5]
def baseStart_2456940 : Nat := 118140960795 + 2456940 * 2 ^ 59
def prefixEnd_2456940 : Nat := 4983230072969 + 3 ^ 40 * 2456940 * 2
def baseEnd_2456940 : Nat := 280353590946160543255721

theorem tailTrace_2456940 : CollatzResearch.WordTrace tailWord_2456940 prefixEnd_2456940 280353590946160543255721 := by
  unfold tailWord_2456940
  simp only [CollatzResearch.WordTrace]
  refine ⟨44805981859466733395048137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59741309145955644526730849 44805981859466733395048137)
  ·
    refine ⟨33604486394600050046286103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44805981859466733395048137 33604486394600050046286103)
    ·
      refine ⟨50406729591900075069429155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33604486394600050046286103 50406729591900075069429155)
      ·
        refine ⟨75610094387850112604143733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50406729591900075069429155 75610094387850112604143733)
        ·
          refine ⟨7088446348860948056638475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75610094387850112604143733 7088446348860948056638475)
          ·
            refine ⟨10632669523291422084957713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7088446348860948056638475 10632669523291422084957713)
            ·
              refine ⟨7974502142468566563718285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10632669523291422084957713 7974502142468566563718285)
              ·
                refine ⟨2990438303425712461394357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7974502142468566563718285 2990438303425712461394357)
                ·
                  refine ⟨280353590946160543255721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2990438303425712461394357 280353590946160543255721)
                  ·
                    rfl

theorem cell22_2456940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_2456940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456940 prefixEnd_2456940 := by exact prefixLift 2456940
  have htrace : WordTrace (prefixWord ++ tailWord_2456940) baseStart_2456940 baseEnd_2456940 := by
    simpa [prefixWord, tailWord_2456940, baseEnd_2456940] using wordTrace_append hprefix tailTrace_2456940
  have hstable : (prefixWord ++ tailWord_2456940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456940).length < 2 ^ (prefixWord ++ tailWord_2456940).sum := by decide
  have hdescent : baseEnd_2456940 < baseStart_2456940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456961 : List Nat := [1, 2, 4, 3, 2, 1, 2, 3, 1, 3]
def baseStart_2456961 : Nat := 118140960795 + 2456961 * 2 ^ 59
def prefixEnd_2456961 : Nat := 4983230072969 + 3 ^ 40 * 2456961 * 2
def baseEnd_2456961 : Nat := 841067961567644574992099

theorem tailTrace_2456961 : CollatzResearch.WordTrace tailWord_2456961 prefixEnd_2456961 841067961567644574992099 := by
  unfold tailWord_2456961
  simp only [CollatzResearch.WordTrace]
  refine ⟨89612729651857387376610737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59741819767904924917740491 89612729651857387376610737)
  ·
    refine ⟨67209547238893040532458053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89612729651857387376610737 67209547238893040532458053)
    ·
      refine ⟨12601790107292445099835885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67209547238893040532458053 12601790107292445099835885)
      ·
        refine ⟨4725671290234666912438457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12601790107292445099835885 4725671290234666912438457)
        ·
          refine ⟨3544253467676000184328843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4725671290234666912438457 3544253467676000184328843)
          ·
            refine ⟨5316380201514000276493265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544253467676000184328843 5316380201514000276493265)
            ·
              refine ⟨3987285151135500207369949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5316380201514000276493265 3987285151135500207369949)
              ·
                refine ⟨1495231931675812577763731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3987285151135500207369949 1495231931675812577763731)
                ·
                  refine ⟨2242847897513718866645597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495231931675812577763731 2242847897513718866645597)
                  ·
                    refine ⟨841067961567644574992099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2242847897513718866645597 841067961567644574992099)
                    ·
                      rfl

theorem cell22_2456961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_2456961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456961 prefixEnd_2456961 := by exact prefixLift 2456961
  have htrace : WordTrace (prefixWord ++ tailWord_2456961) baseStart_2456961 baseEnd_2456961 := by
    simpa [prefixWord, tailWord_2456961, baseEnd_2456961] using wordTrace_append hprefix tailTrace_2456961
  have hstable : (prefixWord ++ tailWord_2456961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456961).length < 2 ^ (prefixWord ++ tailWord_2456961).sum := by decide
  have hdescent : baseEnd_2456961 < baseStart_2456961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456974 : List Nat := [4, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_2456974 : Nat := 118140960795 + 2456974 * 2 ^ 59
def prefixEnd_2456974 : Nat := 4983230072969 + 3 ^ 40 * 2456974 * 2
def baseEnd_2456974 : Nat := 280357470577772291472353

theorem tailTrace_2456974 : CollatzResearch.WordTrace tailWord_2456974 prefixEnd_2456974 280357470577772291472353 := by
  unfold tailWord_2456974
  simp only [CollatzResearch.WordTrace]
  refine ⟨11201650475101286324604247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59742135867206860397889317 11201650475101286324604247)
  ·
    refine ⟨16802475712651929486906371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11201650475101286324604247 16802475712651929486906371)
    ·
      refine ⟨25203713568977894230359557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16802475712651929486906371 25203713568977894230359557)
      ·
        refine ⟨4725696294183355168192417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25203713568977894230359557 4725696294183355168192417)
        ·
          refine ⟨3544272220637516376144313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4725696294183355168192417 3544272220637516376144313)
          ·
            refine ⟨2658204165478137282108235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3544272220637516376144313 2658204165478137282108235)
            ·
              refine ⟨3987306248217205923162353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2658204165478137282108235 3987306248217205923162353)
              ·
                refine ⟨2990479686162904442371765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3987306248217205923162353 2990479686162904442371765)
                ·
                  refine ⟨280357470577772291472353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2990479686162904442371765 280357470577772291472353)
                  ·
                    rfl

theorem cell22_2456974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_2456974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456974 prefixEnd_2456974 := by exact prefixLift 2456974
  have htrace : WordTrace (prefixWord ++ tailWord_2456974) baseStart_2456974 baseEnd_2456974 := by
    simpa [prefixWord, tailWord_2456974, baseEnd_2456974] using wordTrace_append hprefix tailTrace_2456974
  have hstable : (prefixWord ++ tailWord_2456974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456974).length < 2 ^ (prefixWord ++ tailWord_2456974).sum := by decide
  have hdescent : baseEnd_2456974 < baseStart_2456974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2456985 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 6]
def baseStart_2456985 : Nat := 118140960795 + 2456985 * 2 ^ 59
def prefixEnd_2456985 : Nat := 4983230072969 + 3 ^ 40 * 2456985 * 2
def baseEnd_2456985 : Nat := 280358725752705504130675

theorem tailTrace_2456985 : CollatzResearch.WordTrace tailWord_2456985 prefixEnd_2456985 280358725752705504130675 := by
  unfold tailWord_2456985
  simp only [CollatzResearch.WordTrace]
  refine ⟨89613605003770439475484409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59742403335846959650322939 89613605003770439475484409)
  ·
    refine ⟨67210203752827829606613307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89613605003770439475484409 67210203752827829606613307)
    ·
      refine ⟨100815305629241744409919961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67210203752827829606613307 100815305629241744409919961)
      ·
        refine ⟨75611479221931308307439971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100815305629241744409919961 75611479221931308307439971)
        ·
          refine ⟨113417218832896962461159957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75611479221931308307439971 113417218832896962461159957)
          ·
            refine ⟨5316432132792045115366873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 113417218832896962461159957 5316432132792045115366873)
            ·
              refine ⟨3987324099594033836525155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5316432132792045115366873 3987324099594033836525155)
              ·
                refine ⟨5980986149391050754787733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3987324099594033836525155 5980986149391050754787733)
                ·
                  refine ⟨280358725752705504130675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5980986149391050754787733 280358725752705504130675)
                  ·
                    rfl

theorem cell22_2456985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 6].length) (baseStart_2456985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2456985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2456985 prefixEnd_2456985 := by exact prefixLift 2456985
  have htrace : WordTrace (prefixWord ++ tailWord_2456985) baseStart_2456985 baseEnd_2456985 := by
    simpa [prefixWord, tailWord_2456985, baseEnd_2456985] using wordTrace_append hprefix tailTrace_2456985
  have hstable : (prefixWord ++ tailWord_2456985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2456985).length < 2 ^ (prefixWord ++ tailWord_2456985).sum := by decide
  have hdescent : baseEnd_2456985 < baseStart_2456985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2456985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457015 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 2, 4]
def baseStart_2457015 : Nat := 118140960795 + 2457015 * 2 ^ 59
def prefixEnd_2457015 : Nat := 4983230072969 + 3 ^ 40 * 2457015 * 2
def baseEnd_2457015 : Nat := 841086446871206434141933

theorem tailTrace_2457015 : CollatzResearch.WordTrace tailWord_2457015 prefixEnd_2457015 841086446871206434141933 := by
  unfold tailWord_2457015
  simp only [CollatzResearch.WordTrace]
  refine ⟨89614699193661754599076499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59743132795774503066050999 89614699193661754599076499)
  ·
    refine ⟨134422048790492631898614749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89614699193661754599076499 134422048790492631898614749)
    ·
      refine ⟨50408268296434736961980531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134422048790492631898614749 50408268296434736961980531)
      ·
        refine ⟨75612402444652105442970797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50408268296434736961980531 75612402444652105442970797)
        ·
          refine ⟨28354650916744539541114049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75612402444652105442970797 28354650916744539541114049)
          ·
            refine ⟨21265988187558404655835537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28354650916744539541114049 21265988187558404655835537)
            ·
              refine ⟨15949491140668803491876653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21265988187558404655835537 15949491140668803491876653)
              ·
                refine ⟨5981059177750801309453745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15949491140668803491876653 5981059177750801309453745)
                ·
                  refine ⟨4485794383313100982090309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5981059177750801309453745 4485794383313100982090309)
                  ·
                    refine ⟨841086446871206434141933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485794383313100982090309 841086446871206434141933)
                    ·
                      rfl

theorem cell22_2457015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_2457015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457015 prefixEnd_2457015 := by exact prefixLift 2457015
  have htrace : WordTrace (prefixWord ++ tailWord_2457015) baseStart_2457015 baseEnd_2457015 := by
    simpa [prefixWord, tailWord_2457015, baseEnd_2457015] using wordTrace_append hprefix tailTrace_2457015
  have hstable : (prefixWord ++ tailWord_2457015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457015).length < 2 ^ (prefixWord ++ tailWord_2457015).sum := by decide
  have hdescent : baseEnd_2457015 < baseStart_2457015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457096 : List Nat := [2, 1, 3, 2, 1, 1, 6, 2, 1, 3]
def baseStart_2457096 : Nat := 118140960795 + 2457096 * 2 ^ 59
def prefixEnd_2457096 : Nat := 4983230072969 + 3 ^ 40 * 2457096 * 2
def baseEnd_2457096 : Nat := 841114174826549222866685

theorem tailTrace_2457096 : CollatzResearch.WordTrace tailWord_2457096 prefixEnd_2457096 841114174826549222866685 := by
  unfold tailWord_2457096
  simp only [CollatzResearch.WordTrace]
  refine ⟨44808826753184152716387571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59745102337578870288516761 44808826753184152716387571)
  ·
    refine ⟨67213240129776229074581357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44808826753184152716387571 67213240129776229074581357)
    ·
      refine ⟨25204965048666085902968009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67213240129776229074581357 25204965048666085902968009)
      ·
        refine ⟨18903723786499564427226007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25204965048666085902968009 18903723786499564427226007)
        ·
          refine ⟨28355585679749346640839011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18903723786499564427226007 28355585679749346640839011)
          ·
            refine ⟨42533378519624019961258517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28355585679749346640839011 42533378519624019961258517)
            ·
              refine ⟨1993752118107375935683993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42533378519624019961258517 1993752118107375935683993)
              ·
                refine ⟨1495314088580531951762995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1993752118107375935683993 1495314088580531951762995)
                ·
                  refine ⟨2242971132870797927644493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495314088580531951762995 2242971132870797927644493)
                  ·
                    refine ⟨841114174826549222866685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2242971132870797927644493 841114174826549222866685)
                    ·
                      rfl

theorem cell22_2457096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_2457096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457096 prefixEnd_2457096 := by exact prefixLift 2457096
  have htrace : WordTrace (prefixWord ++ tailWord_2457096) baseStart_2457096 baseEnd_2457096 := by
    simpa [prefixWord, tailWord_2457096, baseEnd_2457096] using wordTrace_append hprefix tailTrace_2457096
  have hstable : (prefixWord ++ tailWord_2457096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457096).length < 2 ^ (prefixWord ++ tailWord_2457096).sum := by decide
  have hdescent : baseEnd_2457096 < baseStart_2457096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457105 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 5, 4]
def baseStart_2457105 : Nat := 118140960795 + 2457105 * 2 ^ 59
def prefixEnd_2457105 : Nat := 4983230072969 + 3 ^ 40 * 2457105 * 2
def baseEnd_2457105 : Nat := 841117255710476199391657

theorem tailTrace_2457105 : CollatzResearch.WordTrace tailWord_2457105 prefixEnd_2457105 841117255710476199391657 := by
  unfold tailWord_2457105
  simp only [CollatzResearch.WordTrace]
  refine ⟨89617981763335699969852769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59745321175557133313235179 89617981763335699969852769)
  ·
    refine ⟨67213486322501774977389577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89617981763335699969852769 67213486322501774977389577)
    ·
      refine ⟨50410114741876331233042183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67213486322501774977389577 50410114741876331233042183)
      ·
        refine ⟨75615172112814496849563275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50410114741876331233042183 75615172112814496849563275)
        ·
          refine ⟨113422758169221745274344913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75615172112814496849563275 113422758169221745274344913)
          ·
            refine ⟨85067068626916308955758685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113422758169221745274344913 85067068626916308955758685)
            ·
              refine ⟨31900150735093615858409507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85067068626916308955758685 31900150735093615858409507)
              ·
                refine ⟨47850226102640423787614261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31900150735093615858409507 47850226102640423787614261)
                ·
                  refine ⟨4485958697122539730088837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47850226102640423787614261 4485958697122539730088837)
                  ·
                    refine ⟨841117255710476199391657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485958697122539730088837 841117255710476199391657)
                    ·
                      rfl

theorem cell22_2457105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_2457105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457105 prefixEnd_2457105 := by exact prefixLift 2457105
  have htrace : WordTrace (prefixWord ++ tailWord_2457105) baseStart_2457105 baseEnd_2457105 := by
    simpa [prefixWord, tailWord_2457105, baseEnd_2457105] using wordTrace_append hprefix tailTrace_2457105
  have hstable : (prefixWord ++ tailWord_2457105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457105).length < 2 ^ (prefixWord ++ tailWord_2457105).sum := by decide
  have hdescent : baseEnd_2457105 < baseStart_2457105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457122 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2457122 : Nat := 118140960795 + 2457122 * 2 ^ 59
def prefixEnd_2457122 : Nat := 4983230072969 + 3 ^ 40 * 2457122 * 2
def baseEnd_2457122 : Nat := 841123075157893821716605

theorem tailTrace_2457122 : CollatzResearch.WordTrace tailWord_2457122 prefixEnd_2457122 841123075157893821716605 := by
  unfold tailWord_2457122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22404650451068527968305405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59745734536182741248814413 22404650451068527968305405)
  ·
    refine ⟨8401743919150697988114527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22404650451068527968305405 8401743919150697988114527)
    ·
      refine ⟨12602615878726046982171791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8401743919150697988114527 12602615878726046982171791)
      ·
        refine ⟨18903923818089070473257687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12602615878726046982171791 18903923818089070473257687)
        ·
          refine ⟨28355885727133605709886531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18903923818089070473257687 28355885727133605709886531)
          ·
            refine ⟨42533828590700408564829797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28355885727133605709886531 42533828590700408564829797)
            ·
              refine ⟨7975092860756326605905587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42533828590700408564829797 7975092860756326605905587)
              ·
                refine ⟨11962639291134489908858381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7975092860756326605905587 11962639291134489908858381)
                ·
                  refine ⟨4485989734175433715821893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11962639291134489908858381 4485989734175433715821893)
                  ·
                    refine ⟨841123075157893821716605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4485989734175433715821893 841123075157893821716605)
                    ·
                      rfl

theorem cell22_2457122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2457122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457122 prefixEnd_2457122 := by exact prefixLift 2457122
  have htrace : WordTrace (prefixWord ++ tailWord_2457122) baseStart_2457122 baseEnd_2457122 := by
    simpa [prefixWord, tailWord_2457122, baseEnd_2457122] using wordTrace_append hprefix tailTrace_2457122
  have hstable : (prefixWord ++ tailWord_2457122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457122).length < 2 ^ (prefixWord ++ tailWord_2457122).sum := by decide
  have hdescent : baseEnd_2457122 < baseStart_2457122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457139 : List Nat := [1, 1, 1, 2, 4, 3, 4, 1, 1, 4]
def baseStart_2457139 : Nat := 118140960795 + 2457139 * 2 ^ 59
def prefixEnd_2457139 : Nat := 4983230072969 + 3 ^ 40 * 2457139 * 2
def baseEnd_2457139 : Nat := 841128894605311444041553

theorem tailTrace_2457139 : CollatzResearch.WordTrace tailWord_2457139 prefixEnd_2457139 841128894605311444041553 := by
  unfold tailWord_2457139
  simp only [CollatzResearch.WordTrace]
  refine ⟨89619221845212523776590471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59746147896808349184393647 89619221845212523776590471)
  ·
    refine ⟨134428832767818785664885707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89619221845212523776590471 134428832767818785664885707)
    ·
      refine ⟨201643249151728178497328561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134428832767818785664885707 201643249151728178497328561)
      ·
        refine ⟨151232436863796133872996421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201643249151728178497328561 151232436863796133872996421)
        ·
          refine ⟨28356081911961775101186829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151232436863796133872996421 28356081911961775101186829)
          ·
            refine ⟨10633530716985665662945061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28356081911961775101186829 10633530716985665662945061)
            ·
              refine ⟨1993787009434812311802199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10633530716985665662945061 1993787009434812311802199)
              ·
                refine ⟨2990680514152218467703299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993787009434812311802199 2990680514152218467703299)
                ·
                  refine ⟨4486020771228327701554949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2990680514152218467703299 4486020771228327701554949)
                  ·
                    refine ⟨841128894605311444041553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4486020771228327701554949 841128894605311444041553)
                    ·
                      rfl

theorem cell22_2457139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 1, 4].length) (baseStart_2457139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457139 prefixEnd_2457139 := by exact prefixLift 2457139
  have htrace : WordTrace (prefixWord ++ tailWord_2457139) baseStart_2457139 baseEnd_2457139 := by
    simpa [prefixWord, tailWord_2457139, baseEnd_2457139] using wordTrace_append hprefix tailTrace_2457139
  have hstable : (prefixWord ++ tailWord_2457139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457139).length < 2 ^ (prefixWord ++ tailWord_2457139).sum := by decide
  have hdescent : baseEnd_2457139 < baseStart_2457139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457220 : List Nat := [2, 3, 2, 1, 5, 1, 2, 1, 2, 3]
def baseStart_2457220 : Nat := 118140960795 + 2457220 * 2 ^ 59
def prefixEnd_2457220 : Nat := 4983230072969 + 3 ^ 40 * 2457220 * 2
def baseEnd_2457220 : Nat := 841156622560654232766305

theorem tailTrace_2457220 : CollatzResearch.WordTrace tailWord_2457220 prefixEnd_2457220 841156622560654232766305 := by
  unfold tailWord_2457220
  simp only [CollatzResearch.WordTrace]
  refine ⟨44811088078959537305144557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59748117438612716406859409 44811088078959537305144557)
  ·
    refine ⟨16804158029609826489429209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44811088078959537305144557 16804158029609826489429209)
    ·
      refine ⟨12603118522207369867071907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16804158029609826489429209 12603118522207369867071907)
      ·
        refine ⟨18904677783311054800607861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12603118522207369867071907 18904677783311054800607861)
        ·
          refine ⟨1772313542185411387556987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18904677783311054800607861 1772313542185411387556987)
          ·
            refine ⟨2658470313278117081335481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1772313542185411387556987 2658470313278117081335481)
            ·
              refine ⟨1993852734958587811001611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2658470313278117081335481 1993852734958587811001611)
              ·
                refine ⟨2990779102437881716502417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993852734958587811001611 2990779102437881716502417)
                ·
                  refine ⟨2243084326828411287376813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2990779102437881716502417 2243084326828411287376813)
                  ·
                    refine ⟨841156622560654232766305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2243084326828411287376813 841156622560654232766305)
                    ·
                      rfl

theorem cell22_2457220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_2457220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457220 prefixEnd_2457220 := by exact prefixLift 2457220
  have htrace : WordTrace (prefixWord ++ tailWord_2457220) baseStart_2457220 baseEnd_2457220 := by
    simpa [prefixWord, tailWord_2457220, baseEnd_2457220] using wordTrace_append hprefix tailTrace_2457220
  have hstable : (prefixWord ++ tailWord_2457220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457220).length < 2 ^ (prefixWord ++ tailWord_2457220).sum := by decide
  have hdescent : baseEnd_2457220 < baseStart_2457220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457227 : List Nat := [1, 1, 1, 1, 4, 1, 5, 3, 5]
def baseStart_2457227 : Nat := 118140960795 + 2457227 * 2 ^ 59
def prefixEnd_2457227 : Nat := 4983230072969 + 3 ^ 40 * 2457227 * 2
def baseEnd_2457227 : Nat := 280386339601236182613761

theorem tailTrace_2457227 : CollatzResearch.WordTrace tailWord_2457227 prefixEnd_2457227 280386339601236182613761 := by
  unfold tailWord_2457227
  simp only [CollatzResearch.WordTrace]
  refine ⟨89622431468893714805793935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59748287645929143203862623 89622431468893714805793935)
  ·
    refine ⟨134433647203340572208690903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89622431468893714805793935 134433647203340572208690903)
    ·
      refine ⟨201650470805010858313036355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134433647203340572208690903 201650470805010858313036355)
      ·
        refine ⟨302475706207516287469554533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201650470805010858313036355 302475706207516287469554533)
        ·
          refine ⟨56714194913909303900541475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 302475706207516287469554533 56714194913909303900541475)
          ·
            refine ⟨85071292370863955850812213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56714194913909303900541475 85071292370863955850812213)
            ·
              refine ⟨7975433659768495861013645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85071292370863955850812213 7975433659768495861013645)
              ·
                refine ⟨2990787622413185947880117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7975433659768495861013645 2990787622413185947880117)
                ·
                  refine ⟨280386339601236182613761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2990787622413185947880117 280386339601236182613761)
                  ·
                    rfl

theorem cell22_2457227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 5].length) (baseStart_2457227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457227 prefixEnd_2457227 := by exact prefixLift 2457227
  have htrace : WordTrace (prefixWord ++ tailWord_2457227) baseStart_2457227 baseEnd_2457227 := by
    simpa [prefixWord, tailWord_2457227, baseEnd_2457227] using wordTrace_append hprefix tailTrace_2457227
  have hstable : (prefixWord ++ tailWord_2457227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457227).length < 2 ^ (prefixWord ++ tailWord_2457227).sum := by decide
  have hdescent : baseEnd_2457227 < baseStart_2457227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457304 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 4, 3]
def baseStart_2457304 : Nat := 118140960795 + 2457304 * 2 ^ 59
def prefixEnd_2457304 : Nat := 4983230072969 + 3 ^ 40 * 2457304 * 2
def baseEnd_2457304 : Nat := 841185377477306013666047

theorem tailTrace_2457304 : CollatzResearch.WordTrace tailWord_2457304 prefixEnd_2457304 841185377477306013666047 := by
  unfold tailWord_2457304
  simp only [CollatzResearch.WordTrace]
  refine ⟨44812619944807378478173483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59750159926409837970897977 44812619944807378478173483)
  ·
    refine ⟨67218929917211067717260225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44812619944807378478173483 67218929917211067717260225)
    ·
      refine ⟨50414197437908300787945169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67218929917211067717260225 50414197437908300787945169)
      ·
        refine ⟨37810648078431225590958877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50414197437908300787945169 37810648078431225590958877)
        ·
          refine ⟨14178993029411709596609579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37810648078431225590958877 14178993029411709596609579)
          ·
            refine ⟨21268489544117564394914369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14178993029411709596609579 21268489544117564394914369)
            ·
              refine ⟨15951367158088173296185777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21268489544117564394914369 15951367158088173296185777)
              ·
                refine ⟨11963525368566129972139333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15951367158088173296185777 11963525368566129972139333)
                ·
                  refine ⟨2243161006606149369776125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11963525368566129972139333 2243161006606149369776125)
                  ·
                    refine ⟨841185377477306013666047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2243161006606149369776125 841185377477306013666047)
                    ·
                      rfl

theorem cell22_2457304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_2457304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457304 prefixEnd_2457304 := by exact prefixLift 2457304
  have htrace : WordTrace (prefixWord ++ tailWord_2457304) baseStart_2457304 baseEnd_2457304 := by
    simpa [prefixWord, tailWord_2457304, baseEnd_2457304] using wordTrace_append hprefix tailTrace_2457304
  have hstable : (prefixWord ++ tailWord_2457304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457304).length < 2 ^ (prefixWord ++ tailWord_2457304).sum := by decide
  have hdescent : baseEnd_2457304 < baseStart_2457304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457306 : List Nat := [3, 1, 1, 2, 2, 4, 2, 3, 4]
def baseStart_2457306 : Nat := 118140960795 + 2457306 * 2 ^ 59
def prefixEnd_2457306 : Nat := 4983230072969 + 3 ^ 40 * 2457306 * 2
def baseEnd_2457306 : Nat := 280395354039392891705347

theorem tailTrace_2457306 : CollatzResearch.WordTrace tailWord_2457306 prefixEnd_2457306 280395354039392891705347 := by
  unfold tailWord_2457306
  simp only [CollatzResearch.WordTrace]
  refine ⟨22406328208901877824479943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59750208557071674198613181 22406328208901877824479943)
  ·
    refine ⟨33609492313352816736719915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22406328208901877824479943 33609492313352816736719915)
    ·
      refine ⟨50414238470029225105079873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33609492313352816736719915 50414238470029225105079873)
      ·
        refine ⟨37810678852521918828809905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50414238470029225105079873 37810678852521918828809905)
        ·
          refine ⟨28358009139391439121607429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37810678852521918828809905 28358009139391439121607429)
          ·
            refine ⟨5317126713635894835301393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28358009139391439121607429 5317126713635894835301393)
            ·
              refine ⟨3987845035226921126476045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5317126713635894835301393 3987845035226921126476045)
              ·
                refine ⟨1495441888210095422428517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3987845035226921126476045 1495441888210095422428517)
                ·
                  refine ⟨280395354039392891705347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1495441888210095422428517 280395354039392891705347)
                  ·
                    rfl

theorem cell22_2457306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_2457306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457306 prefixEnd_2457306 := by exact prefixLift 2457306
  have htrace : WordTrace (prefixWord ++ tailWord_2457306) baseStart_2457306 baseEnd_2457306 := by
    simpa [prefixWord, tailWord_2457306, baseEnd_2457306] using wordTrace_append hprefix tailTrace_2457306
  have hstable : (prefixWord ++ tailWord_2457306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457306).length < 2 ^ (prefixWord ++ tailWord_2457306).sum := by decide
  have hdescent : baseEnd_2457306 < baseStart_2457306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457308 : List Nat := [2, 2, 5, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2457308 : Nat := 118140960795 + 2457308 * 2 ^ 59
def prefixEnd_2457308 : Nat := 4983230072969 + 3 ^ 40 * 2457308 * 2
def baseEnd_2457308 : Nat := 841186746759051336566035

theorem tailTrace_2457308 : CollatzResearch.WordTrace tailWord_2457308 prefixEnd_2457308 841186746759051336566035 := by
  unfold tailWord_2457308
  simp only [CollatzResearch.WordTrace]
  refine ⟨44812692890800132819746289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59750257187733510426328385 44812692890800132819746289)
  ·
    refine ⟨33609519668100099614809717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44812692890800132819746289 33609519668100099614809717)
    ·
      refine ⟨3150892468884384338888411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33609519668100099614809717 3150892468884384338888411)
      ·
        refine ⟨4726338703326576508332617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3150892468884384338888411 4726338703326576508332617)
        ·
          refine ⟨3544754027494932381249463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4726338703326576508332617 3544754027494932381249463)
          ·
            refine ⟨5317131041242398571874195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544754027494932381249463 5317131041242398571874195)
            ·
              refine ⟨7975696561863597857811293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5317131041242398571874195 7975696561863597857811293)
              ·
                refine ⟨2990886210698849196679235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7975696561863597857811293 2990886210698849196679235)
                ·
                  refine ⟨4486329316048273795018853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2990886210698849196679235 4486329316048273795018853)
                  ·
                    refine ⟨841186746759051336566035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4486329316048273795018853 841186746759051336566035)
                    ·
                      rfl

theorem cell22_2457308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2457308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457308 prefixEnd_2457308 := by exact prefixLift 2457308
  have htrace : WordTrace (prefixWord ++ tailWord_2457308) baseStart_2457308 baseEnd_2457308 := by
    simpa [prefixWord, tailWord_2457308, baseEnd_2457308] using wordTrace_append hprefix tailTrace_2457308
  have hstable : (prefixWord ++ tailWord_2457308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457308).length < 2 ^ (prefixWord ++ tailWord_2457308).sum := by decide
  have hdescent : baseEnd_2457308 < baseStart_2457308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457317 : List Nat := [1, 3, 1, 4, 1, 1, 11]
def baseStart_2457317 : Nat := 118140960795 + 2457317 * 2 ^ 59
def prefixEnd_2457317 : Nat := 4983230072969 + 3 ^ 40 * 2457317 * 2
def baseEnd_2457317 : Nat := 31155178801591789373741

theorem tailTrace_2457317 : CollatzResearch.WordTrace tailWord_2457317 prefixEnd_2457317 31155178801591789373741 := by
  unfold tailWord_2457317
  simp only [CollatzResearch.WordTrace]
  refine ⟨89625714038567660176570205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59750476025711773451046803 89625714038567660176570205)
  ·
    refine ⟨33609642764462872566213827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89625714038567660176570205 33609642764462872566213827)
    ·
      refine ⟨50414464146694308849320741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33609642764462872566213827 50414464146694308849320741)
      ·
        refine ⟨9452712027505182909247639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50414464146694308849320741 9452712027505182909247639)
        ·
          refine ⟨14179068041257774363871459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9452712027505182909247639 14179068041257774363871459)
          ·
            refine ⟨21268602061886661545807189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14179068041257774363871459 21268602061886661545807189)
            ·
              refine ⟨31155178801591789373741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21268602061886661545807189 31155178801591789373741)
              ·
                rfl

theorem cell22_2457317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 11].length) (baseStart_2457317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457317 prefixEnd_2457317 := by exact prefixLift 2457317
  have htrace : WordTrace (prefixWord ++ tailWord_2457317) baseStart_2457317 baseEnd_2457317 := by
    simpa [prefixWord, tailWord_2457317, baseEnd_2457317] using wordTrace_append hprefix tailTrace_2457317
  have hstable : (prefixWord ++ tailWord_2457317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457317).length < 2 ^ (prefixWord ++ tailWord_2457317).sum := by decide
  have hdescent : baseEnd_2457317 < baseStart_2457317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457347 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 2, 6]
def baseStart_2457347 : Nat := 118140960795 + 2457347 * 2 ^ 59
def prefixEnd_2457347 : Nat := 4983230072969 + 3 ^ 40 * 2457347 * 2
def baseEnd_2457347 : Nat := 841200097256068234840915

theorem tailTrace_2457347 : CollatzResearch.WordTrace tailWord_2457347 prefixEnd_2457347 841200097256068234840915 := by
  unfold tailWord_2457347
  simp only [CollatzResearch.WordTrace]
  refine ⟨89626808228458975300162295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59751205485639316866774863 89626808228458975300162295)
  ·
    refine ⟨134440212342688462950243443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89626808228458975300162295 134440212342688462950243443)
    ·
      refine ⟨201660318514032694425365165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134440212342688462950243443 201660318514032694425365165)
      ·
        refine ⟨75622619442762260409511937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201660318514032694425365165 75622619442762260409511937)
        ·
          refine ⟨56716964582071695307133953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75622619442762260409511937 56716964582071695307133953)
          ·
            refine ⟨42537723436553771480350465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56716964582071695307133953 42537723436553771480350465)
            ·
              refine ⟨31903292577415328610262849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42537723436553771480350465 31903292577415328610262849)
              ·
                refine ⟨23927469433061496457697137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31903292577415328610262849 23927469433061496457697137)
                ·
                  refine ⟨17945602074796122343272853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23927469433061496457697137 17945602074796122343272853)
                  ·
                    refine ⟨841200097256068234840915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17945602074796122343272853 841200097256068234840915)
                    ·
                      rfl

theorem cell22_2457347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 6].length) (baseStart_2457347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457347 prefixEnd_2457347 := by exact prefixLift 2457347
  have htrace : WordTrace (prefixWord ++ tailWord_2457347) baseStart_2457347 baseEnd_2457347 := by
    simpa [prefixWord, tailWord_2457347, baseEnd_2457347] using wordTrace_append hprefix tailTrace_2457347
  have hstable : (prefixWord ++ tailWord_2457347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457347).length < 2 ^ (prefixWord ++ tailWord_2457347).sum := by decide
  have hdescent : baseEnd_2457347 < baseStart_2457347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457392 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 1, 10]
def baseStart_2457392 : Nat := 118140960795 + 2457392 * 2 ^ 59
def prefixEnd_2457392 : Nat := 4983230072969 + 3 ^ 40 * 2457392 * 2
def baseEnd_2457392 : Nat := 841215501675703117465777

theorem tailTrace_2457392 : CollatzResearch.WordTrace tailWord_2457392 prefixEnd_2457392 841215501675703117465777 := by
  unfold tailWord_2457392
  simp only [CollatzResearch.WordTrace]
  refine ⟨44814224756647973992775215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59752299675530631990366953 44814224756647973992775215)
  ·
    refine ⟨67221337134971960989162823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44814224756647973992775215 67221337134971960989162823)
    ·
      refine ⟨100832005702457941483744235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67221337134971960989162823 100832005702457941483744235)
      ·
        refine ⟨151248008553686912225616353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100832005702457941483744235 151248008553686912225616353)
        ·
          refine ⟨113436006415265184169212265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151248008553686912225616353 113436006415265184169212265)
          ·
            refine ⟨85077004811448888126909199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113436006415265184169212265 85077004811448888126909199)
            ·
              refine ⟨127615507217173332190363799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85077004811448888126909199 127615507217173332190363799)
              ·
                refine ⟨191423260825759998285545699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127615507217173332190363799 191423260825759998285545699)
                ·
                  refine ⟨287134891238639997428318549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191423260825759998285545699 287134891238639997428318549)
                  ·
                    refine ⟨841215501675703117465777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 287134891238639997428318549 841215501675703117465777)
                    ·
                      rfl

theorem cell22_2457392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_2457392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457392 prefixEnd_2457392 := by exact prefixLift 2457392
  have htrace : WordTrace (prefixWord ++ tailWord_2457392) baseStart_2457392 baseEnd_2457392 := by
    simpa [prefixWord, tailWord_2457392, baseEnd_2457392] using wordTrace_append hprefix tailTrace_2457392
  have hstable : (prefixWord ++ tailWord_2457392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457392).length < 2 ^ (prefixWord ++ tailWord_2457392).sum := by decide
  have hdescent : baseEnd_2457392 < baseStart_2457392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457441 : List Nat := [1, 2, 3, 1, 1, 1, 5, 4, 4]
def baseStart_2457441 : Nat := 118140960795 + 2457441 * 2 ^ 59
def prefixEnd_2457441 : Nat := 4983230072969 + 3 ^ 40 * 2457441 * 2
def baseEnd_2457441 : Nat := 280410758459027774330209

theorem tailTrace_2457441 : CollatzResearch.WordTrace tailWord_2457441 prefixEnd_2457441 280410758459027774330209 := by
  unfold tailWord_2457441
  simp only [CollatzResearch.WordTrace]
  refine ⟨89630236690118429354084177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59753491126745619569389451 89630236690118429354084177)
  ·
    refine ⟨67222677517588822015563133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89630236690118429354084177 67222677517588822015563133)
    ·
      refine ⟨25208504069095808255836175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67222677517588822015563133 25208504069095808255836175)
      ·
        refine ⟨37812756103643712383754263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25208504069095808255836175 37812756103643712383754263)
        ·
          refine ⟨56719134155465568575631395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37812756103643712383754263 56719134155465568575631395)
          ·
            refine ⟨85078701233198352863447093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56719134155465568575631395 85078701233198352863447093)
            ·
              refine ⟨7976128240612345580948165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85078701233198352863447093 7976128240612345580948165)
              ·
                refine ⟨1495524045114814796427781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7976128240612345580948165 1495524045114814796427781)
                ·
                  refine ⟨280410758459027774330209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1495524045114814796427781 280410758459027774330209)
                  ·
                    rfl

theorem cell22_2457441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 4].length) (baseStart_2457441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457441 prefixEnd_2457441 := by exact prefixLift 2457441
  have htrace : WordTrace (prefixWord ++ tailWord_2457441) baseStart_2457441 baseEnd_2457441 := by
    simpa [prefixWord, tailWord_2457441, baseEnd_2457441] using wordTrace_append hprefix tailTrace_2457441
  have hstable : (prefixWord ++ tailWord_2457441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457441).length < 2 ^ (prefixWord ++ tailWord_2457441).sum := by decide
  have hdescent : baseEnd_2457441 < baseStart_2457441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457490 : List Nat := [3, 2, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_2457490 : Nat := 118140960795 + 2457490 * 2 ^ 59
def prefixEnd_2457490 : Nat := 4983230072969 + 3 ^ 40 * 2457490 * 2
def baseEnd_2457490 : Nat := 841249049078463528515477

theorem tailTrace_2457490 : CollatzResearch.WordTrace tailWord_2457490 prefixEnd_2457490 841249049078463528515477 := by
  unfold tailWord_2457490
  simp only [CollatzResearch.WordTrace]
  refine ⟨22408005966735227680654481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59754682577960607148411949 22408005966735227680654481)
  ·
    refine ⟨16806004475051420760490861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22408005966735227680654481 16806004475051420760490861)
    ·
      refine ⟨6302251678144282785184073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16806004475051420760490861 6302251678144282785184073)
      ·
        refine ⟨4726688758608212088888055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6302251678144282785184073 4726688758608212088888055)
        ·
          refine ⟨7090033137912318133332083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4726688758608212088888055 7090033137912318133332083)
          ·
            refine ⟨10635049706868477199998125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7090033137912318133332083 10635049706868477199998125)
            ·
              refine ⟨3988143640075678949999297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10635049706868477199998125 3988143640075678949999297)
              ·
                refine ⟨2991107730056759212499473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3988143640075678949999297 2991107730056759212499473)
                ·
                  refine ⟨2243330797542569409374605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2991107730056759212499473 2243330797542569409374605)
                  ·
                    refine ⟨841249049078463528515477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2243330797542569409374605 841249049078463528515477)
                    ·
                      rfl

theorem cell22_2457490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_2457490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457490 prefixEnd_2457490 := by exact prefixLift 2457490
  have htrace : WordTrace (prefixWord ++ tailWord_2457490) baseStart_2457490 baseEnd_2457490 := by
    simpa [prefixWord, tailWord_2457490, baseEnd_2457490] using wordTrace_append hprefix tailTrace_2457490
  have hstable : (prefixWord ++ tailWord_2457490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457490).length < 2 ^ (prefixWord ++ tailWord_2457490).sum := by decide
  have hdescent : baseEnd_2457490 < baseStart_2457490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457610 : List Nat := [3, 1, 2, 2, 4, 1, 1, 4, 4]
def baseStart_2457610 : Nat := 118140960795 + 2457610 * 2 ^ 59
def prefixEnd_2457610 : Nat := 4983230072969 + 3 ^ 40 * 2457610 * 2
def baseEnd_2457610 : Nat := 280430042510274405171703

theorem tailTrace_2457610 : CollatzResearch.WordTrace tailWord_2457610 prefixEnd_2457610 280430042510274405171703 := by
  unfold tailWord_2457610
  simp only [CollatzResearch.WordTrace]
  refine ⟨22409100156626542804246571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59757600417670780811324189 22409100156626542804246571)
  ·
    refine ⟨33613650234939814206369857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22409100156626542804246571 33613650234939814206369857)
    ·
      refine ⟨25210237676204860654777393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33613650234939814206369857 25210237676204860654777393)
      ·
        refine ⟨18907678257153645491083045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25210237676204860654777393 18907678257153645491083045)
        ·
          refine ⟨3545189673216308529578071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18907678257153645491083045 3545189673216308529578071)
          ·
            refine ⟨5317784509824462794367107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545189673216308529578071 5317784509824462794367107)
            ·
              refine ⟨7976676764736694191550661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5317784509824462794367107 7976676764736694191550661)
              ·
                refine ⟨1495626893388130160915749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7976676764736694191550661 1495626893388130160915749)
                ·
                  refine ⟨280430042510274405171703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1495626893388130160915749 280430042510274405171703)
                  ·
                    rfl

theorem cell22_2457610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_2457610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457610 prefixEnd_2457610 := by exact prefixLift 2457610
  have htrace : WordTrace (prefixWord ++ tailWord_2457610) baseStart_2457610 baseEnd_2457610 := by
    simpa [prefixWord, tailWord_2457610, baseEnd_2457610] using wordTrace_append hprefix tailTrace_2457610
  have hstable : (prefixWord ++ tailWord_2457610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457610).length < 2 ^ (prefixWord ++ tailWord_2457610).sum := by decide
  have hdescent : baseEnd_2457610 < baseStart_2457610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457640 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 1, 6]
def baseStart_2457640 : Nat := 118140960795 + 2457640 * 2 ^ 59
def prefixEnd_2457640 : Nat := 4983230072969 + 3 ^ 40 * 2457640 * 2
def baseEnd_2457640 : Nat := 841300397143913137265017

theorem tailTrace_2457640 : CollatzResearch.WordTrace tailWord_2457640 prefixEnd_2457640 841300397143913137265017 := by
  unfold tailWord_2457640
  simp only [CollatzResearch.WordTrace]
  refine ⟨44818747408198743170289187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59758329877598324227052249 44818747408198743170289187)
  ·
    refine ⟨67228121112298114755433781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44818747408198743170289187 67228121112298114755433781)
    ·
      refine ⟨6302636354277948258321917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67228121112298114755433781 6302636354277948258321917)
      ·
        refine ⟨2363488632854230596870719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6302636354277948258321917 2363488632854230596870719)
        ·
          refine ⟨3545232949281345895306079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363488632854230596870719 3545232949281345895306079)
          ·
            refine ⟨5317849423922018842959119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545232949281345895306079 5317849423922018842959119)
            ·
              refine ⟨7976774135883028264438679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5317849423922018842959119 7976774135883028264438679)
              ·
                refine ⟨11965161203824542396658019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7976774135883028264438679 11965161203824542396658019)
                ·
                  refine ⟨17947741805736813594987029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11965161203824542396658019 17947741805736813594987029)
                  ·
                    refine ⟨841300397143913137265017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17947741805736813594987029 841300397143913137265017)
                    ·
                      rfl

theorem cell22_2457640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_2457640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457640 prefixEnd_2457640 := by exact prefixLift 2457640
  have htrace : WordTrace (prefixWord ++ tailWord_2457640) baseStart_2457640 baseEnd_2457640 := by
    simpa [prefixWord, tailWord_2457640, baseEnd_2457640] using wordTrace_append hprefix tailTrace_2457640
  have hstable : (prefixWord ++ tailWord_2457640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457640).length < 2 ^ (prefixWord ++ tailWord_2457640).sum := by decide
  have hdescent : baseEnd_2457640 < baseStart_2457640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457713 : List Nat := [1, 2, 2, 2, 1, 1, 3, 5, 1, 4]
def baseStart_2457713 : Nat := 118140960795 + 2457713 * 2 ^ 59
def prefixEnd_2457713 : Nat := 4983230072969 + 3 ^ 40 * 2457713 * 2
def baseEnd_2457713 : Nat := 841325386535765280189793

theorem tailTrace_2457713 : CollatzResearch.WordTrace tailWord_2457713 prefixEnd_2457713 841325386535765280189793 := by
  unfold tailWord_2457713
  simp only [CollatzResearch.WordTrace]
  refine ⟨89640157345133019807985793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59760104896755346538657195 89640157345133019807985793)
  ·
    refine ⟨67230118008849764855989345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89640157345133019807985793 67230118008849764855989345)
    ·
      refine ⟨50422588506637323641992009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67230118008849764855989345 50422588506637323641992009)
      ·
        refine ⟨37816941379977992731494007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50422588506637323641992009 37816941379977992731494007)
        ·
          refine ⟨56725412069966989097241011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37816941379977992731494007 56725412069966989097241011)
          ·
            refine ⟨85088118104950483645861517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56725412069966989097241011 85088118104950483645861517)
            ·
              refine ⟨31908044289356431367198069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85088118104950483645861517 31908044289356431367198069)
              ·
                refine ⟨2991379152127165440674819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31908044289356431367198069 2991379152127165440674819)
                ·
                  refine ⟨4487068728190748161012229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2991379152127165440674819 4487068728190748161012229)
                  ·
                    refine ⟨841325386535765280189793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4487068728190748161012229 841325386535765280189793)
                    ·
                      rfl

theorem cell22_2457713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_2457713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457713 prefixEnd_2457713 := by exact prefixLift 2457713
  have htrace : WordTrace (prefixWord ++ tailWord_2457713) baseStart_2457713 baseEnd_2457713 := by
    simpa [prefixWord, tailWord_2457713, baseEnd_2457713] using wordTrace_append hprefix tailTrace_2457713
  have hstable : (prefixWord ++ tailWord_2457713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457713).length < 2 ^ (prefixWord ++ tailWord_2457713).sum := by decide
  have hdescent : baseEnd_2457713 < baseStart_2457713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457771 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 6, 7]
def baseStart_2457771 : Nat := 118140960795 + 2457771 * 2 ^ 59
def prefixEnd_2457771 : Nat := 4983230072969 + 3 ^ 40 * 2457771 * 2
def baseEnd_2457771 : Nat := 841345241121072462239615

theorem tailTrace_2457771 : CollatzResearch.WordTrace tailWord_2457771 prefixEnd_2457771 841345241121072462239615 := by
  unfold tailWord_2457771
  simp only [CollatzResearch.WordTrace]
  refine ⟨89642272778922895713597167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59761515185948597142398111 89642272778922895713597167)
  ·
    refine ⟨134463409168384343570395751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89642272778922895713597167 134463409168384343570395751)
    ·
      refine ⟨201695113752576515355593627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134463409168384343570395751 201695113752576515355593627)
      ·
        refine ⟨302542670628864773033390441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201695113752576515355593627 302542670628864773033390441)
        ·
          refine ⟨226907002971648579775042831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302542670628864773033390441 226907002971648579775042831)
          ·
            refine ⟨340360504457472869662564247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226907002971648579775042831 340360504457472869662564247)
            ·
              refine ⟨510540756686209304493846371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340360504457472869662564247 510540756686209304493846371)
              ·
                refine ⟨765811135029313956740769557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510540756686209304493846371 765811135029313956740769557)
                ·
                  refine ⟨35897396954499091722223573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 765811135029313956740769557 35897396954499091722223573)
                  ·
                    refine ⟨841345241121072462239615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35897396954499091722223573 841345241121072462239615)
                    ·
                      rfl

theorem cell22_2457771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_2457771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457771 prefixEnd_2457771 := by exact prefixLift 2457771
  have htrace : WordTrace (prefixWord ++ tailWord_2457771) baseStart_2457771 baseEnd_2457771 := by
    simpa [prefixWord, tailWord_2457771, baseEnd_2457771] using wordTrace_append hprefix tailTrace_2457771
  have hstable : (prefixWord ++ tailWord_2457771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457771).length < 2 ^ (prefixWord ++ tailWord_2457771).sum := by decide
  have hdescent : baseEnd_2457771 < baseStart_2457771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457773 : List Nat := [1, 5, 2, 1, 2, 11]
def baseStart_2457773 : Nat := 118140960795 + 2457773 * 2 ^ 59
def prefixEnd_2457773 : Nat := 4983230072969 + 3 ^ 40 * 2457773 * 2
def baseEnd_2457773 : Nat := 10386986737801791650489

theorem tailTrace_2457773 : CollatzResearch.WordTrace tailWord_2457773 prefixEnd_2457773 10386986737801791650489 := by
  unfold tailWord_2457773
  simp only [CollatzResearch.WordTrace]
  refine ⟨89642345724915650055169973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59761563816610433370113315 89642345724915650055169973)
  ·
    refine ⟨8403969911710842192672185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89642345724915650055169973 8403969911710842192672185)
    ·
      refine ⟨6302977433783131644504139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8403969911710842192672185 6302977433783131644504139)
      ·
        refine ⟨9454466150674697466756209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6302977433783131644504139 9454466150674697466756209)
        ·
          refine ⟨7090849613006023100067157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9454466150674697466756209 7090849613006023100067157)
          ·
            refine ⟨10386986737801791650489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7090849613006023100067157 10386986737801791650489)
            ·
              rfl

theorem cell22_2457773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 11].length) (baseStart_2457773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457773 prefixEnd_2457773 := by exact prefixLift 2457773
  have htrace : WordTrace (prefixWord ++ tailWord_2457773) baseStart_2457773 baseEnd_2457773 := by
    simpa [prefixWord, tailWord_2457773, baseEnd_2457773] using wordTrace_append hprefix tailTrace_2457773
  have hstable : (prefixWord ++ tailWord_2457773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457773).length < 2 ^ (prefixWord ++ tailWord_2457773).sum := by decide
  have hdescent : baseEnd_2457773 < baseStart_2457773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457794 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2457794 : Nat := 118140960795 + 2457794 * 2 ^ 59
def prefixEnd_2457794 : Nat := 4983230072969 + 3 ^ 40 * 2457794 * 2
def baseEnd_2457794 : Nat := 841353114491108068914545

theorem tailTrace_2457794 : CollatzResearch.WordTrace tailWord_2457794 prefixEnd_2457794 841353114491108068914545 := by
  unfold tailWord_2457794
  simp only [CollatzResearch.WordTrace]
  refine ⟨22410777914459892660421109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59762074438559713761122957 22410777914459892660421109)
  ·
    refine ⟨2101010429480614936914479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22410777914459892660421109 2101010429480614936914479)
    ·
      refine ⟨3151515644220922405371719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2101010429480614936914479 3151515644220922405371719)
      ·
        refine ⟨4727273466331383608057579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3151515644220922405371719 4727273466331383608057579)
        ·
          refine ⟨7090910199497075412086369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4727273466331383608057579 7090910199497075412086369)
          ·
            refine ⟨5318182649622806559064777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7090910199497075412086369 5318182649622806559064777)
            ·
              refine ⟨3988636987217104919298583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5318182649622806559064777 3988636987217104919298583)
              ·
                refine ⟨5982955480825657378947875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3988636987217104919298583 5982955480825657378947875)
                ·
                  refine ⟨8974433221238486068421813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5982955480825657378947875 8974433221238486068421813)
                  ·
                    refine ⟨841353114491108068914545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8974433221238486068421813 841353114491108068914545)
                    ·
                      rfl

theorem cell22_2457794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2457794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457794 prefixEnd_2457794 := by exact prefixLift 2457794
  have htrace : WordTrace (prefixWord ++ tailWord_2457794) baseStart_2457794 baseEnd_2457794 := by
    simpa [prefixWord, tailWord_2457794, baseEnd_2457794] using wordTrace_append hprefix tailTrace_2457794
  have hstable : (prefixWord ++ tailWord_2457794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457794).length < 2 ^ (prefixWord ++ tailWord_2457794).sum := by decide
  have hdescent : baseEnd_2457794 < baseStart_2457794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457848 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 5, 4]
def baseStart_2457848 : Nat := 118140960795 + 2457848 * 2 ^ 59
def prefixEnd_2457848 : Nat := 4983230072969 + 3 ^ 40 * 2457848 * 2
def baseEnd_2457848 : Nat := 841371599794669928064379

theorem tailTrace_2457848 : CollatzResearch.WordTrace tailWord_2457848 prefixEnd_2457848 841371599794669928064379 := by
  unfold tailWord_2457848
  simp only [CollatzResearch.WordTrace]
  refine ⟨44822540599821968932075099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59763387466429291909433465 44822540599821968932075099)
  ·
    refine ⟨67233810899732953398112649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44822540599821968932075099 67233810899732953398112649)
    ·
      refine ⟨50425358174799715048584487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67233810899732953398112649 50425358174799715048584487)
      ·
        refine ⟨75638037262199572572876731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50425358174799715048584487 75638037262199572572876731)
        ·
          refine ⟨113457055893299358859315097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75638037262199572572876731 113457055893299358859315097)
          ·
            refine ⟨85092791919974519144486323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113457055893299358859315097 85092791919974519144486323)
            ·
              refine ⟨127639187879961778716729485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85092791919974519144486323 127639187879961778716729485)
              ·
                refine ⟨47864695454985667018773557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127639187879961778716729485 47864695454985667018773557)
                ·
                  refine ⟨4487315198904906283010021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47864695454985667018773557 4487315198904906283010021)
                  ·
                    refine ⟨841371599794669928064379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4487315198904906283010021 841371599794669928064379)
                    ·
                      rfl

theorem cell22_2457848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_2457848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457848 prefixEnd_2457848 := by exact prefixLift 2457848
  have htrace : WordTrace (prefixWord ++ tailWord_2457848) baseStart_2457848 baseEnd_2457848 := by
    simpa [prefixWord, tailWord_2457848, baseEnd_2457848] using wordTrace_append hprefix tailTrace_2457848
  have hstable : (prefixWord ++ tailWord_2457848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457848).length < 2 ^ (prefixWord ++ tailWord_2457848).sum := by decide
  have hdescent : baseEnd_2457848 < baseStart_2457848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457852 : List Nat := [2, 2, 2, 1, 4, 2, 3, 1, 5]
def baseStart_2457852 : Nat := 118140960795 + 2457852 * 2 ^ 59
def prefixEnd_2457852 : Nat := 4983230072969 + 3 ^ 40 * 2457852 * 2
def baseEnd_2457852 : Nat := 280457656358805083654789

theorem tailTrace_2457852 : CollatzResearch.WordTrace tailWord_2457852 prefixEnd_2457852 280457656358805083654789 := by
  unfold tailWord_2457852
  simp only [CollatzResearch.WordTrace]
  refine ⟨44822613545814723273647905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59763484727752964364863873 44822613545814723273647905)
  ·
    refine ⟨33616960159361042455235929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44822613545814723273647905 33616960159361042455235929)
    ·
      refine ⟨25212720119520781841426947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33616960159361042455235929 25212720119520781841426947)
      ·
        refine ⟨37819080179281172762140421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25212720119520781841426947 37819080179281172762140421)
        ·
          refine ⟨7091077533615219892901329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37819080179281172762140421 7091077533615219892901329)
          ·
            refine ⟨5318308150211414919675997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7091077533615219892901329 5318308150211414919675997)
            ·
              refine ⟨1994365556329280594878499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5318308150211414919675997 1994365556329280594878499)
              ·
                refine ⟨2991548334493920892317749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1994365556329280594878499 2991548334493920892317749)
                ·
                  refine ⟨280457656358805083654789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2991548334493920892317749 280457656358805083654789)
                  ·
                    rfl

theorem cell22_2457852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_2457852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457852 prefixEnd_2457852 := by exact prefixLift 2457852
  have htrace : WordTrace (prefixWord ++ tailWord_2457852) baseStart_2457852 baseEnd_2457852 := by
    simpa [prefixWord, tailWord_2457852, baseEnd_2457852] using wordTrace_append hprefix tailTrace_2457852
  have hstable : (prefixWord ++ tailWord_2457852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457852).length < 2 ^ (prefixWord ++ tailWord_2457852).sum := by decide
  have hdescent : baseEnd_2457852 < baseStart_2457852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457865 : List Nat := [1, 2, 1, 1, 3, 4, 1, 4, 1, 4]
def baseStart_2457865 : Nat := 118140960795 + 2457865 * 2 ^ 59
def prefixEnd_2457865 : Nat := 4983230072969 + 3 ^ 40 * 2457865 * 2
def baseEnd_2457865 : Nat := 841377419242087550389327

theorem tailTrace_2457865 : CollatzResearch.WordTrace tailWord_2457865 prefixEnd_2457865 841377419242087550389327 := by
  unfold tailWord_2457865
  simp only [CollatzResearch.WordTrace]
  refine ⟨89645701240582349767519049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59763800827054899845012699 89645701240582349767519049)
  ·
    refine ⟨67234275930436762325639287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89645701240582349767519049 67234275930436762325639287)
    ·
      refine ⟨100851413895655143488458931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67234275930436762325639287 100851413895655143488458931)
      ·
        refine ⟨151277120843482715232688397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100851413895655143488458931 151277120843482715232688397)
        ·
          refine ⟨56728920316306018212258149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151277120843482715232688397 56728920316306018212258149)
          ·
            refine ⟨10636672559307378414798403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56728920316306018212258149 10636672559307378414798403)
            ·
              refine ⟨15955008838961067622197605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10636672559307378414798403 15955008838961067622197605)
              ·
                refine ⟨2991564157305200179162051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15955008838961067622197605 2991564157305200179162051)
                ·
                  refine ⟨4487346235957800268743077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2991564157305200179162051 4487346235957800268743077)
                  ·
                    refine ⟨841377419242087550389327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4487346235957800268743077 841377419242087550389327)
                    ·
                      rfl

theorem cell22_2457865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_2457865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457865 prefixEnd_2457865 := by exact prefixLift 2457865
  have htrace : WordTrace (prefixWord ++ tailWord_2457865) baseStart_2457865 baseEnd_2457865 := by
    simpa [prefixWord, tailWord_2457865, baseEnd_2457865] using wordTrace_append hprefix tailTrace_2457865
  have hstable : (prefixWord ++ tailWord_2457865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457865).length < 2 ^ (prefixWord ++ tailWord_2457865).sum := by decide
  have hdescent : baseEnd_2457865 < baseStart_2457865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457923 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 2, 7]
def baseStart_2457923 : Nat := 118140960795 + 2457923 * 2 ^ 59
def prefixEnd_2457923 : Nat := 4983230072969 + 3 ^ 40 * 2457923 * 2
def baseEnd_2457923 : Nat := 841397273827394732439149

theorem tailTrace_2457923 : CollatzResearch.WordTrace tailWord_2457923 prefixEnd_2457923 841397273827394732439149 := by
  unfold tailWord_2457923
  simp only [CollatzResearch.WordTrace]
  refine ⟨89647816674372225673130423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59765211116248150448753615 89647816674372225673130423)
  ·
    refine ⟨134471725011558338509695635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89647816674372225673130423 134471725011558338509695635)
    ·
      refine ⟨201707587517337507764543453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134471725011558338509695635 201707587517337507764543453)
      ·
        refine ⟨75640345319001565411703795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201707587517337507764543453 75640345319001565411703795)
        ·
          refine ⟨113460517978502348117555693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75640345319001565411703795 113460517978502348117555693)
          ·
            refine ⟨42547694241938380544083385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113460517978502348117555693 42547694241938380544083385)
            ·
              refine ⟨31910770681453785408062539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42547694241938380544083385 31910770681453785408062539)
              ·
                refine ⟨47866156022180678112093809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31910770681453785408062539 47866156022180678112093809)
                ·
                  refine ⟨35899617016635508584070357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47866156022180678112093809 35899617016635508584070357)
                  ·
                    refine ⟨841397273827394732439149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35899617016635508584070357 841397273827394732439149)
                    ·
                      rfl

theorem cell22_2457923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_2457923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457923 prefixEnd_2457923 := by exact prefixLift 2457923
  have htrace : WordTrace (prefixWord ++ tailWord_2457923) baseStart_2457923 baseEnd_2457923 := by
    simpa [prefixWord, tailWord_2457923, baseEnd_2457923] using wordTrace_append hprefix tailTrace_2457923
  have hstable : (prefixWord ++ tailWord_2457923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457923).length < 2 ^ (prefixWord ++ tailWord_2457923).sum := by decide
  have hdescent : baseEnd_2457923 < baseStart_2457923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457942 : List Nat := [5, 2, 3, 12]
def baseStart_2457942 : Nat := 118140960795 + 2457942 * 2 ^ 59
def prefixEnd_2457942 : Nat := 4983230072969 + 3 ^ 40 * 2457942 * 2
def baseEnd_2457942 : Nat := 1154188995769115248579

theorem tailTrace_2457942 : CollatzResearch.WordTrace tailWord_2457942 prefixEnd_2457942 1154188995769115248579 := by
  unfold tailWord_2457942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5603031853831461994879505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59765673107535594612048053 5603031853831461994879505)
  ·
    refine ⟨4202273890373596496159629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5603031853831461994879505 4202273890373596496159629)
    ·
      refine ⟨1575852708890098686059861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4202273890373596496159629 1575852708890098686059861)
      ·
        refine ⟨1154188995769115248579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1575852708890098686059861 1154188995769115248579)
        ·
          rfl

theorem cell22_2457942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 12].length) (baseStart_2457942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457942 prefixEnd_2457942 := by exact prefixLift 2457942
  have htrace : WordTrace (prefixWord ++ tailWord_2457942) baseStart_2457942 baseEnd_2457942 := by
    simpa [prefixWord, tailWord_2457942, baseEnd_2457942] using wordTrace_append hprefix tailTrace_2457942
  have hstable : (prefixWord ++ tailWord_2457942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457942).length < 2 ^ (prefixWord ++ tailWord_2457942).sum := by decide
  have hdescent : baseEnd_2457942 < baseStart_2457942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2457948 : List Nat := [2, 2, 4, 3, 1, 2, 2, 2, 4]
def baseStart_2457948 : Nat := 118140960795 + 2457948 * 2 ^ 59
def prefixEnd_2457948 : Nat := 4983230072969 + 3 ^ 40 * 2457948 * 2
def baseEnd_2457948 : Nat := 280468610612767666854691

theorem tailTrace_2457948 : CollatzResearch.WordTrace tailWord_2457948 prefixEnd_2457948 280468610612767666854691 := by
  unfold tailWord_2457948
  simp only [CollatzResearch.WordTrace]
  refine ⟨44824364249640827471395249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59765818999521103295193665 44824364249640827471395249)
  ·
    refine ⟨33618273187230620603546437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44824364249640827471395249 33618273187230620603546437)
    ·
      refine ⟨6303426222605741363164957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33618273187230620603546437 6303426222605741363164957)
      ·
        refine ⟨2363784833477153011186859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6303426222605741363164957 2363784833477153011186859)
        ·
          refine ⟨3545677250215729516780289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363784833477153011186859 3545677250215729516780289)
          ·
            refine ⟨2659257937661797137585217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3545677250215729516780289 2659257937661797137585217)
            ·
              refine ⟨1994443453246347853188913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2659257937661797137585217 1994443453246347853188913)
              ·
                refine ⟨1495832589934760889891685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1994443453246347853188913 1495832589934760889891685)
                ·
                  refine ⟨280468610612767666854691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1495832589934760889891685 280468610612767666854691)
                  ·
                    rfl

theorem cell22_2457948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_2457948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2457948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2457948 prefixEnd_2457948 := by exact prefixLift 2457948
  have htrace : WordTrace (prefixWord ++ tailWord_2457948) baseStart_2457948 baseEnd_2457948 := by
    simpa [prefixWord, tailWord_2457948, baseEnd_2457948] using wordTrace_append hprefix tailTrace_2457948
  have hstable : (prefixWord ++ tailWord_2457948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2457948).length < 2 ^ (prefixWord ++ tailWord_2457948).sum := by decide
  have hdescent : baseEnd_2457948 < baseStart_2457948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2457948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458066 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 6]
def baseStart_2458066 : Nat := 118140960795 + 2458066 * 2 ^ 59
def prefixEnd_2458066 : Nat := 4983230072969 + 3 ^ 40 * 2458066 * 2
def baseEnd_2458066 : Nat := 280482075216596675371237

theorem tailTrace_2458066 : CollatzResearch.WordTrace tailWord_2458066 prefixEnd_2458066 280482075216596675371237 := by
  unfold tailWord_2458066
  simp only [CollatzResearch.WordTrace]
  refine ⟨22413258078213540273896513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59768688208569440730390701 22413258078213540273896513)
  ·
    refine ⟨16809943558660155205422385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22413258078213540273896513 16809943558660155205422385)
    ·
      refine ⟨12607457668995116404066789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16809943558660155205422385 12607457668995116404066789)
      ·
        refine ⟨2363898312936584325762523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12607457668995116404066789 2363898312936584325762523)
        ·
          refine ⟨3545847469404876488643785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363898312936584325762523 3545847469404876488643785)
          ·
            refine ⟨2659385602053657366482839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3545847469404876488643785 2659385602053657366482839)
            ·
              refine ⟨3989078403080486049724259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2659385602053657366482839 3989078403080486049724259)
              ·
                refine ⟨5983617604620729074586389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3989078403080486049724259 5983617604620729074586389)
                ·
                  refine ⟨280482075216596675371237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5983617604620729074586389 280482075216596675371237)
                  ·
                    rfl

theorem cell22_2458066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_2458066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458066 prefixEnd_2458066 := by exact prefixLift 2458066
  have htrace : WordTrace (prefixWord ++ tailWord_2458066) baseStart_2458066 baseEnd_2458066 := by
    simpa [prefixWord, tailWord_2458066, baseEnd_2458066] using wordTrace_append hprefix tailTrace_2458066
  have hstable : (prefixWord ++ tailWord_2458066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458066).length < 2 ^ (prefixWord ++ tailWord_2458066).sum := by decide
  have hdescent : baseEnd_2458066 < baseStart_2458066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458077 : List Nat := [1, 4, 3, 1, 1, 1, 4, 7]
def baseStart_2458077 : Nat := 118140960795 + 2458077 * 2 ^ 59
def prefixEnd_2458077 : Nat := 4983230072969 + 3 ^ 40 * 2458077 * 2
def baseEnd_2458077 : Nat := 93494443463843296009853

theorem tailTrace_2458077 : CollatzResearch.WordTrace tailWord_2458077 prefixEnd_2458077 93494443463843296009853 := by
  unfold tailWord_2458077
  simp only [CollatzResearch.WordTrace]
  refine ⟨89653433515814309974236485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59768955677209539982824323 89653433515814309974236485)
  ·
    refine ⟨16810018784215183120169341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89653433515814309974236485 16810018784215183120169341)
    ·
      refine ⟨6303757044080693670063503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16810018784215183120169341 6303757044080693670063503)
      ·
        refine ⟨9455635566121040505095255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6303757044080693670063503 9455635566121040505095255)
        ·
          refine ⟨14183453349181560757642883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9455635566121040505095255 14183453349181560757642883)
          ·
            refine ⟨21275180023772341136464325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14183453349181560757642883 21275180023772341136464325)
            ·
              refine ⟨3989096254457313963087061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21275180023772341136464325 3989096254457313963087061)
              ·
                refine ⟨93494443463843296009853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3989096254457313963087061 93494443463843296009853)
                ·
                  rfl

theorem cell22_2458077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 7].length) (baseStart_2458077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458077 prefixEnd_2458077 := by exact prefixLift 2458077
  have htrace : WordTrace (prefixWord ++ tailWord_2458077) baseStart_2458077 baseEnd_2458077 := by
    simpa [prefixWord, tailWord_2458077, baseEnd_2458077] using wordTrace_append hprefix tailTrace_2458077
  have hstable : (prefixWord ++ tailWord_2458077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458077).length < 2 ^ (prefixWord ++ tailWord_2458077).sum := by decide
  have hdescent : baseEnd_2458077 < baseStart_2458077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458092 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 5, 3]
def baseStart_2458092 : Nat := 118140960795 + 2458092 * 2 ^ 59
def prefixEnd_2458092 : Nat := 4983230072969 + 3 ^ 40 * 2458092 * 2
def baseEnd_2458092 : Nat := 841455125981134624963631

theorem tailTrace_2458092 : CollatzResearch.WordTrace tailWord_2458092 prefixEnd_2458092 841455125981134624963631 := by
  unfold tailWord_2458092
  simp only [CollatzResearch.WordTrace]
  refine ⟨44826990305379983768016265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59769320407173311690688353 44826990305379983768016265)
  ·
    refine ⟨33620242729034987826012199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44826990305379983768016265 33620242729034987826012199)
    ·
      refine ⟨50430364093552481739018299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33620242729034987826012199 50430364093552481739018299)
      ·
        refine ⟨75645546140328722608527449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50430364093552481739018299 75645546140328722608527449)
        ·
          refine ⟨56734159605246541956395587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75645546140328722608527449 56734159605246541956395587)
          ·
            refine ⟨85101239407869812934593381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56734159605246541956395587 85101239407869812934593381)
            ·
              refine ⟨15956482388975589925236259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85101239407869812934593381 15956482388975589925236259)
              ·
                refine ⟨23934723583463384887854389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15956482388975589925236259 23934723583463384887854389)
                ·
                  refine ⟨2243880335949692333236349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23934723583463384887854389 2243880335949692333236349)
                  ·
                    refine ⟨841455125981134624963631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2243880335949692333236349 841455125981134624963631)
                    ·
                      rfl

theorem cell22_2458092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_2458092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458092 prefixEnd_2458092 := by exact prefixLift 2458092
  have htrace : WordTrace (prefixWord ++ tailWord_2458092) baseStart_2458092 baseEnd_2458092 := by
    simpa [prefixWord, tailWord_2458092, baseEnd_2458092] using wordTrace_append hprefix tailTrace_2458092
  have hstable : (prefixWord ++ tailWord_2458092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458092).length < 2 ^ (prefixWord ++ tailWord_2458092).sum := by decide
  have hdescent : baseEnd_2458092 < baseStart_2458092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458105 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 9]
def baseStart_2458105 : Nat := 118140960795 + 2458105 * 2 ^ 59
def prefixEnd_2458105 : Nat := 4983230072969 + 3 ^ 40 * 2458105 * 2
def baseEnd_2458105 : Nat := 280486525382268974796197

theorem tailTrace_2458105 : CollatzResearch.WordTrace tailWord_2458105 prefixEnd_2458105 280486525382268974796197 := by
  unfold tailWord_2458105
  simp only [CollatzResearch.WordTrace]
  refine ⟨89654454759712870756255769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59769636506475247170837179 89654454759712870756255769)
  ·
    refine ⟨67240841069784653067191827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89654454759712870756255769 67240841069784653067191827)
    ·
      refine ⟨100861261604676979600787741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67240841069784653067191827 100861261604676979600787741)
      ·
        refine ⟨37822973101753867350295403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100861261604676979600787741 37822973101753867350295403)
        ·
          refine ⟨56734459652630801025443105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37822973101753867350295403 56734459652630801025443105)
          ·
            refine ⟨42550844739473100769082329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56734459652630801025443105 42550844739473100769082329)
            ·
              refine ⟨31913133554604825576811747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42550844739473100769082329 31913133554604825576811747)
              ·
                refine ⟨47869700331907238365217621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31913133554604825576811747 47869700331907238365217621)
                ·
                  refine ⟨280486525382268974796197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47869700331907238365217621 280486525382268974796197)
                  ·
                    rfl

theorem cell22_2458105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_2458105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458105 prefixEnd_2458105 := by exact prefixLift 2458105
  have htrace : WordTrace (prefixWord ++ tailWord_2458105) baseStart_2458105 baseEnd_2458105 := by
    simpa [prefixWord, tailWord_2458105, baseEnd_2458105] using wordTrace_append hprefix tailTrace_2458105
  have hstable : (prefixWord ++ tailWord_2458105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458105).length < 2 ^ (prefixWord ++ tailWord_2458105).sum := by decide
  have hdescent : baseEnd_2458105 < baseStart_2458105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458169 : List Nat := [1, 2, 1, 5, 1, 1, 3, 3, 1, 4]
def baseStart_2458169 : Nat := 118140960795 + 2458169 * 2 ^ 59
def prefixEnd_2458169 : Nat := 4983230072969 + 3 ^ 40 * 2458169 * 2
def baseEnd_2458169 : Nat := 841481484654732090788395

theorem tailTrace_2458169 : CollatzResearch.WordTrace tailWord_2458169 prefixEnd_2458169 841481484654732090788395 := by
  unfold tailWord_2458169
  simp only [CollatzResearch.WordTrace]
  refine ⟨89656789031481009686585561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59771192687654006457723707 89656789031481009686585561)
  ·
    refine ⟨67242591773610757264939171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89656789031481009686585561 67242591773610757264939171)
    ·
      refine ⟨100863887660416135897408757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67242591773610757264939171 100863887660416135897408757)
      ·
        refine ⟨9455989468164012740382071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100863887660416135897408757 9455989468164012740382071)
        ·
          refine ⟨14183984202246019110573107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9455989468164012740382071 14183984202246019110573107)
          ·
            refine ⟨21275976303369028665859661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14183984202246019110573107 21275976303369028665859661)
            ·
              refine ⟨7978491113763385749697373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21275976303369028665859661 7978491113763385749697373)
              ·
                refine ⟨2991934167661269656136515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7978491113763385749697373 2991934167661269656136515)
                ·
                  refine ⟨4487901251491904484204773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2991934167661269656136515 4487901251491904484204773)
                  ·
                    refine ⟨841481484654732090788395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4487901251491904484204773 841481484654732090788395)
                    ·
                      rfl

theorem cell22_2458169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_2458169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458169 prefixEnd_2458169 := by exact prefixLift 2458169
  have htrace : WordTrace (prefixWord ++ tailWord_2458169) baseStart_2458169 baseEnd_2458169 := by
    simpa [prefixWord, tailWord_2458169, baseEnd_2458169] using wordTrace_append hprefix tailTrace_2458169
  have hstable : (prefixWord ++ tailWord_2458169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458169).length < 2 ^ (prefixWord ++ tailWord_2458169).sum := by decide
  have hdescent : baseEnd_2458169 < baseStart_2458169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458197 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_2458197 : Nat := 118140960795 + 2458197 * 2 ^ 59
def prefixEnd_2458197 : Nat := 4983230072969 + 3 ^ 40 * 2458197 * 2
def baseEnd_2458197 : Nat := 841491069626949351088309

theorem tailTrace_2458197 : CollatzResearch.WordTrace tailWord_2458197 prefixEnd_2458197 841491069626949351088309 := by
  unfold tailWord_2458197
  simp only [CollatzResearch.WordTrace]
  refine ⟨89657810275379570468604845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59771873516919713645736563 89657810275379570468604845)
  ·
    refine ⟨33621678853267338925726817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89657810275379570468604845 33621678853267338925726817)
    ·
      refine ⟨25216259139950504194295113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33621678853267338925726817 25216259139950504194295113)
      ·
        refine ⟨18912194354962878145721335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25216259139950504194295113 18912194354962878145721335)
        ·
          refine ⟨28368291532444317218582003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18912194354962878145721335 28368291532444317218582003)
          ·
            refine ⟨42552437298666475827873005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28368291532444317218582003 42552437298666475827873005)
            ·
              refine ⟨15957163986999928435452377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42552437298666475827873005 15957163986999928435452377)
              ·
                refine ⟨11967872990249946326589283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15957163986999928435452377 11967872990249946326589283)
                ·
                  refine ⟨17951809485374919489883925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11967872990249946326589283 17951809485374919489883925)
                  ·
                    refine ⟨841491069626949351088309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17951809485374919489883925 841491069626949351088309)
                    ·
                      rfl

theorem cell22_2458197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_2458197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458197 prefixEnd_2458197 := by exact prefixLift 2458197
  have htrace : WordTrace (prefixWord ++ tailWord_2458197) baseStart_2458197 baseEnd_2458197 := by
    simpa [prefixWord, tailWord_2458197, baseEnd_2458197] using wordTrace_append hprefix tailTrace_2458197
  have hstable : (prefixWord ++ tailWord_2458197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458197).length < 2 ^ (prefixWord ++ tailWord_2458197).sum := by decide
  have hdescent : baseEnd_2458197 < baseStart_2458197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458212 : List Nat := [2, 3, 1, 1, 2, 2, 3, 8]
def baseStart_2458212 : Nat := 118140960795 + 2458212 * 2 ^ 59
def prefixEnd_2458212 : Nat := 4983230072969 + 3 ^ 40 * 2458212 * 2
def baseEnd_2458212 : Nat := 93499578270388256884807

theorem tailTrace_2458212 : CollatzResearch.WordTrace tailWord_2458212 prefixEnd_2458212 93499578270388256884807 := by
  unfold tailWord_2458212
  simp only [CollatzResearch.WordTrace]
  refine ⟨44829178685162614015200445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59772238246883485353600593 44829178685162614015200445)
  ·
    refine ⟨16810942006935980255700167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44829178685162614015200445 16810942006935980255700167)
    ·
      refine ⟨25216413010403970383550251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16810942006935980255700167 25216413010403970383550251)
      ·
        refine ⟨37824619515605955575325377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25216413010403970383550251 37824619515605955575325377)
        ·
          refine ⟨28368464636704466681494033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37824619515605955575325377 28368464636704466681494033)
          ·
            refine ⟨21276348477528350011120525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28368464636704466681494033 21276348477528350011120525)
            ·
              refine ⟨7978630679073131254170197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21276348477528350011120525 7978630679073131254170197)
              ·
                refine ⟨93499578270388256884807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7978630679073131254170197 93499578270388256884807)
                ·
                  rfl

theorem cell22_2458212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 8].length) (baseStart_2458212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458212 prefixEnd_2458212 := by exact prefixLift 2458212
  have htrace : WordTrace (prefixWord ++ tailWord_2458212) baseStart_2458212 baseEnd_2458212 := by
    simpa [prefixWord, tailWord_2458212, baseEnd_2458212] using wordTrace_append hprefix tailTrace_2458212
  have hstable : (prefixWord ++ tailWord_2458212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458212).length < 2 ^ (prefixWord ++ tailWord_2458212).sum := by decide
  have hdescent : baseEnd_2458212 < baseStart_2458212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458250 : List Nat := [3, 1, 2, 3, 3, 2, 2, 1, 2, 3]
def baseStart_2458250 : Nat := 118140960795 + 2458250 * 2 ^ 59
def prefixEnd_2458250 : Nat := 4983230072969 + 3 ^ 40 * 2458250 * 2
def baseEnd_2458250 : Nat := 841509212610074879513147

theorem tailTrace_2458250 : CollatzResearch.WordTrace tailWord_2458250 prefixEnd_2458250 841509212610074879513147 := by
  unfold tailWord_2458250
  simp only [CollatzResearch.WordTrace]
  refine ⟨22414935836046890130071051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59773162229458373680189469 22414935836046890130071051)
  ·
    refine ⟨33622403754070335195106577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22414935836046890130071051 33622403754070335195106577)
    ·
      refine ⟨25216802815552751396329933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33622403754070335195106577 25216802815552751396329933)
      ·
        refine ⟨9456301055832281773623725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25216802815552751396329933 9456301055832281773623725)
        ·
          refine ⟨3546112895937105665108897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9456301055832281773623725 3546112895937105665108897)
          ·
            refine ⟨2659584671952829248831673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3546112895937105665108897 2659584671952829248831673)
            ·
              refine ⟨1994688503964621936623755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2659584671952829248831673 1994688503964621936623755)
              ·
                refine ⟨2992032755946932904935633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1994688503964621936623755 2992032755946932904935633)
                ·
                  refine ⟨2244024566960199678701725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2992032755946932904935633 2244024566960199678701725)
                  ·
                    refine ⟨841509212610074879513147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2244024566960199678701725 841509212610074879513147)
                    ·
                      rfl

theorem cell22_2458250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_2458250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458250 prefixEnd_2458250 := by exact prefixLift 2458250
  have htrace : WordTrace (prefixWord ++ tailWord_2458250) baseStart_2458250 baseEnd_2458250 := by
    simpa [prefixWord, tailWord_2458250, baseEnd_2458250] using wordTrace_append hprefix tailTrace_2458250
  have hstable : (prefixWord ++ tailWord_2458250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458250).length < 2 ^ (prefixWord ++ tailWord_2458250).sum := by decide
  have hdescent : baseEnd_2458250 < baseStart_2458250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458304 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 3, 4]
def baseStart_2458304 : Nat := 118140960795 + 2458304 * 2 ^ 59
def prefixEnd_2458304 : Nat := 4983230072969 + 3 ^ 40 * 2458304 * 2
def baseEnd_2458304 : Nat := 841527697913636738662981

theorem tailTrace_2458304 : CollatzResearch.WordTrace tailWord_2458304 prefixEnd_2458304 841527697913636738662981 := by
  unfold tailWord_2458304
  simp only [CollatzResearch.WordTrace]
  refine ⟨44830856442995963871374983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59774475257327951828499977 44830856442995963871374983)
  ·
    refine ⟨67246284664493945807062475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44830856442995963871374983 67246284664493945807062475)
    ·
      refine ⟨100869426996740918710593713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67246284664493945807062475 100869426996740918710593713)
      ·
        refine ⟨75652070247555689032945285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100869426996740918710593713 75652070247555689032945285)
        ·
          refine ⟨14184763171416691693677241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75652070247555689032945285 14184763171416691693677241)
          ·
            refine ⟨10638572378562518770257931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14184763171416691693677241 10638572378562518770257931)
            ·
              refine ⟨15957858567843778155386897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10638572378562518770257931 15957858567843778155386897)
              ·
                refine ⟨11968393925882833616540173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15957858567843778155386897 11968393925882833616540173)
                ·
                  refine ⟨4488147722206062606202565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11968393925882833616540173 4488147722206062606202565)
                  ·
                    refine ⟨841527697913636738662981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4488147722206062606202565 841527697913636738662981)
                    ·
                      rfl

theorem cell22_2458304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_2458304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458304 prefixEnd_2458304 := by exact prefixLift 2458304
  have htrace : WordTrace (prefixWord ++ tailWord_2458304) baseStart_2458304 baseEnd_2458304 := by
    simpa [prefixWord, tailWord_2458304, baseEnd_2458304] using wordTrace_append hprefix tailTrace_2458304
  have hstable : (prefixWord ++ tailWord_2458304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458304).length < 2 ^ (prefixWord ++ tailWord_2458304).sum := by decide
  have hdescent : baseEnd_2458304 < baseStart_2458304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458351 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 4, 3]
def baseStart_2458351 : Nat := 118140960795 + 2458351 * 2 ^ 59
def prefixEnd_2458351 : Nat := 4983230072969 + 3 ^ 40 * 2458351 * 2
def baseEnd_2458351 : Nat := 841543786974144282737837

theorem tailTrace_2458351 : CollatzResearch.WordTrace tailWord_2458351 prefixEnd_2458351 841543786974144282737837 := by
  unfold tailWord_2458351
  simp only [CollatzResearch.WordTrace]
  refine ⟨89663427116821654769710907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59775618077881103179807271 89663427116821654769710907)
  ·
    refine ⟨134495140675232482154566361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89663427116821654769710907 134495140675232482154566361)
    ·
      refine ⟨100871355506424361615924771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134495140675232482154566361 100871355506424361615924771)
      ·
        refine ⟨151307033259636542423887157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100871355506424361615924771 151307033259636542423887157)
        ·
          refine ⟨14185034368090925852239421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151307033259636542423887157 14185034368090925852239421)
          ·
            refine ⟨5319387888034097194589783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14185034368090925852239421 5319387888034097194589783)
            ·
              refine ⟨7979081832051145791884675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5319387888034097194589783 7979081832051145791884675)
              ·
                refine ⟨11968622748076718687827013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7979081832051145791884675 11968622748076718687827013)
                ·
                  refine ⟨2244116765264384753967565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11968622748076718687827013 2244116765264384753967565)
                  ·
                    refine ⟨841543786974144282737837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2244116765264384753967565 841543786974144282737837)
                    ·
                      rfl

theorem cell22_2458351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 3].length) (baseStart_2458351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458351 prefixEnd_2458351 := by exact prefixLift 2458351
  have htrace : WordTrace (prefixWord ++ tailWord_2458351) baseStart_2458351 baseEnd_2458351 := by
    simpa [prefixWord, tailWord_2458351, baseEnd_2458351] using wordTrace_append hprefix tailTrace_2458351
  have hstable : (prefixWord ++ tailWord_2458351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458351).length < 2 ^ (prefixWord ++ tailWord_2458351).sum := by decide
  have hdescent : baseEnd_2458351 < baseStart_2458351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458366 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2458366 : Nat := 118140960795 + 2458366 * 2 ^ 59
def prefixEnd_2458366 : Nat := 4983230072969 + 3 ^ 40 * 2458366 * 2
def baseEnd_2458366 : Nat := 841548921780689243612791

theorem tailTrace_2458366 : CollatzResearch.WordTrace tailWord_2458366 prefixEnd_2458366 841548921780689243612791 := by
  unfold tailWord_2458366
  simp only [CollatzResearch.WordTrace]
  refine ⟨11207996776470914041438369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59775982807844874887671301 11207996776470914041438369)
  ·
    refine ⟨8405997582353185531078777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11207996776470914041438369 8405997582353185531078777)
    ·
      refine ⟨6304498186764889148309083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8405997582353185531078777 6304498186764889148309083)
      ·
        refine ⟨9456747280147333722463625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6304498186764889148309083 9456747280147333722463625)
        ·
          refine ⟨7092560460110500291847719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9456747280147333722463625 7092560460110500291847719)
          ·
            refine ⟨10638840690165750437771579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7092560460110500291847719 10638840690165750437771579)
            ·
              refine ⟨15958261035248625656657369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10638840690165750437771579 15958261035248625656657369)
              ·
                refine ⟨11968695776436469242493027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15958261035248625656657369 11968695776436469242493027)
                ·
                  refine ⟨17953043664654703863739541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11968695776436469242493027 17953043664654703863739541)
                  ·
                    refine ⟨841548921780689243612791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17953043664654703863739541 841548921780689243612791)
                    ·
                      rfl

theorem cell22_2458366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2458366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458366 prefixEnd_2458366 := by exact prefixLift 2458366
  have htrace : WordTrace (prefixWord ++ tailWord_2458366) baseStart_2458366 baseEnd_2458366 := by
    simpa [prefixWord, tailWord_2458366, baseEnd_2458366] using wordTrace_append hprefix tailTrace_2458366
  have hstable : (prefixWord ++ tailWord_2458366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458366).length < 2 ^ (prefixWord ++ tailWord_2458366).sum := by decide
  have hdescent : baseEnd_2458366 < baseStart_2458366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458424 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 1, 7]
def baseStart_2458424 : Nat := 118140960795 + 2458424 * 2 ^ 59
def prefixEnd_2458424 : Nat := 4983230072969 + 3 ^ 40 * 2458424 * 2
def baseEnd_2458424 : Nat := 841568776365996425662613

theorem tailTrace_2458424 : CollatzResearch.WordTrace tailWord_2458424 prefixEnd_2458424 841568776365996425662613 := by
  unfold tailWord_2458424
  simp only [CollatzResearch.WordTrace]
  refine ⟨44833044822778594118559163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59777393097038125491412217 44833044822778594118559163)
  ·
    refine ⟨67249567234167891177838745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44833044822778594118559163 67249567234167891177838745)
    ·
      refine ⟨50437175425625918383379059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67249567234167891177838745 50437175425625918383379059)
      ·
        refine ⟨75655763138438877575068589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50437175425625918383379059 75655763138438877575068589)
        ·
          refine ⟨28370911176914579090650721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75655763138438877575068589 28370911176914579090650721)
          ·
            refine ⟨21278183382685934317988041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28370911176914579090650721 21278183382685934317988041)
            ·
              refine ⟨15958637537014450738491031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21278183382685934317988041 15958637537014450738491031)
              ·
                refine ⟨23937956305521676107736547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15958637537014450738491031 23937956305521676107736547)
                ·
                  refine ⟨35906934458282514161604821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23937956305521676107736547 35906934458282514161604821)
                  ·
                    refine ⟨841568776365996425662613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35906934458282514161604821 841568776365996425662613)
                    ·
                      rfl

theorem cell22_2458424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_2458424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458424 prefixEnd_2458424 := by exact prefixLift 2458424
  have htrace : WordTrace (prefixWord ++ tailWord_2458424) baseStart_2458424 baseEnd_2458424 := by
    simpa [prefixWord, tailWord_2458424, baseEnd_2458424] using wordTrace_append hprefix tailTrace_2458424
  have hstable : (prefixWord ++ tailWord_2458424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458424).length < 2 ^ (prefixWord ++ tailWord_2458424).sum := by decide
  have hdescent : baseEnd_2458424 < baseStart_2458424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458456 : List Nat := [2, 1, 2, 2, 1, 1, 1, 7, 1, 4]
def baseStart_2458456 : Nat := 118140960795 + 2458456 * 2 ^ 59
def prefixEnd_2458456 : Nat := 4983230072969 + 3 ^ 40 * 2458456 * 2
def baseEnd_2458456 : Nat := 841579730619959008862515

theorem tailTrace_2458456 : CollatzResearch.WordTrace tailWord_2458456 prefixEnd_2458456 841579730619959008862515 := by
  unfold tailWord_2458456
  simp only [CollatzResearch.WordTrace]
  refine ⟨44833628390720628851141611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59778171187627505134855481 44833628390720628851141611)
  ·
    refine ⟨67250442586080943276712417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44833628390720628851141611 67250442586080943276712417)
    ·
      refine ⟨50437831939560707457534313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67250442586080943276712417 50437831939560707457534313)
      ·
        refine ⟨37828373954670530593150735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50437831939560707457534313 37828373954670530593150735)
        ·
          refine ⟨56742560932005795889726103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37828373954670530593150735 56742560932005795889726103)
          ·
            refine ⟨85113841398008693834589155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56742560932005795889726103 85113841398008693834589155)
            ·
              refine ⟨127670762097013040751883733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85113841398008693834589155 127670762097013040751883733)
              ·
                refine ⟨2992283486648743142622275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 127670762097013040751883733 2992283486648743142622275)
                ·
                  refine ⟨4488425229973114713933413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2992283486648743142622275 4488425229973114713933413)
                  ·
                    refine ⟨841579730619959008862515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4488425229973114713933413 841579730619959008862515)
                    ·
                      rfl

theorem cell22_2458456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_2458456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458456 prefixEnd_2458456 := by exact prefixLift 2458456
  have htrace : WordTrace (prefixWord ++ tailWord_2458456) baseStart_2458456 baseEnd_2458456 := by
    simpa [prefixWord, tailWord_2458456, baseEnd_2458456] using wordTrace_append hprefix tailTrace_2458456
  have hstable : (prefixWord ++ tailWord_2458456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458456).length < 2 ^ (prefixWord ++ tailWord_2458456).sum := by decide
  have hdescent : baseEnd_2458456 < baseStart_2458456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458501 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_2458501 : Nat := 118140960795 + 2458501 * 2 ^ 59
def prefixEnd_2458501 : Nat := 4983230072969 + 3 ^ 40 * 2458501 * 2
def baseEnd_2458501 : Nat := 841595135039593891487377

theorem tailTrace_2458501 : CollatzResearch.WordTrace tailWord_2458501 prefixEnd_2458501 841595135039593891487377 := by
  unfold tailWord_2458501
  simp only [CollatzResearch.WordTrace]
  refine ⟨89668898066278230387671357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59779265377518820258447571 89668898066278230387671357)
  ·
    refine ⟨33625836774854336395376759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89668898066278230387671357 33625836774854336395376759)
    ·
      refine ⟨50438755162281504593065139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33625836774854336395376759 50438755162281504593065139)
      ·
        refine ⟨75658132743422256889597709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50438755162281504593065139 75658132743422256889597709)
        ·
          refine ⟨28371799778783346333599141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75658132743422256889597709 28371799778783346333599141)
          ·
            refine ⟨5319712458521877437549839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28371799778783346333599141 5319712458521877437549839)
            ·
              refine ⟨7979568687782816156324759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5319712458521877437549839 7979568687782816156324759)
              ·
                refine ⟨11969353031674224234487139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7979568687782816156324759 11969353031674224234487139)
                ·
                  refine ⟨17954029547511336351730709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11969353031674224234487139 17954029547511336351730709)
                  ·
                    refine ⟨841595135039593891487377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17954029547511336351730709 841595135039593891487377)
                    ·
                      rfl

theorem cell22_2458501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_2458501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458501 prefixEnd_2458501 := by exact prefixLift 2458501
  have htrace : WordTrace (prefixWord ++ tailWord_2458501) baseStart_2458501 baseEnd_2458501 := by
    simpa [prefixWord, tailWord_2458501, baseEnd_2458501] using wordTrace_append hprefix tailTrace_2458501
  have hstable : (prefixWord ++ tailWord_2458501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458501).length < 2 ^ (prefixWord ++ tailWord_2458501).sum := by decide
  have hdescent : baseEnd_2458501 < baseStart_2458501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458516 : List Nat := [2, 4, 2, 1, 1, 1, 11]
def baseStart_2458516 : Nat := 118140960795 + 2458516 * 2 ^ 59
def prefixEnd_2458516 : Nat := 4983230072969 + 3 ^ 40 * 2458516 * 2
def baseEnd_2458516 : Nat := 31170380364671809346753

theorem tailTrace_2458516 : CollatzResearch.WordTrace tailWord_2458516 prefixEnd_2458516 31170380364671809346753 := by
  unfold tailWord_2458516
  simp only [CollatzResearch.WordTrace]
  refine ⟨44834722580611943974733701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59779630107482591966311601 44834722580611943974733701)
  ·
    refine ⟨8406510483864739495262569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44834722580611943974733701 8406510483864739495262569)
    ·
      refine ⟨6304882862898554621446927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8406510483864739495262569 6304882862898554621446927)
      ·
        refine ⟨9457324294347831932170391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6304882862898554621446927 9457324294347831932170391)
        ·
          refine ⟨14185986441521747898255587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9457324294347831932170391 14185986441521747898255587)
          ·
            refine ⟨21278979662282621847383381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14185986441521747898255587 21278979662282621847383381)
            ·
              refine ⟨31170380364671809346753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21278979662282621847383381 31170380364671809346753)
              ·
                rfl

theorem cell22_2458516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 11].length) (baseStart_2458516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458516 prefixEnd_2458516 := by exact prefixLift 2458516
  have htrace : WordTrace (prefixWord ++ tailWord_2458516) baseStart_2458516 baseEnd_2458516 := by
    simpa [prefixWord, tailWord_2458516, baseEnd_2458516] using wordTrace_append hprefix tailTrace_2458516
  have hstable : (prefixWord ++ tailWord_2458516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458516).length < 2 ^ (prefixWord ++ tailWord_2458516).sum := by decide
  have hdescent : baseEnd_2458516 < baseStart_2458516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458578 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 7]
def baseStart_2458578 : Nat := 118140960795 + 2458578 * 2 ^ 59
def prefixEnd_2458578 : Nat := 4983230072969 + 3 ^ 40 * 2458578 * 2
def baseEnd_2458578 : Nat := 280540497904397119104047

theorem tailTrace_2458578 : CollatzResearch.WordTrace tailWord_2458578 prefixEnd_2458578 280540497904397119104047 := by
  unfold tailWord_2458578
  simp only [CollatzResearch.WordTrace]
  refine ⟨22417926621749818134556097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59781137657999515025482925 22417926621749818134556097)
  ·
    refine ⟨16813444966312363600917073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22417926621749818134556097 16813444966312363600917073)
    ·
      refine ⟨12610083724734272700687805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16813444966312363600917073 12610083724734272700687805)
      ·
        refine ⟨4728781396775352262757927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12610083724734272700687805 4728781396775352262757927)
        ·
          refine ⟨7093172095163028394136891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4728781396775352262757927 7093172095163028394136891)
          ·
            refine ⟨10639758142744542591205337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7093172095163028394136891 10639758142744542591205337)
            ·
              refine ⟨7979818607058406943404003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10639758142744542591205337 7979818607058406943404003)
              ·
                refine ⟨11969727910587610415106005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7979818607058406943404003 11969727910587610415106005)
                ·
                  refine ⟨280540497904397119104047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11969727910587610415106005 280540497904397119104047)
                  ·
                    rfl

theorem cell22_2458578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_2458578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458578 prefixEnd_2458578 := by exact prefixLift 2458578
  have htrace : WordTrace (prefixWord ++ tailWord_2458578) baseStart_2458578 baseEnd_2458578 := by
    simpa [prefixWord, tailWord_2458578, baseEnd_2458578] using wordTrace_append hprefix tailTrace_2458578
  have hstable : (prefixWord ++ tailWord_2458578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458578).length < 2 ^ (prefixWord ++ tailWord_2458578).sum := by decide
  have hdescent : baseEnd_2458578 < baseStart_2458578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458582 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_2458582 : Nat := 118140960795 + 2458582 * 2 ^ 59
def prefixEnd_2458582 : Nat := 4983230072969 + 3 ^ 40 * 2458582 * 2
def baseEnd_2458582 : Nat := 841622862994936680212129

theorem tailTrace_2458582 : CollatzResearch.WordTrace tailWord_2458582 prefixEnd_2458582 841622862994936680212129 := by
  unfold tailWord_2458582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5604490773686548826335625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59781234919323187480913333 5604490773686548826335625)
  ·
    refine ⟨4203368080264911619751719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5604490773686548826335625 4203368080264911619751719)
    ·
      refine ⟨6305052120397367429627579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4203368080264911619751719 6305052120397367429627579)
      ·
        refine ⟨9457578180596051144441369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6305052120397367429627579 9457578180596051144441369)
        ·
          refine ⟨7093183635447038358331027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9457578180596051144441369 7093183635447038358331027)
          ·
            refine ⟨10639775453170557537496541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7093183635447038358331027 10639775453170557537496541)
            ·
              refine ⟨3989915794938959076561203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10639775453170557537496541 3989915794938959076561203)
              ·
                refine ⟨5984873692408438614841805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3989915794938959076561203 5984873692408438614841805)
                ·
                  refine ⟨2244327634653164480565677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5984873692408438614841805 2244327634653164480565677)
                  ·
                    refine ⟨841622862994936680212129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2244327634653164480565677 841622862994936680212129)
                    ·
                      rfl

theorem cell22_2458582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_2458582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458582 prefixEnd_2458582 := by exact prefixLift 2458582
  have htrace : WordTrace (prefixWord ++ tailWord_2458582) baseStart_2458582 baseEnd_2458582 := by
    simpa [prefixWord, tailWord_2458582, baseEnd_2458582] using wordTrace_append hprefix tailTrace_2458582
  have hstable : (prefixWord ++ tailWord_2458582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458582).length < 2 ^ (prefixWord ++ tailWord_2458582).sum := by decide
  have hdescent : baseEnd_2458582 < baseStart_2458582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458655 : List Nat := [1, 1, 2, 4, 1, 3, 2, 3, 2, 3]
def baseStart_2458655 : Nat := 118140960795 + 2458655 * 2 ^ 59
def prefixEnd_2458655 : Nat := 4983230072969 + 3 ^ 40 * 2458655 * 2
def baseEnd_2458655 : Nat := 841647852386788823136905

theorem tailTrace_2458655 : CollatzResearch.WordTrace tailWord_2458655 prefixEnd_2458655 841647852386788823136905 := by
  unfold tailWord_2458655
  simp only [CollatzResearch.WordTrace]
  refine ⟨89674514907720314688777419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59783009938480209792518279 89674514907720314688777419)
  ·
    refine ⟨134511772361580472033166129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89674514907720314688777419 134511772361580472033166129)
    ·
      refine ⟨100883829271185354024874597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134511772361580472033166129 100883829271185354024874597)
      ·
        refine ⟨18915717988347253879663987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100883829271185354024874597 18915717988347253879663987)
        ·
          refine ⟨28373576982520880819495981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18915717988347253879663987 28373576982520880819495981)
          ·
            refine ⟨10640091368445330307310993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28373576982520880819495981 10640091368445330307310993)
            ·
              refine ⟨7980068526333997730483245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10640091368445330307310993 7980068526333997730483245)
              ·
                refine ⟨2992525697375249148931217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7980068526333997730483245 2992525697375249148931217)
                ·
                  refine ⟨2244394273031436861698413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2992525697375249148931217 2244394273031436861698413)
                  ·
                    refine ⟨841647852386788823136905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2244394273031436861698413 841647852386788823136905)
                    ·
                      rfl

theorem cell22_2458655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 3].length) (baseStart_2458655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458655 prefixEnd_2458655 := by exact prefixLift 2458655
  have htrace : WordTrace (prefixWord ++ tailWord_2458655) baseStart_2458655 baseEnd_2458655 := by
    simpa [prefixWord, tailWord_2458655, baseEnd_2458655] using wordTrace_append hprefix tailTrace_2458655
  have hstable : (prefixWord ++ tailWord_2458655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458655).length < 2 ^ (prefixWord ++ tailWord_2458655).sum := by decide
  have hdescent : baseEnd_2458655 < baseStart_2458655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458668 : List Nat := [2, 2, 1, 1, 1, 2, 7, 6]
def baseStart_2458668 : Nat := 118140960795 + 2458668 * 2 ^ 59
def prefixEnd_2458668 : Nat := 4983230072969 + 3 ^ 40 * 2458668 * 2
def baseEnd_2458668 : Nat := 93516922505829013617985

theorem tailTrace_2458668 : CollatzResearch.WordTrace tailWord_2458668 prefixEnd_2458668 93516922505829013617985 := by
  unfold tailWord_2458668
  simp only [CollatzResearch.WordTrace]
  refine ⟨44837494528336608954500329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59783326037782145272667105 44837494528336608954500329)
  ·
    refine ⟨33628120896252456715875247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44837494528336608954500329 33628120896252456715875247)
    ·
      refine ⟨50442181344378685073812871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33628120896252456715875247 50442181344378685073812871)
      ·
        refine ⟨75663272016568027610719307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50442181344378685073812871 75663272016568027610719307)
        ·
          refine ⟨113494908024852041416078961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75663272016568027610719307 113494908024852041416078961)
          ·
            refine ⟨85121181018639031062059221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113494908024852041416078961 85121181018639031062059221)
            ·
              refine ⟨1995027680124352290517013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 85121181018639031062059221 1995027680124352290517013)
              ·
                refine ⟨93516922505829013617985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1995027680124352290517013 93516922505829013617985)
                ·
                  rfl

theorem cell22_2458668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 6].length) (baseStart_2458668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458668 prefixEnd_2458668 := by exact prefixLift 2458668
  have htrace : WordTrace (prefixWord ++ tailWord_2458668) baseStart_2458668 baseEnd_2458668 := by
    simpa [prefixWord, tailWord_2458668, baseEnd_2458668] using wordTrace_append hprefix tailTrace_2458668
  have hstable : (prefixWord ++ tailWord_2458668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458668).length < 2 ^ (prefixWord ++ tailWord_2458668).sum := by decide
  have hdescent : baseEnd_2458668 < baseStart_2458668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458689 : List Nat := [1, 2, 5, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2458689 : Nat := 118140960795 + 2458689 * 2 ^ 59
def prefixEnd_2458689 : Nat := 4983230072969 + 3 ^ 40 * 2458689 * 2
def baseEnd_2458689 : Nat := 841659491281624067786801

theorem tailTrace_2458689 : CollatzResearch.WordTrace tailWord_2458689 prefixEnd_2458689 841659491281624067786801 := by
  unfold tailWord_2458689
  simp only [CollatzResearch.WordTrace]
  refine ⟨89675754989597138495515121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59783836659731425663676747 89675754989597138495515121)
  ·
    refine ⟨67256816242197853871636341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89675754989597138495515121 67256816242197853871636341)
    ·
      refine ⟨6305326522706048800465907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67256816242197853871636341 6305326522706048800465907)
      ·
        refine ⟨9457989784059073200698861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6305326522706048800465907 9457989784059073200698861)
        ·
          refine ⟨3546746169022152450262073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9457989784059073200698861 3546746169022152450262073)
          ·
            refine ⟨2660059626766614337696555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3546746169022152450262073 2660059626766614337696555)
            ·
              refine ⟨3990089440149921506544833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2660059626766614337696555 3990089440149921506544833)
              ·
                refine ⟨2992567080112441129908625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3990089440149921506544833 2992567080112441129908625)
                ·
                  refine ⟨2244425310084330847431469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2992567080112441129908625 2244425310084330847431469)
                  ·
                    refine ⟨841659491281624067786801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2244425310084330847431469 841659491281624067786801)
                    ·
                      rfl

theorem cell22_2458689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2458689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458689 prefixEnd_2458689 := by exact prefixLift 2458689
  have htrace : WordTrace (prefixWord ++ tailWord_2458689) baseStart_2458689 baseEnd_2458689 := by
    simpa [prefixWord, tailWord_2458689, baseEnd_2458689] using wordTrace_append hprefix tailTrace_2458689
  have hstable : (prefixWord ++ tailWord_2458689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458689).length < 2 ^ (prefixWord ++ tailWord_2458689).sum := by decide
  have hdescent : baseEnd_2458689 < baseStart_2458689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458734 : List Nat := [4, 1, 2, 2, 1, 2, 3, 3, 1, 3]
def baseStart_2458734 : Nat := 118140960795 + 2458734 * 2 ^ 59
def prefixEnd_2458734 : Nat := 4983230072969 + 3 ^ 40 * 2458734 * 2
def baseEnd_2458734 : Nat := 841674895701258950411663

theorem tailTrace_2458734 : CollatzResearch.WordTrace tailWord_2458734 prefixEnd_2458734 841674895701258950411663 := by
  unfold tailWord_2458734
  simp only [CollatzResearch.WordTrace]
  refine ⟨11209674534304263897612907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59784930849622740787268837 11209674534304263897612907)
  ·
    refine ⟨16814511801456395846419361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11209674534304263897612907 16814511801456395846419361)
    ·
      refine ⟨12610883851092296884814521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16814511801456395846419361 12610883851092296884814521)
      ·
        refine ⟨9458162888319222663610891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12610883851092296884814521 9458162888319222663610891)
        ·
          refine ⟨14187244332478833995416337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9458162888319222663610891 14187244332478833995416337)
          ·
            refine ⟨10640433249359125496562253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14187244332478833995416337 10640433249359125496562253)
            ·
              refine ⟨3990162468509672061210845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10640433249359125496562253 3990162468509672061210845)
              ·
                refine ⟨1496310925691127022954067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3990162468509672061210845 1496310925691127022954067)
                ·
                  refine ⟨2244466388536690534431101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1496310925691127022954067 2244466388536690534431101)
                  ·
                    refine ⟨841674895701258950411663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2244466388536690534431101 841674895701258950411663)
                    ·
                      rfl

theorem cell22_2458734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_2458734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458734 prefixEnd_2458734 := by exact prefixLift 2458734
  have htrace : WordTrace (prefixWord ++ tailWord_2458734) baseStart_2458734 baseEnd_2458734 := by
    simpa [prefixWord, tailWord_2458734, baseEnd_2458734] using wordTrace_append hprefix tailTrace_2458734
  have hstable : (prefixWord ++ tailWord_2458734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458734).length < 2 ^ (prefixWord ++ tailWord_2458734).sum := by decide
  have hdescent : baseEnd_2458734 < baseStart_2458734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458807 : List Nat := [1, 1, 3, 1, 4, 1, 4, 2, 2, 3]
def baseStart_2458807 : Nat := 118140960795 + 2458807 * 2 ^ 59
def prefixEnd_2458807 : Nat := 4983230072969 + 3 ^ 40 * 2458807 * 2
def baseEnd_2458807 : Nat := 841699885093111093336439

theorem tailTrace_2458807 : CollatzResearch.WordTrace tailWord_2458807 prefixEnd_2458807 841699885093111093336439 := by
  unfold tailWord_2458807
  simp only [CollatzResearch.WordTrace]
  refine ⟨89680058803169644648310675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59786705868779763098873783 89680058803169644648310675)
  ·
    refine ⟨134520088204754466972466013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89680058803169644648310675 134520088204754466972466013)
    ·
      refine ⟨50445033076782925114674755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134520088204754466972466013 50445033076782925114674755)
      ·
        refine ⟨75667549615174387672012133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50445033076782925114674755 75667549615174387672012133)
        ·
          refine ⟨14187665552845197688502275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75667549615174387672012133 14187665552845197688502275)
          ·
            refine ⟨21281498329267796532753413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14187665552845197688502275 21281498329267796532753413)
            ·
              refine ⟨3990280936737711849891265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21281498329267796532753413 3990280936737711849891265)
              ·
                refine ⟨2992710702553283887418449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3990280936737711849891265 2992710702553283887418449)
                ·
                  refine ⟨2244533026914962915563837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2992710702553283887418449 2244533026914962915563837)
                  ·
                    refine ⟨841699885093111093336439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2244533026914962915563837 841699885093111093336439)
                    ·
                      rfl

theorem cell22_2458807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_2458807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458807 prefixEnd_2458807 := by exact prefixLift 2458807
  have htrace : WordTrace (prefixWord ++ tailWord_2458807) baseStart_2458807 baseEnd_2458807 := by
    simpa [prefixWord, tailWord_2458807, baseEnd_2458807] using wordTrace_append hprefix tailTrace_2458807
  have hstable : (prefixWord ++ tailWord_2458807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458807).length < 2 ^ (prefixWord ++ tailWord_2458807).sum := by decide
  have hdescent : baseEnd_2458807 < baseStart_2458807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458809 : List Nat := [1, 2, 1, 4, 1, 5, 2, 2, 4]
def baseStart_2458809 : Nat := 118140960795 + 2458809 * 2 ^ 59
def prefixEnd_2458809 : Nat := 4983230072969 + 3 ^ 40 * 2458809 * 2
def baseEnd_2458809 : Nat := 280566856577994584928811

theorem tailTrace_2458809 : CollatzResearch.WordTrace tailWord_2458809 prefixEnd_2458809 280566856577994584928811 := by
  unfold tailWord_2458809
  simp only [CollatzResearch.WordTrace]
  refine ⟨89680131749162398989883481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59786754499441599326588987 89680131749162398989883481)
  ·
    refine ⟨67260098811871799242412611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89680131749162398989883481 67260098811871799242412611)
    ·
      refine ⟨100890148217807698863618917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67260098811871799242412611 100890148217807698863618917)
      ·
        refine ⟨18916902790838943536928547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100890148217807698863618917 18916902790838943536928547)
        ·
          refine ⟨28375354186258415305392821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18916902790838943536928547 28375354186258415305392821)
          ·
            refine ⟨2660189454961726434880577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28375354186258415305392821 2660189454961726434880577)
            ·
              refine ⟨1995142091221294826160433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2660189454961726434880577 1995142091221294826160433)
              ·
                refine ⟨1496356568415971119620325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1995142091221294826160433 1496356568415971119620325)
                ·
                  refine ⟨280566856577994584928811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1496356568415971119620325 280566856577994584928811)
                  ·
                    rfl

theorem cell22_2458809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 4].length) (baseStart_2458809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458809 prefixEnd_2458809 := by exact prefixLift 2458809
  have htrace : WordTrace (prefixWord ++ tailWord_2458809) baseStart_2458809 baseEnd_2458809 := by
    simpa [prefixWord, tailWord_2458809, baseEnd_2458809] using wordTrace_append hprefix tailTrace_2458809
  have hstable : (prefixWord ++ tailWord_2458809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458809).length < 2 ^ (prefixWord ++ tailWord_2458809).sum := by decide
  have hdescent : baseEnd_2458809 < baseStart_2458809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458833 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 4, 6]
def baseStart_2458833 : Nat := 118140960795 + 2458833 * 2 ^ 59
def prefixEnd_2458833 : Nat := 4983230072969 + 3 ^ 40 * 2458833 * 2
def baseEnd_2458833 : Nat := 841708785424455692186359

theorem tailTrace_2458833 : CollatzResearch.WordTrace tailWord_2458833 prefixEnd_2458833 841708785424455692186359 := by
  unfold tailWord_2458833
  simp only [CollatzResearch.WordTrace]
  refine ⟨89681007101075451088757153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59787338067383634059171435 89681007101075451088757153)
  ·
    refine ⟨67260755325806588316567865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89681007101075451088757153 67260755325806588316567865)
    ·
      refine ⟨50445566494354941237425899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67260755325806588316567865 50445566494354941237425899)
      ·
        refine ⟨75668349741532411856138849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50445566494354941237425899 75668349741532411856138849)
        ·
          refine ⟨56751262306149308892104137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75668349741532411856138849 56751262306149308892104137)
          ·
            refine ⟨42563446729611981669078103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56751262306149308892104137 42563446729611981669078103)
            ·
              refine ⟨63845170094417972503617155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42563446729611981669078103 63845170094417972503617155)
              ·
                refine ⟨95767755141626958755425733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63845170094417972503617155 95767755141626958755425733)
                ·
                  refine ⟨17956454089055054766642325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95767755141626958755425733 17956454089055054766642325)
                  ·
                    refine ⟨841708785424455692186359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17956454089055054766642325 841708785424455692186359)
                    ·
                      rfl

theorem cell22_2458833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_2458833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458833 prefixEnd_2458833 := by exact prefixLift 2458833
  have htrace : WordTrace (prefixWord ++ tailWord_2458833) baseStart_2458833 baseEnd_2458833 := by
    simpa [prefixWord, tailWord_2458833, baseEnd_2458833] using wordTrace_append hprefix tailTrace_2458833
  have hstable : (prefixWord ++ tailWord_2458833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458833).length < 2 ^ (prefixWord ++ tailWord_2458833).sum := by decide
  have hdescent : baseEnd_2458833 < baseStart_2458833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458835 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 3, 3]
def baseStart_2458835 : Nat := 118140960795 + 2458835 * 2 ^ 59
def prefixEnd_2458835 : Nat := 4983230072969 + 3 ^ 40 * 2458835 * 2
def baseEnd_2458835 : Nat := 841709470065328353636353

theorem tailTrace_2458835 : CollatzResearch.WordTrace tailWord_2458835 prefixEnd_2458835 841709470065328353636353 := by
  unfold tailWord_2458835
  simp only [CollatzResearch.WordTrace]
  refine ⟨89681080047068205430329959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59787386698045470286886639 89681080047068205430329959)
  ·
    refine ⟨134521620070602308145494939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89681080047068205430329959 134521620070602308145494939)
    ·
      refine ⟨201782430105903462218242409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134521620070602308145494939 201782430105903462218242409)
      ·
        refine ⟨151336822579427596663681807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201782430105903462218242409 151336822579427596663681807)
        ·
          refine ⟨227005233869141394995522711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151336822579427596663681807 227005233869141394995522711)
          ·
            refine ⟨340507850803712092493284067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227005233869141394995522711 340507850803712092493284067)
            ·
              refine ⟨510761776205568138739926101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340507850803712092493284067 510761776205568138739926101)
              ·
                refine ⟨5985489564909001625858509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 510761776205568138739926101 5985489564909001625858509)
                ·
                  refine ⟨2244558586840875609696941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5985489564909001625858509 2244558586840875609696941)
                  ·
                    refine ⟨841709470065328353636353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2244558586840875609696941 841709470065328353636353)
                    ·
                      rfl

theorem cell22_2458835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 3].length) (baseStart_2458835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458835 prefixEnd_2458835 := by exact prefixLift 2458835
  have htrace : WordTrace (prefixWord ++ tailWord_2458835) baseStart_2458835 baseEnd_2458835 := by
    simpa [prefixWord, tailWord_2458835, baseEnd_2458835] using wordTrace_append hprefix tailTrace_2458835
  have hstable : (prefixWord ++ tailWord_2458835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458835).length < 2 ^ (prefixWord ++ tailWord_2458835).sum := by decide
  have hdescent : baseEnd_2458835 < baseStart_2458835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458837 : List Nat := [1, 3, 2, 4, 1, 2, 3, 6]
def baseStart_2458837 : Nat := 118140960795 + 2458837 * 2 ^ 59
def prefixEnd_2458837 : Nat := 4983230072969 + 3 ^ 40 * 2458837 * 2
def baseEnd_2458837 : Nat := 93523350522911223898483

theorem tailTrace_2458837 : CollatzResearch.WordTrace tailWord_2458837 prefixEnd_2458837 93523350522911223898483 := by
  unfold tailWord_2458837
  simp only [CollatzResearch.WordTrace]
  refine ⟨89681152993060959771902765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59787435328707306514601843 89681152993060959771902765)
  ·
    refine ⟨33630432372397859914463537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89681152993060959771902765 33630432372397859914463537)
    ·
      refine ⟨25222824279298394935847653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33630432372397859914463537 25222824279298394935847653)
      ·
        refine ⟨4729279552368449050471435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25222824279298394935847653 4729279552368449050471435)
        ·
          refine ⟨7093919328552673575707153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4729279552368449050471435 7093919328552673575707153)
          ·
            refine ⟨5320439496414505181780365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7093919328552673575707153 5320439496414505181780365)
            ·
              refine ⟨1995164811155439443167637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5320439496414505181780365 1995164811155439443167637)
              ·
                refine ⟨93523350522911223898483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1995164811155439443167637 93523350522911223898483)
                ·
                  rfl

theorem cell22_2458837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 6].length) (baseStart_2458837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458837 prefixEnd_2458837 := by exact prefixLift 2458837
  have htrace : WordTrace (prefixWord ++ tailWord_2458837) baseStart_2458837 baseEnd_2458837 := by
    simpa [prefixWord, tailWord_2458837, baseEnd_2458837] using wordTrace_append hprefix tailTrace_2458837
  have hstable : (prefixWord ++ tailWord_2458837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458837).length < 2 ^ (prefixWord ++ tailWord_2458837).sum := by decide
  have hdescent : baseEnd_2458837 < baseStart_2458837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2458942 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_2458942 : Nat := 118140960795 + 2458942 * 2 ^ 59
def prefixEnd_2458942 : Nat := 4983230072969 + 3 ^ 40 * 2458942 * 2
def baseEnd_2458942 : Nat := 841746098352015741211025

theorem tailTrace_2458942 : CollatzResearch.WordTrace tailWord_2458942 prefixEnd_2458942 841746098352015741211025 := by
  unfold tailWord_2458942
  simp only [CollatzResearch.WordTrace]
  refine ⟨11210622832210070338059385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59789988438453708469650053 11210622832210070338059385)
  ·
    refine ⟨8407967124157552753544539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11210622832210070338059385 8407967124157552753544539)
    ·
      refine ⟨12611950686236329130316809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8407967124157552753544539 12611950686236329130316809)
      ·
        refine ⟨9458963014677246847737607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12611950686236329130316809 9458963014677246847737607)
        ·
          refine ⟨14188444522015870271606411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9458963014677246847737607 14188444522015870271606411)
          ·
            refine ⟨21282666783023805407409617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14188444522015870271606411 21282666783023805407409617)
            ·
              refine ⟨15962000087267854055557213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21282666783023805407409617 15962000087267854055557213)
              ·
                refine ⟨5985750032725445270833955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15962000087267854055557213 5985750032725445270833955)
                ·
                  refine ⟨8978625049088167906250933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5985750032725445270833955 8978625049088167906250933)
                  ·
                    refine ⟨841746098352015741211025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8978625049088167906250933 841746098352015741211025)
                    ·
                      rfl

theorem cell22_2458942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_2458942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2458942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2458942 prefixEnd_2458942 := by exact prefixLift 2458942
  have htrace : WordTrace (prefixWord ++ tailWord_2458942) baseStart_2458942 baseEnd_2458942 := by
    simpa [prefixWord, tailWord_2458942, baseEnd_2458942] using wordTrace_append hprefix tailTrace_2458942
  have hstable : (prefixWord ++ tailWord_2458942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2458942).length < 2 ^ (prefixWord ++ tailWord_2458942).sum := by decide
  have hdescent : baseEnd_2458942 < baseStart_2458942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2458942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459038 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_2459038 : Nat := 118140960795 + 2459038 * 2 ^ 59
def prefixEnd_2459038 : Nat := 4983230072969 + 3 ^ 40 * 2459038 * 2
def baseEnd_2459038 : Nat := 841778961113903490810731

theorem tailTrace_2459038 : CollatzResearch.WordTrace tailWord_2459038 prefixEnd_2459038 841778961113903490810731 := by
  unfold tailWord_2459038
  simp only [CollatzResearch.WordTrace]
  refine ⟨11211060508166596387496221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59792322710221847399979845 11211060508166596387496221)
  ·
    refine ⟨4204147690562473645311083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11211060508166596387496221 4204147690562473645311083)
    ·
      refine ⟨6306221535843710467966625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4204147690562473645311083 6306221535843710467966625)
      ·
        refine ⟨4729666151882782850974969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6306221535843710467966625 4729666151882782850974969)
        ·
          refine ⟨3547249613912087138231227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4729666151882782850974969 3547249613912087138231227)
          ·
            refine ⟨5320874420868130707346841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547249613912087138231227 5320874420868130707346841)
            ·
              refine ⟨3990655815651098030510131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5320874420868130707346841 3990655815651098030510131)
              ·
                refine ⟨5985983723476647045765197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3990655815651098030510131 5985983723476647045765197)
                ·
                  refine ⟨2244743896303742642161949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5985983723476647045765197 2244743896303742642161949)
                  ·
                    refine ⟨841778961113903490810731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2244743896303742642161949 841778961113903490810731)
                    ·
                      rfl

theorem cell22_2459038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_2459038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459038 prefixEnd_2459038 := by exact prefixLift 2459038
  have htrace : WordTrace (prefixWord ++ tailWord_2459038) baseStart_2459038 baseEnd_2459038 := by
    simpa [prefixWord, tailWord_2459038, baseEnd_2459038] using wordTrace_append hprefix tailTrace_2459038
  have hstable : (prefixWord ++ tailWord_2459038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459038).length < 2 ^ (prefixWord ++ tailWord_2459038).sum := by decide
  have hdescent : baseEnd_2459038 < baseStart_2459038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459107 : List Nat := [1, 1, 1, 6, 2, 1, 1, 9]
def baseStart_2459107 : Nat := 118140960795 + 2459107 * 2 ^ 59
def prefixEnd_2459107 : Nat := 4983230072969 + 3 ^ 40 * 2459107 * 2
def baseEnd_2459107 : Nat := 93533620136001145648391

theorem tailTrace_2459107 : CollatzResearch.WordTrace tailWord_2459107 prefixEnd_2459107 93533620136001145648391 := by
  unfold tailWord_2459107
  simp only [CollatzResearch.WordTrace]
  refine ⟨89691000702082795884231575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59794000468055197256154383 89691000702082795884231575)
  ·
    refine ⟨134536501053124193826347363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89691000702082795884231575 134536501053124193826347363)
    ·
      refine ⟨201804751579686290739521045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134536501053124193826347363 201804751579686290739521045)
      ·
        refine ⟨9459597730297794878415049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 201804751579686290739521045 9459597730297794878415049)
        ·
          refine ⟨7094698297723346158811287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9459597730297794878415049 7094698297723346158811287)
          ·
            refine ⟨10642047446585019238216931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7094698297723346158811287 10642047446585019238216931)
            ·
              refine ⟨15963071169877528857325397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10642047446585019238216931 15963071169877528857325397)
              ·
                refine ⟨93533620136001145648391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15963071169877528857325397 93533620136001145648391)
                ·
                  rfl

theorem cell22_2459107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 9].length) (baseStart_2459107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459107 prefixEnd_2459107 := by exact prefixLift 2459107
  have htrace : WordTrace (prefixWord ++ tailWord_2459107) baseStart_2459107 baseEnd_2459107 := by
    simpa [prefixWord, tailWord_2459107, baseEnd_2459107] using wordTrace_append hprefix tailTrace_2459107
  have hstable : (prefixWord ++ tailWord_2459107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459107).length < 2 ^ (prefixWord ++ tailWord_2459107).sum := by decide
  have hdescent : baseEnd_2459107 < baseStart_2459107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459111 : List Nat := [1, 1, 5, 2, 1, 3, 1, 3, 2, 3]
def baseStart_2459111 : Nat := 118140960795 + 2459111 * 2 ^ 59
def prefixEnd_2459111 : Nat := 4983230072969 + 3 ^ 40 * 2459111 * 2
def baseEnd_2459111 : Nat := 841803950505755633735507

theorem tailTrace_2459111 : CollatzResearch.WordTrace tailWord_2459111 prefixEnd_2459111 841803950505755633735507 := by
  unfold tailWord_2459111
  simp only [CollatzResearch.WordTrace]
  refine ⟨89691146594068304567377187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59794097729378869711584791 89691146594068304567377187)
  ·
    refine ⟨134536719891102456851065781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89691146594068304567377187 134536719891102456851065781)
    ·
      refine ⟨12612817489790855329787417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134536719891102456851065781 12612817489790855329787417)
      ·
        refine ⟨9459613117343141497340563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12612817489790855329787417 9459613117343141497340563)
        ·
          refine ⟨14189419676014712246010845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9459613117343141497340563 14189419676014712246010845)
          ·
            refine ⟨5321032378505517092254067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14189419676014712246010845 5321032378505517092254067)
            ·
              refine ⟨7981548567758275638381101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5321032378505517092254067 7981548567758275638381101)
              ·
                refine ⟨2993080712909353364392913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7981548567758275638381101 2993080712909353364392913)
                ·
                  refine ⟨2244810534682015023294685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2993080712909353364392913 2244810534682015023294685)
                  ·
                    refine ⟨841803950505755633735507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2244810534682015023294685 841803950505755633735507)
                    ·
                      rfl

theorem cell22_2459111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_2459111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459111 prefixEnd_2459111 := by exact prefixLift 2459111
  have htrace : WordTrace (prefixWord ++ tailWord_2459111) baseStart_2459111 baseEnd_2459111 := by
    simpa [prefixWord, tailWord_2459111, baseEnd_2459111] using wordTrace_append hprefix tailTrace_2459111
  have hstable : (prefixWord ++ tailWord_2459111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459111).length < 2 ^ (prefixWord ++ tailWord_2459111).sum := by decide
  have hdescent : baseEnd_2459111 < baseStart_2459111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459126 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_2459126 : Nat := 118140960795 + 2459126 * 2 ^ 59
def prefixEnd_2459126 : Nat := 4983230072969 + 3 ^ 40 * 2459126 * 2
def baseEnd_2459126 : Nat := 841809085312300594610461

theorem tailTrace_2459126 : CollatzResearch.WordTrace tailWord_2459126 prefixEnd_2459126 841809085312300594610461 := by
  unfold tailWord_2459126
  simp only [CollatzResearch.WordTrace]
  refine ⟨5605730855563372633073327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59794462459342641419448821 5605730855563372633073327)
  ·
    refine ⟨8408596283345058949609991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5605730855563372633073327 8408596283345058949609991)
    ·
      refine ⟨12612894425017588424414987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8408596283345058949609991 12612894425017588424414987)
      ·
        refine ⟨18919341637526382636622481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12612894425017588424414987 18919341637526382636622481)
        ·
          refine ⟨14189506228144786977466861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18919341637526382636622481 14189506228144786977466861)
          ·
            refine ⟨5321064835554295116550073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14189506228144786977466861 5321064835554295116550073)
            ·
              refine ⟨3990798626665721337412555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5321064835554295116550073 3990798626665721337412555)
              ·
                refine ⟨5986197939998582006118833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3990798626665721337412555 5986197939998582006118833)
                ·
                  refine ⟨4489648454998936504589125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5986197939998582006118833 4489648454998936504589125)
                  ·
                    refine ⟨841809085312300594610461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4489648454998936504589125 841809085312300594610461)
                    ·
                      rfl

theorem cell22_2459126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_2459126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459126 prefixEnd_2459126 := by exact prefixLift 2459126
  have htrace : WordTrace (prefixWord ++ tailWord_2459126) baseStart_2459126 baseEnd_2459126 := by
    simpa [prefixWord, tailWord_2459126, baseEnd_2459126] using wordTrace_append hprefix tailTrace_2459126
  have hstable : (prefixWord ++ tailWord_2459126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459126).length < 2 ^ (prefixWord ++ tailWord_2459126).sum := by decide
  have hdescent : baseEnd_2459126 < baseStart_2459126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459167 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 1, 7]
def baseStart_2459167 : Nat := 118140960795 + 2459167 * 2 ^ 59
def prefixEnd_2459167 : Nat := 4983230072969 + 3 ^ 40 * 2459167 * 2
def baseEnd_2459167 : Nat := 841823120450190154335335

theorem tailTrace_2459167 : CollatzResearch.WordTrace tailWord_2459167 prefixEnd_2459167 841823120450190154335335 := by
  unfold tailWord_2459167
  simp only [CollatzResearch.WordTrace]
  refine ⟨89693189081865426131415755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59795459387910284087610503 89693189081865426131415755)
  ·
    refine ⟨134539783622798139197123633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89693189081865426131415755 134539783622798139197123633)
    ·
      refine ⟨100904837717098604397842725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134539783622798139197123633 100904837717098604397842725)
      ·
        refine ⟨18919657071955988324595511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100904837717098604397842725 18919657071955988324595511)
        ·
          refine ⟨28379485607933982486893267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18919657071955988324595511 28379485607933982486893267)
          ·
            refine ⟨42569228411900973730339901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28379485607933982486893267 42569228411900973730339901)
            ·
              refine ⟨15963460654462865148877463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42569228411900973730339901 15963460654462865148877463)
              ·
                refine ⟨23945190981694297723316195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15963460654462865148877463 23945190981694297723316195)
                ·
                  refine ⟨35917786472541446584974293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23945190981694297723316195 35917786472541446584974293)
                  ·
                    refine ⟨841823120450190154335335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35917786472541446584974293 841823120450190154335335)
                    ·
                      rfl

theorem cell22_2459167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_2459167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459167 prefixEnd_2459167 := by exact prefixLift 2459167
  have htrace : WordTrace (prefixWord ++ tailWord_2459167) baseStart_2459167 baseEnd_2459167 := by
    simpa [prefixWord, tailWord_2459167, baseEnd_2459167] using wordTrace_append hprefix tailTrace_2459167
  have hstable : (prefixWord ++ tailWord_2459167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459167).length < 2 ^ (prefixWord ++ tailWord_2459167).sum := by decide
  have hdescent : baseEnd_2459167 < baseStart_2459167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459169 : List Nat := [1, 2, 3, 2, 2, 2, 2, 3, 5]
def baseStart_2459169 : Nat := 118140960795 + 2459169 * 2 ^ 59
def prefixEnd_2459169 : Nat := 4983230072969 + 3 ^ 40 * 2459169 * 2
def baseEnd_2459169 : Nat := 280607935030354271928443

theorem tailTrace_2459169 : CollatzResearch.WordTrace tailWord_2459169 prefixEnd_2459169 280607935030354271928443 := by
  unfold tailWord_2459169
  simp only [CollatzResearch.WordTrace]
  refine ⟨89693262027858180472988561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59795508018572120315325707 89693262027858180472988561)
  ·
    refine ⟨67269946520893635354741421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89693262027858180472988561 67269946520893635354741421)
    ·
      refine ⟨25226229945335113258028033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67269946520893635354741421 25226229945335113258028033)
      ·
        refine ⟨18919672459001334943521025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25226229945335113258028033 18919672459001334943521025)
        ·
          refine ⟨14189754344251001207640769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18919672459001334943521025 14189754344251001207640769)
          ·
            refine ⟨10642315758188250905730577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14189754344251001207640769 10642315758188250905730577)
            ·
              refine ⟨7981736818641188179297933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10642315758188250905730577 7981736818641188179297933)
              ·
                refine ⟨2993151306990445567236725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7981736818641188179297933 2993151306990445567236725)
                ·
                  refine ⟨280607935030354271928443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2993151306990445567236725 280607935030354271928443)
                  ·
                    rfl

theorem cell22_2459169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 5].length) (baseStart_2459169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459169 prefixEnd_2459169 := by exact prefixLift 2459169
  have htrace : WordTrace (prefixWord ++ tailWord_2459169) baseStart_2459169 baseEnd_2459169 := by
    simpa [prefixWord, tailWord_2459169, baseEnd_2459169] using wordTrace_append hprefix tailTrace_2459169
  have hstable : (prefixWord ++ tailWord_2459169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459169).length < 2 ^ (prefixWord ++ tailWord_2459169).sum := by decide
  have hdescent : baseEnd_2459169 < baseStart_2459169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459244 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_2459244 : Nat := 118140960795 + 2459244 * 2 ^ 59
def prefixEnd_2459244 : Nat := 4983230072969 + 3 ^ 40 * 2459244 * 2
def baseEnd_2459244 : Nat := 841849479123787620160099

theorem tailTrace_2459244 : CollatzResearch.WordTrace tailWord_2459244 prefixEnd_2459244 841849479123787620160099 := by
  unfold tailWord_2459244
  simp only [CollatzResearch.WordTrace]
  refine ⟨44847998751293234140984393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59797331668390978854645857 44847998751293234140984393)
  ·
    refine ⟨33635999063469925605738295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44847998751293234140984393 33635999063469925605738295)
    ·
      refine ⟨50453998595204888408607443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33635999063469925605738295 50453998595204888408607443)
      ·
        refine ⟨75680997892807332612911165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50453998595204888408607443 75680997892807332612911165)
        ·
          refine ⟨28380374209802749729841687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75680997892807332612911165 28380374209802749729841687)
          ·
            refine ⟨42570561314704124594762531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28380374209802749729841687 42570561314704124594762531)
            ·
              refine ⟨63855841972056186892143797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42570561314704124594762531 63855841972056186892143797)
              ·
                refine ⟨5986485184880267521138481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63855841972056186892143797 5986485184880267521138481)
                ·
                  refine ⟨4489863888660200640853861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5986485184880267521138481 4489863888660200640853861)
                  ·
                    refine ⟨841849479123787620160099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4489863888660200640853861 841849479123787620160099)
                    ·
                      rfl

theorem cell22_2459244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_2459244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459244 prefixEnd_2459244 := by exact prefixLift 2459244
  have htrace : WordTrace (prefixWord ++ tailWord_2459244) baseStart_2459244 baseEnd_2459244 := by
    simpa [prefixWord, tailWord_2459244, baseEnd_2459244] using wordTrace_append hprefix tailTrace_2459244
  have hstable : (prefixWord ++ tailWord_2459244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459244).length < 2 ^ (prefixWord ++ tailWord_2459244).sum := by decide
  have hdescent : baseEnd_2459244 < baseStart_2459244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459248 : List Nat := [2, 1, 1, 1, 6, 3, 1, 3, 4]
def baseStart_2459248 : Nat := 118140960795 + 2459248 * 2 ^ 59
def prefixEnd_2459248 : Nat := 4983230072969 + 3 ^ 40 * 2459248 * 2
def baseEnd_2459248 : Nat := 280616949468510981020029

theorem tailTrace_2459248 : CollatzResearch.WordTrace tailWord_2459248 prefixEnd_2459248 280616949468510981020029 := by
  unfold tailWord_2459248
  simp only [CollatzResearch.WordTrace]
  refine ⟨44848071697285988482557199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59797428929714651310076265 44848071697285988482557199)
  ·
    refine ⟨67272107545928982723835799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44848071697285988482557199 67272107545928982723835799)
    ·
      refine ⟨100908161318893474085753699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67272107545928982723835799 100908161318893474085753699)
      ·
        refine ⟨151362241978340211128630549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100908161318893474085753699 151362241978340211128630549)
        ·
          refine ⟨7095105092734697396654557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 151362241978340211128630549 7095105092734697396654557)
          ·
            refine ⟨2660664409775511523745459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7095105092734697396654557 2660664409775511523745459)
            ·
              refine ⟨3990996614663267285618189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2660664409775511523745459 3990996614663267285618189)
              ·
                refine ⟨1496623730498725232106821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3990996614663267285618189 1496623730498725232106821)
                ·
                  refine ⟨280616949468510981020029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1496623730498725232106821 280616949468510981020029)
                  ·
                    rfl

theorem cell22_2459248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 4].length) (baseStart_2459248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459248 prefixEnd_2459248 := by exact prefixLift 2459248
  have htrace : WordTrace (prefixWord ++ tailWord_2459248) baseStart_2459248 baseEnd_2459248 := by
    simpa [prefixWord, tailWord_2459248, baseEnd_2459248] using wordTrace_append hprefix tailTrace_2459248
  have hstable : (prefixWord ++ tailWord_2459248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459248).length < 2 ^ (prefixWord ++ tailWord_2459248).sum := by decide
  have hdescent : baseEnd_2459248 < baseStart_2459248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459261 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_2459261 : Nat := 118140960795 + 2459261 * 2 ^ 59
def prefixEnd_2459261 : Nat := 4983230072969 + 3 ^ 40 * 2459261 * 2
def baseEnd_2459261 : Nat := 841855298571205242485047

theorem tailTrace_2459261 : CollatzResearch.WordTrace tailWord_2459261 prefixEnd_2459261 841855298571205242485047 := by
  unfold tailWord_2459261
  simp only [CollatzResearch.WordTrace]
  refine ⟨89696617543524880185337637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59797745029016586790225091 89696617543524880185337637)
  ·
    refine ⟨16818115789410915034750807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89696617543524880185337637 16818115789410915034750807)
    ·
      refine ⟨25227173684116372552126211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16818115789410915034750807 25227173684116372552126211)
      ·
        refine ⟨37840760526174558828189317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25227173684116372552126211 37840760526174558828189317)
        ·
          refine ⟨7095142598657729780285497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37840760526174558828189317 7095142598657729780285497)
          ·
            refine ⟨5321356948993297335214123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7095142598657729780285497 5321356948993297335214123)
            ·
              refine ⟨7982035423489946002821185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5321356948993297335214123 7982035423489946002821185)
              ·
                refine ⟨5986526567617459502115889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7982035423489946002821185 5986526567617459502115889)
                ·
                  refine ⟨4489894925713094626586917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5986526567617459502115889 4489894925713094626586917)
                  ·
                    refine ⟨841855298571205242485047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4489894925713094626586917 841855298571205242485047)
                    ·
                      rfl

theorem cell22_2459261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_2459261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459261 prefixEnd_2459261 := by exact prefixLift 2459261
  have htrace : WordTrace (prefixWord ++ tailWord_2459261) baseStart_2459261 baseEnd_2459261 := by
    simpa [prefixWord, tailWord_2459261, baseEnd_2459261] using wordTrace_append hprefix tailTrace_2459261
  have hstable : (prefixWord ++ tailWord_2459261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459261).length < 2 ^ (prefixWord ++ tailWord_2459261).sum := by decide
  have hdescent : baseEnd_2459261 < baseStart_2459261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459351 : List Nat := [1, 1, 3, 2, 1, 3, 2, 4, 1, 4]
def baseStart_2459351 : Nat := 118140960795 + 2459351 * 2 ^ 59
def prefixEnd_2459351 : Nat := 4983230072969 + 3 ^ 40 * 2459351 * 2
def baseEnd_2459351 : Nat := 841886107410475007734771

theorem tailTrace_2459351 : CollatzResearch.WordTrace tailWord_2459351 prefixEnd_2459351 841886107410475007734771 := by
  unfold tailWord_2459351
  simp only [CollatzResearch.WordTrace]
  refine ⟨89699900113198825556113907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59799933408799217037409271 89699900113198825556113907)
  ·
    refine ⟨134549850169798238334170861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89699900113198825556113907 134549850169798238334170861)
    ·
      refine ⟨50456193813674339375314073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134549850169798238334170861 50456193813674339375314073)
      ·
        refine ⟨37842145360255754531485555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50456193813674339375314073 37842145360255754531485555)
        ·
          refine ⟨56763218040383631797228333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37842145360255754531485555 56763218040383631797228333)
          ·
            refine ⟨21286206765143861923960625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56763218040383631797228333 21286206765143861923960625)
            ·
              refine ⟨15964655073857896442970469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21286206765143861923960625 15964655073857896442970469)
              ·
                refine ⟨2993372826348355583056963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15964655073857896442970469 2993372826348355583056963)
                ·
                  refine ⟨4490059239522533374585445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993372826348355583056963 4490059239522533374585445)
                  ·
                    refine ⟨841886107410475007734771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4490059239522533374585445 841886107410475007734771)
                    ·
                      rfl

theorem cell22_2459351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_2459351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459351 prefixEnd_2459351 := by exact prefixLift 2459351
  have htrace : WordTrace (prefixWord ++ tailWord_2459351) baseStart_2459351 baseEnd_2459351 := by
    simpa [prefixWord, tailWord_2459351, baseEnd_2459351] using wordTrace_append hprefix tailTrace_2459351
  have hstable : (prefixWord ++ tailWord_2459351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459351).length < 2 ^ (prefixWord ++ tailWord_2459351).sum := by decide
  have hdescent : baseEnd_2459351 < baseStart_2459351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459368 : List Nat := [2, 1, 4, 1, 3, 2, 1, 3, 1, 4]
def baseStart_2459368 : Nat := 118140960795 + 2459368 * 2 ^ 59
def prefixEnd_2459368 : Nat := 4983230072969 + 3 ^ 40 * 2459368 * 2
def baseEnd_2459368 : Nat := 841891926857892630059719

theorem tailTrace_2459368 : CollatzResearch.WordTrace tailWord_2459368 prefixEnd_2459368 841891926857892630059719 := by
  unfold tailWord_2459368
  simp only [CollatzResearch.WordTrace]
  refine ⟨44850260077068618729741379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59800346769424824972988505 44850260077068618729741379)
  ·
    refine ⟨67275390115602928094612069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44850260077068618729741379 67275390115602928094612069)
    ·
      refine ⟨12614135646675549017739763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67275390115602928094612069 12614135646675549017739763)
      ·
        refine ⟨18921203470013323526609645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12614135646675549017739763 18921203470013323526609645)
        ·
          refine ⟨7095451301254996322478617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18921203470013323526609645 7095451301254996322478617)
          ·
            refine ⟨5321588475941247241858963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7095451301254996322478617 5321588475941247241858963)
            ·
              refine ⟨7982382713911870862788445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5321588475941247241858963 7982382713911870862788445)
              ·
                refine ⟨2993393517716951573545667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7982382713911870862788445 2993393517716951573545667)
                ·
                  refine ⟨4490090276575427360318501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2993393517716951573545667 4490090276575427360318501)
                  ·
                    refine ⟨841891926857892630059719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4490090276575427360318501 841891926857892630059719)
                    ·
                      rfl

theorem cell22_2459368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_2459368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459368 prefixEnd_2459368 := by exact prefixLift 2459368
  have htrace : WordTrace (prefixWord ++ tailWord_2459368) baseStart_2459368 baseEnd_2459368 := by
    simpa [prefixWord, tailWord_2459368, baseEnd_2459368] using wordTrace_append hprefix tailTrace_2459368
  have hstable : (prefixWord ++ tailWord_2459368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459368).length < 2 ^ (prefixWord ++ tailWord_2459368).sum := by decide
  have hdescent : baseEnd_2459368 < baseStart_2459368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459396 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_2459396 : Nat := 118140960795 + 2459396 * 2 ^ 59
def prefixEnd_2459396 : Nat := 4983230072969 + 3 ^ 40 * 2459396 * 2
def baseEnd_2459396 : Nat := 841901511830109890359633

theorem tailTrace_2459396 : CollatzResearch.WordTrace tailWord_2459396 prefixEnd_2459396 841901511830109890359633 := by
  unfold tailWord_2459396
  simp only [CollatzResearch.WordTrace]
  refine ⟨44850770699017899120751021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59801027598690532161001361 44850770699017899120751021)
  ·
    refine ⟨16819039012131712170281633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44850770699017899120751021 16819039012131712170281633)
    ·
      refine ⟨12614279259098784127711225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16819039012131712170281633 12614279259098784127711225)
      ·
        refine ⟨9460709444324088095783419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12614279259098784127711225 9460709444324088095783419)
        ·
          refine ⟨14191064166486132143675129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9460709444324088095783419 14191064166486132143675129)
          ·
            refine ⟨10643298124864599107756347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14191064166486132143675129 10643298124864599107756347)
            ·
              refine ⟨15964947187296898661634521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10643298124864599107756347 15964947187296898661634521)
              ·
                refine ⟨11973710390472673996225891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15964947187296898661634521 11973710390472673996225891)
                ·
                  refine ⟨17960565585709010994338837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11973710390472673996225891 17960565585709010994338837)
                  ·
                    refine ⟨841901511830109890359633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17960565585709010994338837 841901511830109890359633)
                    ·
                      rfl

theorem cell22_2459396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_2459396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459396 prefixEnd_2459396 := by exact prefixLift 2459396
  have htrace : WordTrace (prefixWord ++ tailWord_2459396) baseStart_2459396 baseEnd_2459396 := by
    simpa [prefixWord, tailWord_2459396, baseEnd_2459396] using wordTrace_append hprefix tailTrace_2459396
  have hstable : (prefixWord ++ tailWord_2459396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459396).length < 2 ^ (prefixWord ++ tailWord_2459396).sum := by decide
  have hdescent : baseEnd_2459396 < baseStart_2459396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459409 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 1, 9]
def baseStart_2459409 : Nat := 118140960795 + 2459409 * 2 ^ 59
def prefixEnd_2459409 : Nat := 4983230072969 + 3 ^ 40 * 2459409 * 2
def baseEnd_2459409 : Nat := 841905961995782189784593

theorem tailTrace_2459409 : CollatzResearch.WordTrace tailWord_2459409 prefixEnd_2459409 841905961995782189784593 := by
  unfold tailWord_2459409
  simp only [CollatzResearch.WordTrace]
  refine ⟨89702015546988701461725281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59801343697992467641150187 89702015546988701461725281)
  ·
    refine ⟨67276511660241526096293961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89702015546988701461725281 67276511660241526096293961)
    ·
      refine ⟨50457383745181144572220471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67276511660241526096293961 50457383745181144572220471)
      ·
        refine ⟨75686075617771716858330707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50457383745181144572220471 75686075617771716858330707)
        ·
          refine ⟨113529113426657575287496061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75686075617771716858330707 113529113426657575287496061)
          ·
            refine ⟨42573417534996590732811023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113529113426657575287496061 42573417534996590732811023)
            ·
              refine ⟨63860126302494886099216535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42573417534996590732811023 63860126302494886099216535)
              ·
                refine ⟨95790189453742329148824803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63860126302494886099216535 95790189453742329148824803)
                ·
                  refine ⟨143685284180613493723237205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95790189453742329148824803 143685284180613493723237205)
                  ·
                    refine ⟨841905961995782189784593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 143685284180613493723237205 841905961995782189784593)
                    ·
                      rfl

theorem cell22_2459409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_2459409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459409 prefixEnd_2459409 := by exact prefixLift 2459409
  have htrace : WordTrace (prefixWord ++ tailWord_2459409) baseStart_2459409 baseEnd_2459409 := by
    simpa [prefixWord, tailWord_2459409, baseEnd_2459409] using wordTrace_append hprefix tailTrace_2459409
  have hstable : (prefixWord ++ tailWord_2459409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459409).length < 2 ^ (prefixWord ++ tailWord_2459409).sum := by decide
  have hdescent : baseEnd_2459409 < baseStart_2459409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459449 : List Nat := [1, 2, 1, 7, 1, 2, 2, 1, 2, 3]
def baseStart_2459449 : Nat := 118140960795 + 2459449 * 2 ^ 59
def prefixEnd_2459449 : Nat := 4983230072969 + 3 ^ 40 * 2459449 * 2
def baseEnd_2459449 : Nat := 841919654813235418784471

theorem tailTrace_2459449 : CollatzResearch.WordTrace tailWord_2459449 prefixEnd_2459449 841919654813235418784471 := by
  unfold tailWord_2459449
  simp only [CollatzResearch.WordTrace]
  refine ⟨89703474466843788293181401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59802316311229192195454267 89703474466843788293181401)
  ·
    refine ⟨67277605850132841219886051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89703474466843788293181401 67277605850132841219886051)
    ·
      refine ⟨100916408775199261829829077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67277605850132841219886051 100916408775199261829829077)
      ·
        refine ⟨2365228330668732699136619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 100916408775199261829829077 2365228330668732699136619)
        ·
          refine ⟨3547842496003099048704929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365228330668732699136619 3547842496003099048704929)
          ·
            refine ⟨2660881872002324286528697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3547842496003099048704929 2660881872002324286528697)
            ·
              refine ⟨1995661404001743214896523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2660881872002324286528697 1995661404001743214896523)
              ·
                refine ⟨2993492106002614822344785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995661404001743214896523 2993492106002614822344785)
                ·
                  refine ⟨2245119079501961116758589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2993492106002614822344785 2245119079501961116758589)
                  ·
                    refine ⟨841919654813235418784471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2245119079501961116758589 841919654813235418784471)
                    ·
                      rfl

theorem cell22_2459449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 2, 3].length) (baseStart_2459449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459449 prefixEnd_2459449 := by exact prefixLift 2459449
  have htrace : WordTrace (prefixWord ++ tailWord_2459449) baseStart_2459449 baseEnd_2459449 := by
    simpa [prefixWord, tailWord_2459449, baseEnd_2459449] using wordTrace_append hprefix tailTrace_2459449
  have hstable : (prefixWord ++ tailWord_2459449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459449).length < 2 ^ (prefixWord ++ tailWord_2459449).sum := by decide
  have hdescent : baseEnd_2459449 < baseStart_2459449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459490 : List Nat := [3, 3, 2, 1, 2, 2, 2, 2, 5]
def baseStart_2459490 : Nat := 118140960795 + 2459490 * 2 ^ 59
def prefixEnd_2459490 : Nat := 4983230072969 + 3 ^ 40 * 2459490 * 2
def baseEnd_2459490 : Nat := 280644563317041659503115

theorem tailTrace_2459490 : CollatzResearch.WordTrace tailWord_2459490 prefixEnd_2459490 280644563317041659503115 := by
  unfold tailWord_2459490
  simp only [CollatzResearch.WordTrace]
  refine ⟨22426242464923813073855981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59803313239796834863615949 22426242464923813073855981)
  ·
    refine ⟨8409840924346429902695993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22426242464923813073855981 8409840924346429902695993)
    ·
      refine ⟨6307380693259822427021995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8409840924346429902695993 6307380693259822427021995)
      ·
        refine ⟨9461071039889733640532993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6307380693259822427021995 9461071039889733640532993)
        ·
          refine ⟨7095803279917300230399745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9461071039889733640532993 7095803279917300230399745)
          ·
            refine ⟨5321852459937975172799809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7095803279917300230399745 5321852459937975172799809)
            ·
              refine ⟨3991389344953481379599857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5321852459937975172799809 3991389344953481379599857)
              ·
                refine ⟨2993542008715111034699893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3991389344953481379599857 2993542008715111034699893)
                ·
                  refine ⟨280644563317041659503115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2993542008715111034699893 280644563317041659503115)
                  ·
                    rfl

theorem cell22_2459490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_2459490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459490 prefixEnd_2459490 := by exact prefixLift 2459490
  have htrace : WordTrace (prefixWord ++ tailWord_2459490) baseStart_2459490 baseEnd_2459490 := by
    simpa [prefixWord, tailWord_2459490, baseEnd_2459490] using wordTrace_append hprefix tailTrace_2459490
  have hstable : (prefixWord ++ tailWord_2459490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459490).length < 2 ^ (prefixWord ++ tailWord_2459490).sum := by decide
  have hdescent : baseEnd_2459490 < baseStart_2459490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459578 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 5, 3]
def baseStart_2459578 : Nat := 118140960795 + 2459578 * 2 ^ 59
def prefixEnd_2459578 : Nat := 4983230072969 + 3 ^ 40 * 2459578 * 2
def baseEnd_2459578 : Nat := 841963814149522082309075

theorem tailTrace_2459578 : CollatzResearch.WordTrace tailWord_2459578 prefixEnd_2459578 841963814149522082309075 := by
  unfold tailWord_2459578
  simp only [CollatzResearch.WordTrace]
  refine ⟨22427044870844110831156847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59805452988917628883084925 22427044870844110831156847)
  ·
    refine ⟨33640567306266166246735271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22427044870844110831156847 33640567306266166246735271)
    ·
      refine ⟨50460850959399249370102907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33640567306266166246735271 50460850959399249370102907)
      ·
        refine ⟨75691276439098874055154361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50460850959399249370102907 75691276439098874055154361)
        ·
          refine ⟨56768457329324155541365771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75691276439098874055154361 56768457329324155541365771)
          ·
            refine ⟨85152685993986233312048657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56768457329324155541365771 85152685993986233312048657)
            ·
              refine ⟨63864514495489674984036493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85152685993986233312048657 63864514495489674984036493)
              ·
                refine ⟨23949192935808628119013685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63864514495489674984036493 23949192935808628119013685)
                ·
                  refine ⟨2245236837732058886157533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23949192935808628119013685 2245236837732058886157533)
                  ·
                    refine ⟨841963814149522082309075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2245236837732058886157533 841963814149522082309075)
                    ·
                      rfl

theorem cell22_2459578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_2459578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459578 prefixEnd_2459578 := by exact prefixLift 2459578
  have htrace : WordTrace (prefixWord ++ tailWord_2459578) baseStart_2459578 baseEnd_2459578 := by
    simpa [prefixWord, tailWord_2459578, baseEnd_2459578] using wordTrace_append hprefix tailTrace_2459578
  have hstable : (prefixWord ++ tailWord_2459578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459578).length < 2 ^ (prefixWord ++ tailWord_2459578).sum := by decide
  have hdescent : baseEnd_2459578 < baseStart_2459578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459580 : List Nat := [2, 2, 2, 5, 1, 1, 1, 8]
def baseStart_2459580 : Nat := 118140960795 + 2459580 * 2 ^ 59
def prefixEnd_2459580 : Nat := 4983230072969 + 3 ^ 40 * 2459580 * 2
def baseEnd_2459580 : Nat := 93551610976710527084341

theorem tailTrace_2459580 : CollatzResearch.WordTrace tailWord_2459580 prefixEnd_2459580 93551610976710527084341 := by
  unfold tailWord_2459580
  simp only [CollatzResearch.WordTrace]
  refine ⟨44854126214684598833100097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59805501619579465110800129 44854126214684598833100097)
  ·
    refine ⟨33640594661013449124825073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44854126214684598833100097 33640594661013449124825073)
    ·
      refine ⟨25230445995760086843618805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33640594661013449124825073 25230445995760086843618805)
      ·
        refine ⟨2365354312102508141589263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25230445995760086843618805 2365354312102508141589263)
        ·
          refine ⟨3548031468153762212383895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365354312102508141589263 3548031468153762212383895)
          ·
            refine ⟨5322047202230643318575843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548031468153762212383895 5322047202230643318575843)
            ·
              refine ⟨7983070803345964977863765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5322047202230643318575843 7983070803345964977863765)
              ·
                refine ⟨93551610976710527084341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7983070803345964977863765 93551610976710527084341)
                ·
                  rfl

theorem cell22_2459580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 8].length) (baseStart_2459580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459580 prefixEnd_2459580 := by exact prefixLift 2459580
  have htrace : WordTrace (prefixWord ++ tailWord_2459580) baseStart_2459580 baseEnd_2459580 := by
    simpa [prefixWord, tailWord_2459580, baseEnd_2459580] using wordTrace_append hprefix tailTrace_2459580
  have hstable : (prefixWord ++ tailWord_2459580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459580).length < 2 ^ (prefixWord ++ tailWord_2459580).sum := by decide
  have hdescent : baseEnd_2459580 < baseStart_2459580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459608 : List Nat := [2, 1, 2, 2, 2, 2, 2, 4, 5]
def baseStart_2459608 : Nat := 118140960795 + 2459608 * 2 ^ 59
def prefixEnd_2459608 : Nat := 4983230072969 + 3 ^ 40 * 2459608 * 2
def baseEnd_2459608 : Nat := 280658027920870668019661

theorem tailTrace_2459608 : CollatzResearch.WordTrace tailWord_2459608 prefixEnd_2459608 280658027920870668019661 := by
  unfold tailWord_2459608
  simp only [CollatzResearch.WordTrace]
  refine ⟨44854636836633879224109739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59806182448845172298812985 44854636836633879224109739)
  ·
    refine ⟨67281955254950818836164609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44854636836633879224109739 67281955254950818836164609)
    ·
      refine ⟨50461466441213114127123457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67281955254950818836164609 50461466441213114127123457)
      ·
        refine ⟨37846099830909835595342593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50461466441213114127123457 37846099830909835595342593)
        ·
          refine ⟨28384574873182376696506945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37846099830909835595342593 28384574873182376696506945)
          ·
            refine ⟨21288431154886782522380209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28384574873182376696506945 21288431154886782522380209)
            ·
              refine ⟨15966323366165086891785157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21288431154886782522380209 15966323366165086891785157)
              ·
                refine ⟨2993685631155953792209717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15966323366165086891785157 2993685631155953792209717)
                ·
                  refine ⟨280658027920870668019661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2993685631155953792209717 280658027920870668019661)
                  ·
                    rfl

theorem cell22_2459608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 5].length) (baseStart_2459608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459608 prefixEnd_2459608 := by exact prefixLift 2459608
  have htrace : WordTrace (prefixWord ++ tailWord_2459608) baseStart_2459608 baseEnd_2459608 := by
    simpa [prefixWord, tailWord_2459608, baseEnd_2459608] using wordTrace_append hprefix tailTrace_2459608
  have hstable : (prefixWord ++ tailWord_2459608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459608).length < 2 ^ (prefixWord ++ tailWord_2459608).sum := by decide
  have hdescent : baseEnd_2459608 < baseStart_2459608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459618 : List Nat := [3, 3, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2459618 : Nat := 118140960795 + 2459618 * 2 ^ 59
def prefixEnd_2459618 : Nat := 4983230072969 + 3 ^ 40 * 2459618 * 2
def baseEnd_2459618 : Nat := 841977506966975311308953

theorem tailTrace_2459618 : CollatzResearch.WordTrace tailWord_2459618 prefixEnd_2459618 841977506966975311308953 := by
  unfold tailWord_2459618
  simp only [CollatzResearch.WordTrace]
  refine ⟨22427409600807882539020877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59806425602154353437389005 22427409600807882539020877)
  ·
    refine ⟨8410278600302955952132829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22427409600807882539020877 8410278600302955952132829)
    ·
      refine ⟨3153854475113608482049811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8410278600302955952132829 3153854475113608482049811)
      ·
        refine ⟨4730781712670412723074717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3153854475113608482049811 4730781712670412723074717)
        ·
          refine ⟨1774043142251404771153019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4730781712670412723074717 1774043142251404771153019)
          ·
            refine ⟨2661064713377107156729529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774043142251404771153019 2661064713377107156729529)
            ·
              refine ⟨1995798535032830367547147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2661064713377107156729529 1995798535032830367547147)
              ·
                refine ⟨2993697802549245551320721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995798535032830367547147 2993697802549245551320721)
                ·
                  refine ⟨2245273351911934163490541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2993697802549245551320721 2245273351911934163490541)
                  ·
                    refine ⟨841977506966975311308953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2245273351911934163490541 841977506966975311308953)
                    ·
                      rfl

theorem cell22_2459618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2459618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459618 prefixEnd_2459618 := by exact prefixLift 2459618
  have htrace : WordTrace (prefixWord ++ tailWord_2459618) baseStart_2459618 baseEnd_2459618 := by
    simpa [prefixWord, tailWord_2459618, baseEnd_2459618] using wordTrace_append hprefix tailTrace_2459618
  have hstable : (prefixWord ++ tailWord_2459618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459618).length < 2 ^ (prefixWord ++ tailWord_2459618).sum := by decide
  have hdescent : baseEnd_2459618 < baseStart_2459618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459683 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 1, 6]
def baseStart_2459683 : Nat := 118140960795 + 2459683 * 2 ^ 59
def prefixEnd_2459683 : Nat := 4983230072969 + 3 ^ 40 * 2459683 * 2
def baseEnd_2459683 : Nat := 841999757795336808433753

theorem tailTrace_2459683 : CollatzResearch.WordTrace tailWord_2459683 prefixEnd_2459683 841999757795336808433753 := by
  unfold tailWord_2459683
  simp only [CollatzResearch.WordTrace]
  refine ⟨89712009147996046257199703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59808006098664030838133135 89712009147996046257199703)
  ·
    refine ⟨134568013721994069385799555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89712009147996046257199703 134568013721994069385799555)
    ·
      refine ⟨201852020582991104078699333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134568013721994069385799555 201852020582991104078699333)
      ·
        refine ⟨37847253859310832014756125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201852020582991104078699333 37847253859310832014756125)
        ·
          refine ⟨14192720197241562005533547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37847253859310832014756125 14192720197241562005533547)
          ·
            refine ⟨21289080295862343008300321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14192720197241562005533547 21289080295862343008300321)
            ·
              refine ⟨15966810221896757256225241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21289080295862343008300321 15966810221896757256225241)
              ·
                refine ⟨11975107666422567942168931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15966810221896757256225241 11975107666422567942168931)
                ·
                  refine ⟨17962661499633851913253397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11975107666422567942168931 17962661499633851913253397)
                  ·
                    refine ⟨841999757795336808433753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17962661499633851913253397 841999757795336808433753)
                    ·
                      rfl

theorem cell22_2459683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 6].length) (baseStart_2459683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459683 prefixEnd_2459683 := by exact prefixLift 2459683
  have htrace : WordTrace (prefixWord ++ tailWord_2459683) baseStart_2459683 baseEnd_2459683 := by
    simpa [prefixWord, tailWord_2459683, baseEnd_2459683] using wordTrace_append hprefix tailTrace_2459683
  have hstable : (prefixWord ++ tailWord_2459683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459683).length < 2 ^ (prefixWord ++ tailWord_2459683).sum := by decide
  have hdescent : baseEnd_2459683 < baseStart_2459683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459685 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 1, 5]
def baseStart_2459685 : Nat := 118140960795 + 2459685 * 2 ^ 59
def prefixEnd_2459685 : Nat := 4983230072969 + 3 ^ 40 * 2459685 * 2
def baseEnd_2459685 : Nat := 842000442436209469883747

theorem tailTrace_2459685 : CollatzResearch.WordTrace tailWord_2459685 prefixEnd_2459685 842000442436209469883747 := by
  unfold tailWord_2459685
  simp only [CollatzResearch.WordTrace]
  refine ⟨89712082093988800598772509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59808054729325867065848339 89712082093988800598772509)
  ·
    refine ⟨33642030785245800224539691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89712082093988800598772509 33642030785245800224539691)
    ·
      refine ⟨50463046177868700336809537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33642030785245800224539691 50463046177868700336809537)
      ·
        refine ⟨37847284633401525252607153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50463046177868700336809537 37847284633401525252607153)
        ·
          refine ⟨28385463475051143939455365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37847284633401525252607153 28385463475051143939455365)
          ·
            refine ⟨5322274401572089488647881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28385463475051143939455365 5322274401572089488647881)
            ·
              refine ⟨3991705801179067116485911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5322274401572089488647881 3991705801179067116485911)
              ·
                refine ⟨5987558701768600674728867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3991705801179067116485911 5987558701768600674728867)
                ·
                  refine ⟨8981338052652901012093301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5987558701768600674728867 8981338052652901012093301)
                  ·
                    refine ⟨842000442436209469883747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8981338052652901012093301 842000442436209469883747)
                    ·
                      rfl

theorem cell22_2459685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_2459685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459685 prefixEnd_2459685 := by exact prefixLift 2459685
  have htrace : WordTrace (prefixWord ++ tailWord_2459685) baseStart_2459685 baseEnd_2459685 := by
    simpa [prefixWord, tailWord_2459685, baseEnd_2459685] using wordTrace_append hprefix tailTrace_2459685
  have hstable : (prefixWord ++ tailWord_2459685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459685).length < 2 ^ (prefixWord ++ tailWord_2459685).sum := by decide
  have hdescent : baseEnd_2459685 < baseStart_2459685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459687 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 6]
def baseStart_2459687 : Nat := 118140960795 + 2459687 * 2 ^ 59
def prefixEnd_2459687 : Nat := 4983230072969 + 3 ^ 40 * 2459687 * 2
def baseEnd_2459687 : Nat := 280667042359027377111247

theorem tailTrace_2459687 : CollatzResearch.WordTrace tailWord_2459687 prefixEnd_2459687 280667042359027377111247 := by
  unfold tailWord_2459687
  simp only [CollatzResearch.WordTrace]
  refine ⟨89712155039981554940345315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59808103359987703293563543 89712155039981554940345315)
  ·
    refine ⟨134568232559972332410517973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89712155039981554940345315 134568232559972332410517973)
    ·
      refine ⟨3153942950624351540871515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 134568232559972332410517973 3153942950624351540871515)
      ·
        refine ⟨4730914425936527311307273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3153942950624351540871515 4730914425936527311307273)
        ·
          refine ⟨3548185819452395483480455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4730914425936527311307273 3548185819452395483480455)
          ·
            refine ⟨5322278729178593225220683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548185819452395483480455 5322278729178593225220683)
            ·
              refine ⟨7983418093767889837831025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5322278729178593225220683 7983418093767889837831025)
              ·
                refine ⟨5987563570325917378373269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7983418093767889837831025 5987563570325917378373269)
                ·
                  refine ⟨280667042359027377111247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5987563570325917378373269 280667042359027377111247)
                  ·
                    rfl

theorem cell22_2459687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 6].length) (baseStart_2459687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459687 prefixEnd_2459687 := by exact prefixLift 2459687
  have htrace : WordTrace (prefixWord ++ tailWord_2459687) baseStart_2459687 baseEnd_2459687 := by
    simpa [prefixWord, tailWord_2459687, baseEnd_2459687] using wordTrace_append hprefix tailTrace_2459687
  have hstable : (prefixWord ++ tailWord_2459687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459687).length < 2 ^ (prefixWord ++ tailWord_2459687).sum := by decide
  have hdescent : baseEnd_2459687 < baseStart_2459687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459702 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_2459702 : Nat := 118140960795 + 2459702 * 2 ^ 59
def prefixEnd_2459702 : Nat := 4983230072969 + 3 ^ 40 * 2459702 * 2
def baseEnd_2459702 : Nat := 842006261883627092208695

theorem tailTrace_2459702 : CollatzResearch.WordTrace tailWord_2459702 prefixEnd_2459702 842006261883627092208695 := by
  unfold tailWord_2459702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5607043883432950781383835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59808468089951475001427573 5607043883432950781383835)
  ·
    refine ⟨8410565825149426172075753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5607043883432950781383835 8410565825149426172075753)
    ·
      refine ⟨6307924368862069629056815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8410565825149426172075753 6307924368862069629056815)
      ·
        refine ⟨9461886553293104443585223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6307924368862069629056815 9461886553293104443585223)
        ·
          refine ⟨14192829829939656665377835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9461886553293104443585223 14192829829939656665377835)
          ·
            refine ⟨21289244744909484998066753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14192829829939656665377835 21289244744909484998066753)
            ·
              refine ⟨15966933558682113748550065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21289244744909484998066753 15966933558682113748550065)
              ·
                refine ⟨11975200169011585311412549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15966933558682113748550065 11975200169011585311412549)
                ·
                  refine ⟨2245350031689672245889853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11975200169011585311412549 2245350031689672245889853)
                  ·
                    refine ⟨842006261883627092208695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2245350031689672245889853 842006261883627092208695)
                    ·
                      rfl

theorem cell22_2459702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_2459702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459702 prefixEnd_2459702 := by exact prefixLift 2459702
  have htrace : WordTrace (prefixWord ++ tailWord_2459702) baseStart_2459702 baseEnd_2459702 := by
    simpa [prefixWord, tailWord_2459702, baseEnd_2459702] using wordTrace_append hprefix tailTrace_2459702
  have hstable : (prefixWord ++ tailWord_2459702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459702).length < 2 ^ (prefixWord ++ tailWord_2459702).sum := by decide
  have hdescent : baseEnd_2459702 < baseStart_2459702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459781 : List Nat := [1, 3, 1, 1, 5, 2, 3, 2, 1, 3]
def baseStart_2459781 : Nat := 118140960795 + 2459781 * 2 ^ 59
def prefixEnd_2459781 : Nat := 4983230072969 + 3 ^ 40 * 2459781 * 2
def baseEnd_2459781 : Nat := 842033305198097219483453

theorem tailTrace_2459781 : CollatzResearch.WordTrace tailWord_2459781 prefixEnd_2459781 842033305198097219483453 := by
  unfold tailWord_2459781
  simp only [CollatzResearch.WordTrace]
  refine ⟨89715583501641008994267197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59810389001094005996178131 89715583501641008994267197)
  ·
    refine ⟨33643343813115378372850199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89715583501641008994267197 33643343813115378372850199)
    ·
      refine ⟨50465015719673067559275299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33643343813115378372850199 50465015719673067559275299)
      ·
        refine ⟨75697523579509601338912949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50465015719673067559275299 75697523579509601338912949)
        ·
          refine ⟨7096642835579025125523089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75697523579509601338912949 7096642835579025125523089)
          ·
            refine ⟨5322482126684268844142317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7096642835579025125523089 5322482126684268844142317)
            ·
              refine ⟨1995930797506600816553369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5322482126684268844142317 1995930797506600816553369)
              ·
                refine ⟨1496948098129950612415027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1995930797506600816553369 1496948098129950612415027)
                ·
                  refine ⟨2245422147194925918622541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1496948098129950612415027 2245422147194925918622541)
                  ·
                    refine ⟨842033305198097219483453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2245422147194925918622541 842033305198097219483453)
                    ·
                      rfl

theorem cell22_2459781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_2459781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459781 prefixEnd_2459781 := by exact prefixLift 2459781
  have htrace : WordTrace (prefixWord ++ tailWord_2459781) baseStart_2459781 baseEnd_2459781 := by
    simpa [prefixWord, tailWord_2459781, baseEnd_2459781] using wordTrace_append hprefix tailTrace_2459781
  have hstable : (prefixWord ++ tailWord_2459781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459781).length < 2 ^ (prefixWord ++ tailWord_2459781).sum := by decide
  have hdescent : baseEnd_2459781 < baseStart_2459781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459807 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 3, 4]
def baseStart_2459807 : Nat := 118140960795 + 2459807 * 2 ^ 59
def prefixEnd_2459807 : Nat := 4983230072969 + 3 ^ 40 * 2459807 * 2
def baseEnd_2459807 : Nat := 842042205529441818333373

theorem tailTrace_2459807 : CollatzResearch.WordTrace tailWord_2459807 prefixEnd_2459807 842042205529441818333373 := by
  unfold tailWord_2459807
  simp only [CollatzResearch.WordTrace]
  refine ⟨89716531799546815434713675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59811021199697876956475783 89716531799546815434713675)
  ·
    refine ⟨134574797699320223152070513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89716531799546815434713675 134574797699320223152070513)
    ·
      refine ⟨100931098274490167364052885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134574797699320223152070513 100931098274490167364052885)
      ·
        refine ⟨4731145231616726595189979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100931098274490167364052885 4731145231616726595189979)
        ·
          refine ⟨7096717847425089892784969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4731145231616726595189979 7096717847425089892784969)
          ·
            refine ⟨5322538385568817419588727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7096717847425089892784969 5322538385568817419588727)
            ·
              refine ⟨7983807578353226129383091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5322538385568817419588727 7983807578353226129383091)
              ·
                refine ⟨11975711367529839194074637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7983807578353226129383091 11975711367529839194074637)
                ·
                  refine ⟨4490891762823689697777989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11975711367529839194074637 4490891762823689697777989)
                  ·
                    refine ⟨842042205529441818333373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4490891762823689697777989 842042205529441818333373)
                    ·
                      rfl

theorem cell22_2459807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_2459807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459807 prefixEnd_2459807 := by exact prefixLift 2459807
  have htrace : WordTrace (prefixWord ++ tailWord_2459807) baseStart_2459807 baseEnd_2459807 := by
    simpa [prefixWord, tailWord_2459807, baseEnd_2459807] using wordTrace_append hprefix tailTrace_2459807
  have hstable : (prefixWord ++ tailWord_2459807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459807).length < 2 ^ (prefixWord ++ tailWord_2459807).sum := by decide
  have hdescent : baseEnd_2459807 < baseStart_2459807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459828 : List Nat := [2, 5, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2459828 : Nat := 118140960795 + 2459828 * 2 ^ 59
def prefixEnd_2459828 : Nat := 4983230072969 + 3 ^ 40 * 2459828 * 2
def baseEnd_2459828 : Nat := 280683131419534921186103

theorem tailTrace_2459828 : CollatzResearch.WordTrace tailWord_2459828 prefixEnd_2459828 280683131419534921186103 := by
  unfold tailWord_2459828
  simp only [CollatzResearch.WordTrace]
  refine ⟨44858648866235368010614069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59811531821647157347485425 44858648866235368010614069)
  ·
    refine ⟨4205498331209565750995069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44858648866235368010614069 4205498331209565750995069)
    ·
      refine ⟨1577061874203587156623151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4205498331209565750995069 1577061874203587156623151)
      ·
        refine ⟨2365592811305380734934727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577061874203587156623151 2365592811305380734934727)
        ·
          refine ⟨3548389216958071102402091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365592811305380734934727 3548389216958071102402091)
          ·
            refine ⟨5322583825437106653603137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548389216958071102402091 5322583825437106653603137)
            ·
              refine ⟨3991937869077829990202353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5322583825437106653603137 3991937869077829990202353)
              ·
                refine ⟨2993953401808372492651765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3991937869077829990202353 2993953401808372492651765)
                ·
                  refine ⟨280683131419534921186103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2993953401808372492651765 280683131419534921186103)
                  ·
                    rfl

theorem cell22_2459828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2459828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459828 prefixEnd_2459828 := by exact prefixLift 2459828
  have htrace : WordTrace (prefixWord ++ tailWord_2459828) baseStart_2459828 baseEnd_2459828 := by
    simpa [prefixWord, tailWord_2459828, baseEnd_2459828] using wordTrace_append hprefix tailTrace_2459828
  have hstable : (prefixWord ++ tailWord_2459828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459828).length < 2 ^ (prefixWord ++ tailWord_2459828).sum := by decide
  have hdescent : baseEnd_2459828 < baseStart_2459828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459835 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 2, 4]
def baseStart_2459835 : Nat := 118140960795 + 2459835 * 2 ^ 59
def prefixEnd_2459835 : Nat := 4983230072969 + 3 ^ 40 * 2459835 * 2
def baseEnd_2459835 : Nat := 842051790501659078633287

theorem tailTrace_2459835 : CollatzResearch.WordTrace tailWord_2459835 prefixEnd_2459835 842051790501659078633287 := by
  unfold tailWord_2459835
  simp only [CollatzResearch.WordTrace]
  refine ⟨89717553043445376216732959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59811702028963584144488639 89717553043445376216732959)
  ·
    refine ⟨134576329565168064325099439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89717553043445376216732959 134576329565168064325099439)
    ·
      refine ⟨201864494347752096487649159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134576329565168064325099439 201864494347752096487649159)
      ·
        refine ⟨302796741521628144731473739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201864494347752096487649159 302796741521628144731473739)
        ·
          refine ⟨454195112282442217097210609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302796741521628144731473739 454195112282442217097210609)
          ·
            refine ⟨340646334211831662822907957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454195112282442217097210609 340646334211831662822907957)
            ·
              refine ⟨31935593832359218389647621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 340646334211831662822907957 31935593832359218389647621)
              ·
                refine ⟨5987923843567353448058929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31935593832359218389647621 5987923843567353448058929)
                ·
                  refine ⟨4490942882675515086044197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5987923843567353448058929 4490942882675515086044197)
                  ·
                    refine ⟨842051790501659078633287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4490942882675515086044197 842051790501659078633287)
                    ·
                      rfl

theorem cell22_2459835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 4].length) (baseStart_2459835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459835 prefixEnd_2459835 := by exact prefixLift 2459835
  have htrace : WordTrace (prefixWord ++ tailWord_2459835) baseStart_2459835 baseEnd_2459835 := by
    simpa [prefixWord, tailWord_2459835, baseEnd_2459835] using wordTrace_append hprefix tailTrace_2459835
  have hstable : (prefixWord ++ tailWord_2459835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459835).length < 2 ^ (prefixWord ++ tailWord_2459835).sum := by decide
  have hdescent : baseEnd_2459835 < baseStart_2459835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459854 : List Nat := [4, 1, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_2459854 : Nat := 118140960795 + 2459854 * 2 ^ 59
def prefixEnd_2459854 : Nat := 4983230072969 + 3 ^ 40 * 2459854 * 2
def baseEnd_2459854 : Nat := 842058294589949362408229

theorem tailTrace_2459854 : CollatzResearch.WordTrace tailWord_2459854 prefixEnd_2459854 842058294589949362408229 := by
  unfold tailWord_2459854
  simp only [CollatzResearch.WordTrace]
  refine ⟨11214780753797067807709327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59812164020251028307783077 11214780753797067807709327)
  ·
    refine ⟨16822171130695601711563991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11214780753797067807709327 16822171130695601711563991)
    ·
      refine ⟨25233256696043402567345987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16822171130695601711563991 25233256696043402567345987)
      ·
        refine ⟨37849885044065103851018981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25233256696043402567345987 37849885044065103851018981)
        ·
          refine ⟨7096853445762206972066059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37849885044065103851018981 7096853445762206972066059)
          ·
            refine ⟨10645280168643310458099089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7096853445762206972066059 10645280168643310458099089)
            ·
              refine ⟨7983960126482482843574317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10645280168643310458099089 7983960126482482843574317)
              ·
                refine ⟨2993985047430931066340369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7983960126482482843574317 2993985047430931066340369)
                ·
                  refine ⟨2245488785573198299755277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2993985047430931066340369 2245488785573198299755277)
                  ·
                    refine ⟨842058294589949362408229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2245488785573198299755277 842058294589949362408229)
                    ·
                      rfl

theorem cell22_2459854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_2459854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459854 prefixEnd_2459854 := by exact prefixLift 2459854
  have htrace : WordTrace (prefixWord ++ tailWord_2459854) baseStart_2459854 baseEnd_2459854 := by
    simpa [prefixWord, tailWord_2459854, baseEnd_2459854] using wordTrace_append hprefix tailTrace_2459854
  have hstable : (prefixWord ++ tailWord_2459854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459854).length < 2 ^ (prefixWord ++ tailWord_2459854).sum := by decide
  have hdescent : baseEnd_2459854 < baseStart_2459854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459869 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_2459869 : Nat := 118140960795 + 2459869 * 2 ^ 59
def prefixEnd_2459869 : Nat := 4983230072969 + 3 ^ 40 * 2459869 * 2
def baseEnd_2459869 : Nat := 842063429396494323283183

theorem tailTrace_2459869 : CollatzResearch.WordTrace tailWord_2459869 prefixEnd_2459869 842063429396494323283183 := by
  unfold tailWord_2459869
  simp only [CollatzResearch.WordTrace]
  refine ⟨89718793125322200023470661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59812528750214800015647107 89718793125322200023470661)
  ·
    refine ⟨16822273710997912504400749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89718793125322200023470661 16822273710997912504400749)
    ·
      refine ⟨6308352641624217189150281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16822273710997912504400749 6308352641624217189150281)
      ·
        refine ⟨4731264481218162891862711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6308352641624217189150281 4731264481218162891862711)
        ·
          refine ⟨7096896721827244337794067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4731264481218162891862711 7096896721827244337794067)
          ·
            refine ⟨10645345082740866506691101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7096896721827244337794067 10645345082740866506691101)
            ·
              refine ⟨3992004406027824940009163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10645345082740866506691101 3992004406027824940009163)
              ·
                refine ⟨5988006609041737410013745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3992004406027824940009163 5988006609041737410013745)
                ·
                  refine ⟨4491004956781303057510309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5988006609041737410013745 4491004956781303057510309)
                  ·
                    refine ⟨842063429396494323283183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4491004956781303057510309 842063429396494323283183)
                    ·
                      rfl

theorem cell22_2459869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_2459869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459869 prefixEnd_2459869 := by exact prefixLift 2459869
  have htrace : WordTrace (prefixWord ++ tailWord_2459869) baseStart_2459869 baseEnd_2459869 := by
    simpa [prefixWord, tailWord_2459869, baseEnd_2459869] using wordTrace_append hprefix tailTrace_2459869
  have hstable : (prefixWord ++ tailWord_2459869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459869).length < 2 ^ (prefixWord ++ tailWord_2459869).sum := by decide
  have hdescent : baseEnd_2459869 < baseStart_2459869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459882 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 5, 3]
def baseStart_2459882 : Nat := 118140960795 + 2459882 * 2 ^ 59
def prefixEnd_2459882 : Nat := 4983230072969 + 3 ^ 40 * 2459882 * 2
def baseEnd_2459882 : Nat := 842067879562166622708143

theorem tailTrace_2459882 : CollatzResearch.WordTrace tailWord_2459882 prefixEnd_2459882 842067879562166622708143 := by
  unfold tailWord_2459882
  simp only [CollatzResearch.WordTrace]
  refine ⟨22429816818568775810923475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59812844849516735495795933 22429816818568775810923475)
  ·
    refine ⟨33644725227853163716385213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22429816818568775810923475 33644725227853163716385213)
    ·
      refine ⟨12616771960444936393644455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33644725227853163716385213 12616771960444936393644455)
      ·
        refine ⟨18925157940667404590466683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12616771960444936393644455 18925157940667404590466683)
        ·
          refine ⟨28387736911001106885700025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18925157940667404590466683 28387736911001106885700025)
          ·
            refine ⟨21290802683250830164275019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28387736911001106885700025 21290802683250830164275019)
            ·
              refine ⟨31936204024876245246412529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21290802683250830164275019 31936204024876245246412529)
              ·
                refine ⟨23952153018657183934809397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31936204024876245246412529 23952153018657183934809397)
                ·
                  refine ⟨2245514345499110993888381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23952153018657183934809397 2245514345499110993888381)
                  ·
                    refine ⟨842067879562166622708143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2245514345499110993888381 842067879562166622708143)
                    ·
                      rfl

theorem cell22_2459882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_2459882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459882 prefixEnd_2459882 := by exact prefixLift 2459882
  have htrace : WordTrace (prefixWord ++ tailWord_2459882) baseStart_2459882 baseEnd_2459882 := by
    simpa [prefixWord, tailWord_2459882, baseEnd_2459882] using wordTrace_append hprefix tailTrace_2459882
  have hstable : (prefixWord ++ tailWord_2459882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459882).length < 2 ^ (prefixWord ++ tailWord_2459882).sum := by decide
  have hdescent : baseEnd_2459882 < baseStart_2459882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459950 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 3, 3]
def baseStart_2459950 : Nat := 118140960795 + 2459950 * 2 ^ 59
def prefixEnd_2459950 : Nat := 4983230072969 + 3 ^ 40 * 2459950 * 2
def baseEnd_2459950 : Nat := 842091157351837112007935

theorem tailTrace_2459950 : CollatzResearch.WordTrace tailWord_2459950 prefixEnd_2459950 842091157351837112007935 := by
  unfold tailWord_2459950
  simp only [CollatzResearch.WordTrace]
  refine ⟨11215218429753593857146163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59814498292019167238112869 11215218429753593857146163)
  ·
    refine ⟨16822827644630390785719245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11215218429753593857146163 16822827644630390785719245)
    ·
      refine ⟨6308560366736396544644717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16822827644630390785719245 6308560366736396544644717)
      ·
        refine ⟨2365710137526148704241769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6308560366736396544644717 2365710137526148704241769)
        ·
          refine ⟨1774282603144611528181327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2365710137526148704241769 1774282603144611528181327)
          ·
            refine ⟨2661423904716917292271991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774282603144611528181327 2661423904716917292271991)
            ·
              refine ⟨3992135857075375938407987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2661423904716917292271991 3992135857075375938407987)
              ·
                refine ⟨5988203785613063907611981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3992135857075375938407987 5988203785613063907611981)
                ·
                  refine ⟨2245576419604898965354493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5988203785613063907611981 2245576419604898965354493)
                  ·
                    refine ⟨842091157351837112007935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2245576419604898965354493 842091157351837112007935)
                    ·
                      rfl

theorem cell22_2459950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_2459950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459950 prefixEnd_2459950 := by exact prefixLift 2459950
  have htrace : WordTrace (prefixWord ++ tailWord_2459950) baseStart_2459950 baseEnd_2459950 := by
    simpa [prefixWord, tailWord_2459950, baseEnd_2459950] using wordTrace_append hprefix tailTrace_2459950
  have hstable : (prefixWord ++ tailWord_2459950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459950).length < 2 ^ (prefixWord ++ tailWord_2459950).sum := by decide
  have hdescent : baseEnd_2459950 < baseStart_2459950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2459989 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 1, 5]
def baseStart_2459989 : Nat := 118140960795 + 2459989 * 2 ^ 59
def prefixEnd_2459989 : Nat := 4983230072969 + 3 ^ 40 * 2459989 * 2
def baseEnd_2459989 : Nat := 842104507848854010282815

theorem tailTrace_2459989 : CollatzResearch.WordTrace tailWord_2459989 prefixEnd_2459989 842104507848854010282815 := by
  unfold tailWord_2459989
  simp only [CollatzResearch.WordTrace]
  refine ⟨89723169884887460517839021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59815446589924973678559347 89723169884887460517839021)
  ·
    refine ⟨33646188706832797694189633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89723169884887460517839021 33646188706832797694189633)
    ·
      refine ⟨25234641530124598270642225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33646188706832797694189633 25234641530124598270642225)
      ·
        refine ⟨18925981147593448702981669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25234641530124598270642225 18925981147593448702981669)
        ·
          refine ⟨3548621465173771631809063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18925981147593448702981669 3548621465173771631809063)
          ·
            refine ⟨5322932197760657447713595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548621465173771631809063 5322932197760657447713595)
            ·
              refine ⟨7984398296640986171570393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5322932197760657447713595 7984398296640986171570393)
              ·
                refine ⟨5988298722480739628677795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7984398296640986171570393 5988298722480739628677795)
                ·
                  refine ⟨8982448083721109443016693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5988298722480739628677795 8982448083721109443016693)
                  ·
                    refine ⟨842104507848854010282815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8982448083721109443016693 842104507848854010282815)
                    ·
                      rfl

theorem cell22_2459989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_2459989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2459989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2459989 prefixEnd_2459989 := by exact prefixLift 2459989
  have htrace : WordTrace (prefixWord ++ tailWord_2459989) baseStart_2459989 baseEnd_2459989 := by
    simpa [prefixWord, tailWord_2459989, baseEnd_2459989] using wordTrace_append hprefix tailTrace_2459989
  have hstable : (prefixWord ++ tailWord_2459989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2459989).length < 2 ^ (prefixWord ++ tailWord_2459989).sum := by decide
  have hdescent : baseEnd_2459989 < baseStart_2459989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2459989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460002 : List Nat := [3, 3, 2, 1, 1, 12]
def baseStart_2460002 : Nat := 118140960795 + 2460002 * 2 ^ 59
def prefixEnd_2460002 : Nat := 4983230072969 + 3 ^ 40 * 2460002 * 2
def baseEnd_2460002 : Nat := 10396406889068226045775

theorem tailTrace_2460002 : CollatzResearch.WordTrace tailWord_2460002 prefixEnd_2460002 10396406889068226045775 := by
  unfold tailWord_2460002
  simp only [CollatzResearch.WordTrace]
  refine ⟨22430911008460090934515565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59815762689226909158708173 22430911008460090934515565)
  ·
    refine ⟨8411591628172534100443337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22430911008460090934515565 8411591628172534100443337)
    ·
      refine ⟨6308693721129400575332503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8411591628172534100443337 6308693721129400575332503)
      ·
        refine ⟨9463040581694100862998755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6308693721129400575332503 9463040581694100862998755)
        ·
          refine ⟨14194560872541151294498133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9463040581694100862998755 14194560872541151294498133)
          ·
            refine ⟨10396406889068226045775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14194560872541151294498133 10396406889068226045775)
            ·
              rfl

theorem cell22_2460002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 12].length) (baseStart_2460002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460002 prefixEnd_2460002 := by exact prefixLift 2460002
  have htrace : WordTrace (prefixWord ++ tailWord_2460002) baseStart_2460002 baseEnd_2460002 := by
    simpa [prefixWord, tailWord_2460002, baseEnd_2460002] using wordTrace_append hprefix tailTrace_2460002
  have hstable : (prefixWord ++ tailWord_2460002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460002).length < 2 ^ (prefixWord ++ tailWord_2460002).sum := by decide
  have hdescent : baseEnd_2460002 < baseStart_2460002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460008 : List Nat := [2, 1, 4, 2, 2, 3, 2, 2, 4]
def baseStart_2460008 : Nat := 118140960795 + 2460008 * 2 ^ 59
def prefixEnd_2460008 : Nat := 4983230072969 + 3 ^ 40 * 2460008 * 2
def baseEnd_2460008 : Nat := 280703670645714764685919

theorem tailTrace_2460008 : CollatzResearch.WordTrace tailWord_2460008 prefixEnd_2460008 280703670645714764685919 := by
  unfold tailWord_2460008
  simp only [CollatzResearch.WordTrace]
  refine ⟨44861931435909313381390339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59815908581212417841853785 44861931435909313381390339)
  ·
    refine ⟨67292897153863970072085509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44861931435909313381390339 67292897153863970072085509)
    ·
      refine ⟨12617418216349494388516033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67292897153863970072085509 12617418216349494388516033)
      ·
        refine ⟨9463063662262120791387025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12617418216349494388516033 9463063662262120791387025)
        ·
          refine ⟨7097297746696590593540269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9463063662262120791387025 7097297746696590593540269)
          ·
            refine ⟨2661486655011221472577601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7097297746696590593540269 2661486655011221472577601)
            ·
              refine ⟨1996114991258416104433201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2661486655011221472577601 1996114991258416104433201)
              ·
                refine ⟨1497086243443812078324901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1996114991258416104433201 1497086243443812078324901)
                ·
                  refine ⟨280703670645714764685919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1497086243443812078324901 280703670645714764685919)
                  ·
                    rfl

theorem cell22_2460008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 4].length) (baseStart_2460008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460008 prefixEnd_2460008 := by exact prefixLift 2460008
  have htrace : WordTrace (prefixWord ++ tailWord_2460008) baseStart_2460008 baseEnd_2460008 := by
    simpa [prefixWord, tailWord_2460008, baseEnd_2460008] using wordTrace_append hprefix tailTrace_2460008
  have hstable : (prefixWord ++ tailWord_2460008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460008).length < 2 ^ (prefixWord ++ tailWord_2460008).sum := by decide
  have hdescent : baseEnd_2460008 < baseStart_2460008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460064 : List Nat := [2, 1, 1, 4, 1, 3, 3, 2, 5]
def baseStart_2460064 : Nat := 118140960795 + 2460064 * 2 ^ 59
def prefixEnd_2460064 : Nat := 4983230072969 + 3 ^ 40 * 2460064 * 2
def baseEnd_2460064 : Nat := 280710060627192938219195

theorem tailTrace_2460064 : CollatzResearch.WordTrace tailWord_2460064 prefixEnd_2460064 280710060627192938219195 := by
  unfold tailWord_2460064
  simp only [CollatzResearch.WordTrace]
  refine ⟨44862952679807874163409623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59817270239743832217879497 44862952679807874163409623)
  ·
    refine ⟨67294429019711811245114435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44862952679807874163409623 67294429019711811245114435)
    ·
      refine ⟨100941643529567716867671653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67294429019711811245114435 100941643529567716867671653)
      ·
        refine ⟨18926558161793946912688435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100941643529567716867671653 18926558161793946912688435)
        ·
          refine ⟨28389837242690920369032653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18926558161793946912688435 28389837242690920369032653)
          ·
            refine ⟨10646188966009095138387245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28389837242690920369032653 10646188966009095138387245)
            ·
              refine ⟨3992320862253410676895217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10646188966009095138387245 3992320862253410676895217)
              ·
                refine ⟨2994240646690058007671413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3992320862253410676895217 2994240646690058007671413)
                ·
                  refine ⟨280710060627192938219195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2994240646690058007671413 280710060627192938219195)
                  ·
                    rfl

theorem cell22_2460064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 5].length) (baseStart_2460064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460064 prefixEnd_2460064 := by exact prefixLift 2460064
  have htrace : WordTrace (prefixWord ++ tailWord_2460064) baseStart_2460064 baseEnd_2460064 := by
    simpa [prefixWord, tailWord_2460064, baseEnd_2460064] using wordTrace_append hprefix tailTrace_2460064
  have hstable : (prefixWord ++ tailWord_2460064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460064).length < 2 ^ (prefixWord ++ tailWord_2460064).sum := by decide
  have hdescent : baseEnd_2460064 < baseStart_2460064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460081 : List Nat := [1, 2, 2, 4, 1, 3, 3, 1, 5]
def baseStart_2460081 : Nat := 118140960795 + 2460081 * 2 ^ 59
def prefixEnd_2460081 : Nat := 4983230072969 + 3 ^ 40 * 2460081 * 2
def baseEnd_2460081 : Nat := 280712000442998812327511

theorem tailTrace_2460081 : CollatzResearch.WordTrace tailWord_2460081 prefixEnd_2460081 280712000442998812327511 := by
  unfold tailWord_2460081
  simp only [CollatzResearch.WordTrace]
  refine ⟨89726525400554160230188097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59817683600369440153458731 89726525400554160230188097)
  ·
    refine ⟨67294894050415620172641073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89726525400554160230188097 67294894050415620172641073)
    ·
      refine ⟨50471170537811715129480805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67294894050415620172641073 50471170537811715129480805)
      ·
        refine ⟨9463344475839696586777651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50471170537811715129480805 9463344475839696586777651)
        ·
          refine ⟨14195016713759544880166477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9463344475839696586777651 14195016713759544880166477)
          ·
            refine ⟨5323131267659829330062429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14195016713759544880166477 5323131267659829330062429)
            ·
              refine ⟨1996174225372435998773411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5323131267659829330062429 1996174225372435998773411)
              ·
                refine ⟨2994261338058653998160117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1996174225372435998773411 2994261338058653998160117)
                ·
                  refine ⟨280712000442998812327511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2994261338058653998160117 280712000442998812327511)
                  ·
                    rfl

theorem cell22_2460081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 5].length) (baseStart_2460081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460081 prefixEnd_2460081 := by exact prefixLift 2460081
  have htrace : WordTrace (prefixWord ++ tailWord_2460081) baseStart_2460081 baseEnd_2460081 := by
    simpa [prefixWord, tailWord_2460081, baseEnd_2460081] using wordTrace_append hprefix tailTrace_2460081
  have hstable : (prefixWord ++ tailWord_2460081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460081).length < 2 ^ (prefixWord ++ tailWord_2460081).sum := by decide
  have hdescent : baseEnd_2460081 < baseStart_2460081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460094 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_2460094 : Nat := 118140960795 + 2460094 * 2 ^ 59
def prefixEnd_2460094 : Nat := 4983230072969 + 3 ^ 40 * 2460094 * 2
def baseEnd_2460094 : Nat := 842140451494668736407493

theorem tailTrace_2460094 : CollatzResearch.WordTrace tailWord_2460094 prefixEnd_2460094 842140451494668736407493 := by
  unfold tailWord_2460094
  simp only [CollatzResearch.WordTrace]
  refine ⟨11215874943688382931301417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59817999699671375633607557 11215874943688382931301417)
  ·
    refine ⟨8411906207766287198476063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11215874943688382931301417 8411906207766287198476063)
    ·
      refine ⟨12617859311649430797714095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8411906207766287198476063 12617859311649430797714095)
      ·
        refine ⟨18926788967474146196571143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12617859311649430797714095 18926788967474146196571143)
        ·
          refine ⟨28390183451211219294856715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18926788967474146196571143 28390183451211219294856715)
          ·
            refine ⟨42585275176816828942285073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28390183451211219294856715 42585275176816828942285073)
            ·
              refine ⟨31938956382612621706713805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42585275176816828942285073 31938956382612621706713805)
              ·
                refine ⟨11977108643479733140017677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31938956382612621706713805 11977108643479733140017677)
                ·
                  refine ⟨4491415741304899927506629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11977108643479733140017677 4491415741304899927506629)
                  ·
                    refine ⟨842140451494668736407493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4491415741304899927506629 842140451494668736407493)
                    ·
                      rfl

theorem cell22_2460094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_2460094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460094 prefixEnd_2460094 := by exact prefixLift 2460094
  have htrace : WordTrace (prefixWord ++ tailWord_2460094) baseStart_2460094 baseEnd_2460094 := by
    simpa [prefixWord, tailWord_2460094, baseEnd_2460094] using wordTrace_append hprefix tailTrace_2460094
  have hstable : (prefixWord ++ tailWord_2460094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460094).length < 2 ^ (prefixWord ++ tailWord_2460094).sum := by decide
  have hdescent : baseEnd_2460094 < baseStart_2460094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460107 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 3, 5]
def baseStart_2460107 : Nat := 118140960795 + 2460107 * 2 ^ 59
def prefixEnd_2460107 : Nat := 4983230072969 + 3 ^ 40 * 2460107 * 2
def baseEnd_2460107 : Nat := 842144901660341035832453

theorem tailTrace_2460107 : CollatzResearch.WordTrace tailWord_2460107 prefixEnd_2460107 842144901660341035832453 := by
  unfold tailWord_2460107
  simp only [CollatzResearch.WordTrace]
  refine ⟨89727473698459966670634575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59818315798973311113756383 89727473698459966670634575)
  ·
    refine ⟨134591210547689950005951863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89727473698459966670634575 134591210547689950005951863)
    ·
      refine ⟨201886815821534925008927795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134591210547689950005951863 201886815821534925008927795)
      ·
        refine ⟨302830223732302387513391693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201886815821534925008927795 302830223732302387513391693)
        ·
          refine ⟨113561333899613395317521885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302830223732302387513391693 113561333899613395317521885)
          ·
            refine ⟨42585500212355023244070707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113561333899613395317521885 42585500212355023244070707)
            ·
              refine ⟨63878250318532534866106061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42585500212355023244070707 63878250318532534866106061)
              ·
                refine ⟨23954343869449700574789773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63878250318532534866106061 23954343869449700574789773)
                ·
                  refine ⟨8982878951043637715546165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23954343869449700574789773 8982878951043637715546165)
                  ·
                    refine ⟨842144901660341035832453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8982878951043637715546165 842144901660341035832453)
                    ·
                      rfl

theorem cell22_2460107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 5].length) (baseStart_2460107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460107 prefixEnd_2460107 := by exact prefixLift 2460107
  have htrace : WordTrace (prefixWord ++ tailWord_2460107) baseStart_2460107 baseEnd_2460107 := by
    simpa [prefixWord, tailWord_2460107, baseEnd_2460107] using wordTrace_append hprefix tailTrace_2460107
  have hstable : (prefixWord ++ tailWord_2460107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460107).length < 2 ^ (prefixWord ++ tailWord_2460107).sum := by decide
  have hdescent : baseEnd_2460107 < baseStart_2460107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460169 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 7, 3]
def baseStart_2460169 : Nat := 118140960795 + 2460169 * 2 ^ 59
def prefixEnd_2460169 : Nat := 4983230072969 + 3 ^ 40 * 2460169 * 2
def baseEnd_2460169 : Nat := 842166125527393540782263

theorem tailTrace_2460169 : CollatzResearch.WordTrace tailWord_2460169 prefixEnd_2460169 842166125527393540782263 := by
  unfold tailWord_2460169
  simp only [CollatzResearch.WordTrace]
  refine ⟨89729735024235351259391561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59819823349490234172927707 89729735024235351259391561)
  ·
    refine ⟨67297301268176513444543671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89729735024235351259391561 67297301268176513444543671)
    ·
      refine ⟨100945951902264770166815507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67297301268176513444543671 100945951902264770166815507)
      ·
        refine ⟨151418927853397155250223261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100945951902264770166815507 151418927853397155250223261)
        ·
          refine ⟨56782097945023933218833723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151418927853397155250223261 56782097945023933218833723)
          ·
            refine ⟨85173146917535899828250585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56782097945023933218833723 85173146917535899828250585)
            ·
              refine ⟨63879860188151924871187939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85173146917535899828250585 63879860188151924871187939)
              ·
                refine ⟨95819790282227887306781909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63879860188151924871187939 95819790282227887306781909)
                ·
                  refine ⟨2245776334739716108752701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 95819790282227887306781909 2245776334739716108752701)
                  ·
                    refine ⟨842166125527393540782263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2245776334739716108752701 842166125527393540782263)
                    ·
                      rfl

theorem cell22_2460169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 3].length) (baseStart_2460169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460169 prefixEnd_2460169 := by exact prefixLift 2460169
  have htrace : WordTrace (prefixWord ++ tailWord_2460169) baseStart_2460169 baseEnd_2460169 := by
    simpa [prefixWord, tailWord_2460169, baseEnd_2460169] using wordTrace_append hprefix tailTrace_2460169
  have hstable : (prefixWord ++ tailWord_2460169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460169).length < 2 ^ (prefixWord ++ tailWord_2460169).sum := by decide
  have hdescent : baseEnd_2460169 < baseStart_2460169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460184 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 2, 6]
def baseStart_2460184 : Nat := 118140960795 + 2460184 * 2 ^ 59
def prefixEnd_2460184 : Nat := 4983230072969 + 3 ^ 40 * 2460184 * 2
def baseEnd_2460184 : Nat := 842171260333938501657217

theorem tailTrace_2460184 : CollatzResearch.WordTrace tailWord_2460184 prefixEnd_2460184 842171260333938501657217 := by
  unfold tailWord_2460184
  simp only [CollatzResearch.WordTrace]
  refine ⟨44865141059590504410593803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59820188079454005880791737 44865141059590504410593803)
  ·
    refine ⟨67297711589385756615890705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44865141059590504410593803 67297711589385756615890705)
    ·
      refine ⟨50473283692039317461918029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67297711589385756615890705 50473283692039317461918029)
      ·
        refine ⟨18927481384514744048219261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50473283692039317461918029 18927481384514744048219261)
        ·
          refine ⟨7097805519193029018082223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18927481384514744048219261 7097805519193029018082223)
          ·
            refine ⟨10646708278789543527123335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7097805519193029018082223 10646708278789543527123335)
            ·
              refine ⟨15970062418184315290685003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10646708278789543527123335 15970062418184315290685003)
              ·
                refine ⟨23955093627276472936027505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15970062418184315290685003 23955093627276472936027505)
                ·
                  refine ⟨17966320220457354702020629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23955093627276472936027505 17966320220457354702020629)
                  ·
                    refine ⟨842171260333938501657217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17966320220457354702020629 842171260333938501657217)
                    ·
                      rfl

theorem cell22_2460184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_2460184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460184 prefixEnd_2460184 := by exact prefixLift 2460184
  have htrace : WordTrace (prefixWord ++ tailWord_2460184) baseStart_2460184 baseEnd_2460184 := by
    simpa [prefixWord, tailWord_2460184, baseEnd_2460184] using wordTrace_append hprefix tailTrace_2460184
  have hstable : (prefixWord ++ tailWord_2460184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460184).length < 2 ^ (prefixWord ++ tailWord_2460184).sum := by decide
  have hdescent : baseEnd_2460184 < baseStart_2460184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460220 : List Nat := [2, 2, 2, 2, 3, 2, 2, 3, 1, 3]
def baseStart_2460220 : Nat := 118140960795 + 2460220 * 2 ^ 59
def prefixEnd_2460220 : Nat := 4983230072969 + 3 ^ 40 * 2460220 * 2
def baseEnd_2460220 : Nat := 842183583869646407757107

theorem tailTrace_2460220 : CollatzResearch.WordTrace tailWord_2460220 prefixEnd_2460220 842183583869646407757107 := by
  unfold tailWord_2460220
  simp only [CollatzResearch.WordTrace]
  refine ⟨44865797573525293484749057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59821063431367057979665409 44865797573525293484749057)
  ·
    refine ⟨33649348180143970113561793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44865797573525293484749057 33649348180143970113561793)
    ·
      refine ⟨25237011135107977585171345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33649348180143970113561793 25237011135107977585171345)
      ·
        refine ⟨18927758351330983188878509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25237011135107977585171345 18927758351330983188878509)
        ·
          refine ⟨7097909381749118695829441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18927758351330983188878509 7097909381749118695829441)
          ·
            refine ⟨5323432036311839021872081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7097909381749118695829441 5323432036311839021872081)
            ·
              refine ⟨3992574027233879266404061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5323432036311839021872081 3992574027233879266404061)
              ·
                refine ⟨1497215260212704724901523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3992574027233879266404061 1497215260212704724901523)
                ·
                  refine ⟨2245822890319057087352285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1497215260212704724901523 2245822890319057087352285)
                  ·
                    refine ⟨842183583869646407757107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2245822890319057087352285 842183583869646407757107)
                    ·
                      rfl

theorem cell22_2460220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_2460220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460220 prefixEnd_2460220 := by exact prefixLift 2460220
  have htrace : WordTrace (prefixWord ++ tailWord_2460220) baseStart_2460220 baseEnd_2460220 := by
    simpa [prefixWord, tailWord_2460220, baseEnd_2460220] using wordTrace_append hprefix tailTrace_2460220
  have hstable : (prefixWord ++ tailWord_2460220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460220).length < 2 ^ (prefixWord ++ tailWord_2460220).sum := by decide
  have hdescent : baseEnd_2460220 < baseStart_2460220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460306 : List Nat := [3, 2, 3, 1, 2, 1, 1, 9]
def baseStart_2460306 : Nat := 118140960795 + 2460306 * 2 ^ 59
def prefixEnd_2460306 : Nat := 4983230072969 + 3 ^ 40 * 2460306 * 2
def baseEnd_2460306 : Nat := 93579224825241205567427

theorem tailTrace_2460306 : CollatzResearch.WordTrace tailWord_2460306 prefixEnd_2460306 93579224825241205567427 := by
  unfold tailWord_2460306
  simp only [CollatzResearch.WordTrace]
  refine ⟨22433682956184755914282193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59823154549826015771419181 22433682956184755914282193)
  ·
    refine ⟨16825262217138566935711645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22433682956184755914282193 16825262217138566935711645)
    ·
      refine ⟨6309473331426962600891867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16825262217138566935711645 6309473331426962600891867)
      ·
        refine ⟨9464209997140443901337801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6309473331426962600891867 9464209997140443901337801)
        ·
          refine ⟨7098157497855332926003351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9464209997140443901337801 7098157497855332926003351)
          ·
            refine ⟨10647236246782999389005027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7098157497855332926003351 10647236246782999389005027)
            ·
              refine ⟨15970854370174499083507541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10647236246782999389005027 15970854370174499083507541)
              ·
                refine ⟨93579224825241205567427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15970854370174499083507541 93579224825241205567427)
                ·
                  rfl

theorem cell22_2460306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_2460306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460306 prefixEnd_2460306 := by exact prefixLift 2460306
  have htrace : WordTrace (prefixWord ++ tailWord_2460306) baseStart_2460306 baseEnd_2460306 := by
    simpa [prefixWord, tailWord_2460306, baseEnd_2460306] using wordTrace_append hprefix tailTrace_2460306
  have hstable : (prefixWord ++ tailWord_2460306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460306).length < 2 ^ (prefixWord ++ tailWord_2460306).sum := by decide
  have hdescent : baseEnd_2460306 < baseStart_2460306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460351 : List Nat := [1, 1, 2, 2, 2, 4, 1, 4, 5]
def baseStart_2460351 : Nat := 118140960795 + 2460351 * 2 ^ 59
def prefixEnd_2460351 : Nat := 4983230072969 + 3 ^ 40 * 2460351 * 2
def baseEnd_2460351 : Nat := 280742809282268577577235

theorem tailTrace_2460351 : CollatzResearch.WordTrace tailWord_2460351 prefixEnd_2460351 280742809282268577577235 := by
  unfold tailWord_2460351
  simp only [CollatzResearch.WordTrace]
  refine ⟨89736373109575996342516907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59824248739717330895011271 89736373109575996342516907)
  ·
    refine ⟨134604559664363994513775361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89736373109575996342516907 134604559664363994513775361)
    ·
      refine ⟨100953419748272995885331521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134604559664363994513775361 100953419748272995885331521)
      ·
        refine ⟨75715064811204746913998641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100953419748272995885331521 75715064811204746913998641)
        ·
          refine ⟨56786298608403560185498981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75715064811204746913998641 56786298608403560185498981)
          ·
            refine ⟨10647430989075667534781059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56786298608403560185498981 10647430989075667534781059)
            ·
              refine ⟨15971146483613501302171589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10647430989075667534781059 15971146483613501302171589)
              ·
                refine ⟨2994589965677531494157173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15971146483613501302171589 2994589965677531494157173)
                ·
                  refine ⟨280742809282268577577235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2994589965677531494157173 280742809282268577577235)
                  ·
                    rfl

theorem cell22_2460351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 5].length) (baseStart_2460351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460351 prefixEnd_2460351 := by exact prefixLift 2460351
  have htrace : WordTrace (prefixWord ++ tailWord_2460351) baseStart_2460351 baseEnd_2460351 := by
    simpa [prefixWord, tailWord_2460351, baseEnd_2460351] using wordTrace_append hprefix tailTrace_2460351
  have hstable : (prefixWord ++ tailWord_2460351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460351).length < 2 ^ (prefixWord ++ tailWord_2460351).sum := by decide
  have hdescent : baseEnd_2460351 < baseStart_2460351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460366 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_2460366 : Nat := 118140960795 + 2460366 * 2 ^ 59
def prefixEnd_2460366 : Nat := 4983230072969 + 3 ^ 40 * 2460366 * 2
def baseEnd_2460366 : Nat := 842233562653350693606659

theorem tailTrace_2460366 : CollatzResearch.WordTrace tailWord_2460366 prefixEnd_2460366 842233562653350693606659 := by
  unfold tailWord_2460366
  simp only [CollatzResearch.WordTrace]
  refine ⟨11217115025565206738039119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59824613469681102602875301 11217115025565206738039119)
  ·
    refine ⟨16825672538347810107058679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11217115025565206738039119 16825672538347810107058679)
    ·
      refine ⟨25238508807521715160588019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16825672538347810107058679 25238508807521715160588019)
      ·
        refine ⟨37857763211282572740882029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25238508807521715160588019 37857763211282572740882029)
        ·
          refine ⟨14196661204230964777830761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37857763211282572740882029 14196661204230964777830761)
          ·
            refine ⟨10647495903173223583373071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14196661204230964777830761 10647495903173223583373071)
            ·
              refine ⟨15971243854759835375059607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10647495903173223583373071 15971243854759835375059607)
              ·
                refine ⟨23956865782139753062589411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15971243854759835375059607 23956865782139753062589411)
                ·
                  refine ⟨35935298673209629593884117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23956865782139753062589411 35935298673209629593884117)
                  ·
                    refine ⟨842233562653350693606659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35935298673209629593884117 842233562653350693606659)
                    ·
                      rfl

theorem cell22_2460366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_2460366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460366 prefixEnd_2460366 := by exact prefixLift 2460366
  have htrace : WordTrace (prefixWord ++ tailWord_2460366) baseStart_2460366 baseEnd_2460366 := by
    simpa [prefixWord, tailWord_2460366, baseEnd_2460366] using wordTrace_append hprefix tailTrace_2460366
  have hstable : (prefixWord ++ tailWord_2460366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460366).length < 2 ^ (prefixWord ++ tailWord_2460366).sum := by decide
  have hdescent : baseEnd_2460366 < baseStart_2460366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460413 : List Nat := [1, 4, 1, 1, 1, 1, 3, 6, 4]
def baseStart_2460413 : Nat := 118140960795 + 2460413 * 2 ^ 59
def prefixEnd_2460413 : Nat := 4983230072969 + 3 ^ 40 * 2460413 * 2
def baseEnd_2460413 : Nat := 280749883904619412560505

theorem tailTrace_2460413 : CollatzResearch.WordTrace tailWord_2460413 prefixEnd_2460413 280749883904619412560505 := by
  unfold tailWord_2460413
  simp only [CollatzResearch.WordTrace]
  refine ⟨89738634435351380931273893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59825756290234253954182595 89738634435351380931273893)
  ·
    refine ⟨16825993956628383924613855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89738634435351380931273893 16825993956628383924613855)
    ·
      refine ⟨25238990934942575886920783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16825993956628383924613855 25238990934942575886920783)
      ·
        refine ⟨37858486402413863830381175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25238990934942575886920783 37858486402413863830381175)
        ·
          refine ⟨56787729603620795745571763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37858486402413863830381175 56787729603620795745571763)
          ·
            refine ⟨85181594405431193618357645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56787729603620795745571763 85181594405431193618357645)
            ·
              refine ⟨31943097902036697606884117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85181594405431193618357645 31943097902036697606884117)
              ·
                refine ⟨1497332714157970200322693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31943097902036697606884117 1497332714157970200322693)
                ·
                  refine ⟨280749883904619412560505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1497332714157970200322693 280749883904619412560505)
                  ·
                    rfl

theorem cell22_2460413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_2460413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460413 prefixEnd_2460413 := by exact prefixLift 2460413
  have htrace : WordTrace (prefixWord ++ tailWord_2460413) baseStart_2460413 baseEnd_2460413 := by
    simpa [prefixWord, tailWord_2460413, baseEnd_2460413] using wordTrace_append hprefix tailTrace_2460413
  have hstable : (prefixWord ++ tailWord_2460413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460413).length < 2 ^ (prefixWord ++ tailWord_2460413).sum := by decide
  have hdescent : baseEnd_2460413 < baseStart_2460413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460426 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_2460426 : Nat := 118140960795 + 2460426 * 2 ^ 59
def prefixEnd_2460426 : Nat := 4983230072969 + 3 ^ 40 * 2460426 * 2
def baseEnd_2460426 : Nat := 842254101879530537106475

theorem tailTrace_2460426 : CollatzResearch.WordTrace tailWord_2460426 prefixEnd_2460426 842254101879530537106475 := by
  unfold tailWord_2460426
  simp only [CollatzResearch.WordTrace]
  refine ⟨22434777146076071037874283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59826072389536189434331421 22434777146076071037874283)
  ·
    refine ⟨33652165719114106556811425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22434777146076071037874283 33652165719114106556811425)
    ·
      refine ⟨25239124289335579917608569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33652165719114106556811425 25239124289335579917608569)
      ·
        refine ⟨18929343217001684938206427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25239124289335579917608569 18929343217001684938206427)
        ·
          refine ⟨28394014825502527407309641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18929343217001684938206427 28394014825502527407309641)
          ·
            refine ⟨21295511119126895555482231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28394014825502527407309641 21295511119126895555482231)
            ·
              refine ⟨31943266678690343333223347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21295511119126895555482231 31943266678690343333223347)
              ·
                refine ⟨47914900018035514999835021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31943266678690343333223347 47914900018035514999835021)
                ·
                  refine ⟨17968087506763318124938133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47914900018035514999835021 17968087506763318124938133)
                  ·
                    refine ⟨842254101879530537106475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17968087506763318124938133 842254101879530537106475)
                    ·
                      rfl

theorem cell22_2460426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_2460426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460426 prefixEnd_2460426 := by exact prefixLift 2460426
  have htrace : WordTrace (prefixWord ++ tailWord_2460426) baseStart_2460426 baseEnd_2460426 := by
    simpa [prefixWord, tailWord_2460426, baseEnd_2460426] using wordTrace_append hprefix tailTrace_2460426
  have hstable : (prefixWord ++ tailWord_2460426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460426).length < 2 ^ (prefixWord ++ tailWord_2460426).sum := by decide
  have hdescent : baseEnd_2460426 < baseStart_2460426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460471 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 2, 6]
def baseStart_2460471 : Nat := 118140960795 + 2460471 * 2 ^ 59
def prefixEnd_2460471 : Nat := 4983230072969 + 3 ^ 40 * 2460471 * 2
def baseEnd_2460471 : Nat := 842269506299165419731337

theorem tailTrace_2460471 : CollatzResearch.WordTrace tailWord_2460471 prefixEnd_2460471 842269506299165419731337 := by
  unfold tailWord_2460471
  simp only [CollatzResearch.WordTrace]
  refine ⟨89740749869141256836885267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59827166579427504557923511 89740749869141256836885267)
  ·
    refine ⟨134611124803711885255327901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89740749869141256836885267 134611124803711885255327901)
    ·
      refine ⟨50479171801391956970747963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134611124803711885255327901 50479171801391956970747963)
      ·
        refine ⟨75718757702087935456121945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50479171801391956970747963 75718757702087935456121945)
        ·
          refine ⟨56789068276565951592091459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75718757702087935456121945 56789068276565951592091459)
          ·
            refine ⟨85183602414848927388137189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56789068276565951592091459 85183602414848927388137189)
            ·
              refine ⟨15971925452784173885275723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85183602414848927388137189 15971925452784173885275723)
              ·
                refine ⟨23957888179176260827913585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15971925452784173885275723 23957888179176260827913585)
                ·
                  refine ⟨17968416134382195620935189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23957888179176260827913585 17968416134382195620935189)
                  ·
                    refine ⟨842269506299165419731337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17968416134382195620935189 842269506299165419731337)
                    ·
                      rfl

theorem cell22_2460471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_2460471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460471 prefixEnd_2460471 := by exact prefixLift 2460471
  have htrace : WordTrace (prefixWord ++ tailWord_2460471) baseStart_2460471 baseEnd_2460471 := by
    simpa [prefixWord, tailWord_2460471, baseEnd_2460471] using wordTrace_append hprefix tailTrace_2460471
  have hstable : (prefixWord ++ tailWord_2460471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460471).length < 2 ^ (prefixWord ++ tailWord_2460471).sum := by decide
  have hdescent : baseEnd_2460471 < baseStart_2460471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460520 : List Nat := [2, 1, 4, 2, 1, 3, 2, 2, 5]
def baseStart_2460520 : Nat := 118140960795 + 2460520 * 2 ^ 59
def prefixEnd_2460520 : Nat := 4983230072969 + 3 ^ 40 * 2460520 * 2
def baseEnd_2460520 : Nat := 280762093333515208418729

theorem tailTrace_2460520 : CollatzResearch.WordTrace tailWord_2460520 prefixEnd_2460520 280762093333515208418729 := by
  unfold tailWord_2460520
  simp only [CollatzResearch.WordTrace]
  refine ⟨44871268522981869102709507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59828358030642492136946009 44871268522981869102709507)
  ·
    refine ⟨67306902784472803654064261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44871268522981869102709507 67306902784472803654064261)
    ·
      refine ⟨12620044272088650685137049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67306902784472803654064261 12620044272088650685137049)
      ·
        refine ⟨9465033204066488013852787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12620044272088650685137049 9465033204066488013852787)
        ·
          refine ⟨14197549806099732020779181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9465033204066488013852787 14197549806099732020779181)
          ·
            refine ⟨5324081177287399507792193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14197549806099732020779181 5324081177287399507792193)
            ·
              refine ⟨3993060882965549630844145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5324081177287399507792193 3993060882965549630844145)
              ·
                refine ⟨2994795662224162223133109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3993060882965549630844145 2994795662224162223133109)
                ·
                  refine ⟨280762093333515208418729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2994795662224162223133109 280762093333515208418729)
                  ·
                    rfl

theorem cell22_2460520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 5].length) (baseStart_2460520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460520 prefixEnd_2460520 := by exact prefixLift 2460520
  have htrace : WordTrace (prefixWord ++ tailWord_2460520) baseStart_2460520 baseEnd_2460520 := by
    simpa [prefixWord, tailWord_2460520, baseEnd_2460520] using wordTrace_append hprefix tailTrace_2460520
  have hstable : (prefixWord ++ tailWord_2460520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460520).length < 2 ^ (prefixWord ++ tailWord_2460520).sum := by decide
  have hdescent : baseEnd_2460520 < baseStart_2460520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460565 : List Nat := [1, 3, 2, 1, 1, 4, 1, 5, 4]
def baseStart_2460565 : Nat := 118140960795 + 2460565 * 2 ^ 59
def prefixEnd_2460565 : Nat := 4983230072969 + 3 ^ 40 * 2460565 * 2
def baseEnd_2460565 : Nat := 280767228140060169293683

theorem tailTrace_2460565 : CollatzResearch.WordTrace tailWord_2460565 prefixEnd_2460565 280767228140060169293683 := by
  unfold tailWord_2460565
  simp only [CollatzResearch.WordTrace]
  refine ⟨89744178330800710890807149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59829452220533807260538099 89744178330800710890807149)
  ·
    refine ⟨33654066874050266584052681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89744178330800710890807149 33654066874050266584052681)
    ·
      refine ⟨25240550155537699938039511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33654066874050266584052681 25240550155537699938039511)
      ·
        refine ⟨37860825233306549907059267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25240550155537699938039511 37860825233306549907059267)
        ·
          refine ⟨56791237849959824860588901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37860825233306549907059267 56791237849959824860588901)
          ·
            refine ⟨10648357096867467161360419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56791237849959824860588901 10648357096867467161360419)
            ·
              refine ⟨15972535645301200742040629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10648357096867467161360419 15972535645301200742040629)
              ·
                refine ⟨1497425216746987569566309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15972535645301200742040629 1497425216746987569566309)
                ·
                  refine ⟨280767228140060169293683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1497425216746987569566309 280767228140060169293683)
                  ·
                    rfl

theorem cell22_2460565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_2460565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460565 prefixEnd_2460565 := by exact prefixLift 2460565
  have htrace : WordTrace (prefixWord ++ tailWord_2460565) baseStart_2460565 baseEnd_2460565 := by
    simpa [prefixWord, tailWord_2460565, baseEnd_2460565] using wordTrace_append hprefix tailTrace_2460565
  have hstable : (prefixWord ++ tailWord_2460565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460565).length < 2 ^ (prefixWord ++ tailWord_2460565).sum := by decide
  have hdescent : baseEnd_2460565 < baseStart_2460565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460580 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_2460580 : Nat := 118140960795 + 2460580 * 2 ^ 59
def prefixEnd_2460580 : Nat := 4983230072969 + 3 ^ 40 * 2460580 * 2
def baseEnd_2460580 : Nat := 842306819226725468756003

theorem tailTrace_2460580 : CollatzResearch.WordTrace tailWord_2460580 prefixEnd_2460580 842306819226725468756003 := by
  unfold tailWord_2460580
  simp only [CollatzResearch.WordTrace]
  refine ⟨44872362712873184226301597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59829816950497578968402129 44872362712873184226301597)
  ·
    refine ⟨16827136017327444084863099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44872362712873184226301597 16827136017327444084863099)
    ·
      refine ⟨25240704025991166127294649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16827136017327444084863099 25240704025991166127294649)
      ·
        refine ⟨18930528019493374595470987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25240704025991166127294649 18930528019493374595470987)
        ·
          refine ⟨28395792029240061893206481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18930528019493374595470987 28395792029240061893206481)
          ·
            refine ⟨21296844021930046419904861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28395792029240061893206481 21296844021930046419904861)
            ·
              refine ⟨7986316508223767407464323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21296844021930046419904861 7986316508223767407464323)
              ·
                refine ⟨11979474762335651111196485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7986316508223767407464323 11979474762335651111196485)
                ·
                  refine ⟨2246151517937934583349341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11979474762335651111196485 2246151517937934583349341)
                  ·
                    refine ⟨842306819226725468756003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2246151517937934583349341 842306819226725468756003)
                    ·
                      rfl

theorem cell22_2460580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_2460580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460580 prefixEnd_2460580 := by exact prefixLift 2460580
  have htrace : WordTrace (prefixWord ++ tailWord_2460580) baseStart_2460580 baseEnd_2460580 := by
    simpa [prefixWord, tailWord_2460580, baseEnd_2460580] using wordTrace_append hprefix tailTrace_2460580
  have hstable : (prefixWord ++ tailWord_2460580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460580).length < 2 ^ (prefixWord ++ tailWord_2460580).sum := by decide
  have hdescent : baseEnd_2460580 < baseStart_2460580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460655 : List Nat := [1, 1, 2, 1, 4, 4, 1, 3, 5]
def baseStart_2460655 : Nat := 118140960795 + 2460655 * 2 ^ 59
def prefixEnd_2460655 : Nat := 4983230072969 + 3 ^ 40 * 2460655 * 2
def baseEnd_2460655 : Nat := 280777497753150091043591

theorem tailTrace_2460655 : CollatzResearch.WordTrace tailWord_2460655 prefixEnd_2460655 280777497753150091043591 := by
  unfold tailWord_2460655
  simp only [CollatzResearch.WordTrace]
  refine ⟨89747460900474656261583419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59831640600316437507722279 89747460900474656261583419)
  ·
    refine ⟨134621191350711984392375129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89747460900474656261583419 134621191350711984392375129)
    ·
      refine ⟨100965893513033988294281347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134621191350711984392375129 100965893513033988294281347)
      ·
        refine ⟨151448840269550982441422021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100965893513033988294281347 151448840269550982441422021)
        ·
          refine ⟨28396657550540809207766629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151448840269550982441422021 28396657550540809207766629)
          ·
            refine ⟨5324373290726401726456243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28396657550540809207766629 5324373290726401726456243)
            ·
              refine ⟨7986559936089602589684365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5324373290726401726456243 7986559936089602589684365)
              ·
                refine ⟨2994959976033600971131637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7986559936089602589684365 2994959976033600971131637)
                ·
                  refine ⟨280777497753150091043591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2994959976033600971131637 280777497753150091043591)
                  ·
                    rfl

theorem cell22_2460655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 5].length) (baseStart_2460655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460655 prefixEnd_2460655 := by exact prefixLift 2460655
  have htrace : WordTrace (prefixWord ++ tailWord_2460655) baseStart_2460655 baseEnd_2460655 := by
    simpa [prefixWord, tailWord_2460655, baseEnd_2460655] using wordTrace_append hprefix tailTrace_2460655
  have hstable : (prefixWord ++ tailWord_2460655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460655).length < 2 ^ (prefixWord ++ tailWord_2460655).sum := by decide
  have hdescent : baseEnd_2460655 < baseStart_2460655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460715 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 1, 5]
def baseStart_2460715 : Nat := 118140960795 + 2460715 * 2 ^ 59
def prefixEnd_2460715 : Nat := 4983230072969 + 3 ^ 40 * 2460715 * 2
def baseEnd_2460715 : Nat := 842353032485630116630589

theorem tailTrace_2460715 : CollatzResearch.WordTrace tailWord_2460715 prefixEnd_2460715 842353032485630116630589 := by
  unfold tailWord_2460715
  simp only [CollatzResearch.WordTrace]
  refine ⟨89749649280257286508767599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59833099520171524339178399 89749649280257286508767599)
  ·
    refine ⟨134624473920385929763151399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89749649280257286508767599 134624473920385929763151399)
    ·
      refine ⟨201936710880578894644727099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134624473920385929763151399 201936710880578894644727099)
      ·
        refine ⟨302905066320868341967090649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201936710880578894644727099 302905066320868341967090649)
        ·
          refine ⟨227178799740651256475317987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302905066320868341967090649 227178799740651256475317987)
          ·
            refine ⟨340768199610976884712976981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227178799740651256475317987 340768199610976884712976981)
            ·
              refine ⟨3993377339191135367730199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 340768199610976884712976981 3993377339191135367730199)
              ·
                refine ⟨5990066008786703051595299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3993377339191135367730199 5990066008786703051595299)
                ·
                  refine ⟨8985099013180054577392949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5990066008786703051595299 8985099013180054577392949)
                  ·
                    refine ⟨842353032485630116630589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8985099013180054577392949 842353032485630116630589)
                    ·
                      rfl

theorem cell22_2460715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 5].length) (baseStart_2460715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460715 prefixEnd_2460715 := by exact prefixLift 2460715
  have htrace : WordTrace (prefixWord ++ tailWord_2460715) baseStart_2460715 baseEnd_2460715 := by
    simpa [prefixWord, tailWord_2460715, baseEnd_2460715] using wordTrace_append hprefix tailTrace_2460715
  have hstable : (prefixWord ++ tailWord_2460715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460715).length < 2 ^ (prefixWord ++ tailWord_2460715).sum := by decide
  have hdescent : baseEnd_2460715 < baseStart_2460715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460734 : List Nat := [4, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_2460734 : Nat := 118140960795 + 2460734 * 2 ^ 59
def prefixEnd_2460734 : Nat := 4983230072969 + 3 ^ 40 * 2460734 * 2
def baseEnd_2460734 : Nat := 280786512191306800135177

theorem tailTrace_2460734 : CollatzResearch.WordTrace tailWord_2460734 prefixEnd_2460734 280786512191306800135177 := by
  unfold tailWord_2460734
  simp only [CollatzResearch.WordTrace]
  refine ⟨11218792783398556594213657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59833561511458968502472837 11218792783398556594213657)
  ·
    refine ⟨8414094587548917445660243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11218792783398556594213657 8414094587548917445660243)
    ·
      refine ⟨12621141881323376168490365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8414094587548917445660243 12621141881323376168490365)
      ·
        refine ⟨4732928205496266063183887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12621141881323376168490365 4732928205496266063183887)
        ·
          refine ⟨7099392308244399094775831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4732928205496266063183887 7099392308244399094775831)
          ·
            refine ⟨10649088462366598642163747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7099392308244399094775831 10649088462366598642163747)
            ·
              refine ⟨15973632693549897963245621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10649088462366598642163747 15973632693549897963245621)
              ·
                refine ⟨1497528065020302934054277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15973632693549897963245621 1497528065020302934054277)
                ·
                  refine ⟨280786512191306800135177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1497528065020302934054277 280786512191306800135177)
                  ·
                    rfl

theorem cell22_2460734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_2460734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460734 prefixEnd_2460734 := by exact prefixLift 2460734
  have htrace : WordTrace (prefixWord ++ tailWord_2460734) baseStart_2460734 baseEnd_2460734 := by
    simpa [prefixWord, tailWord_2460734, baseEnd_2460734] using wordTrace_append hprefix tailTrace_2460734
  have hstable : (prefixWord ++ tailWord_2460734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460734).length < 2 ^ (prefixWord ++ tailWord_2460734).sum := by decide
  have hdescent : baseEnd_2460734 < baseStart_2460734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460749 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_2460749 : Nat := 118140960795 + 2460749 * 2 ^ 59
def prefixEnd_2460749 : Nat := 4983230072969 + 3 ^ 40 * 2460749 * 2
def baseEnd_2460749 : Nat := 842364671380465361280485

theorem tailTrace_2460749 : CollatzResearch.WordTrace tailWord_2460749 prefixEnd_2460749 842364671380465361280485 := by
  unfold tailWord_2460749
  simp only [CollatzResearch.WordTrace]
  refine ⟨89750889362134110315505301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59833926241422740210336867 89750889362134110315505301)
  ·
    refine ⟨4207072938850036421039311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89750889362134110315505301 4207072938850036421039311)
    ·
      refine ⟨6310609408275054631558967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4207072938850036421039311 6310609408275054631558967)
      ·
        refine ⟨9465914112412581947338451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6310609408275054631558967 9465914112412581947338451)
        ·
          refine ⟨14198871168618872921007677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9465914112412581947338451 14198871168618872921007677)
          ·
            refine ⟨5324576688232077345377879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14198871168618872921007677 5324576688232077345377879)
            ·
              refine ⟨7986865032348116018066819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5324576688232077345377879 7986865032348116018066819)
              ·
                refine ⟨11980297548522174027100229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7986865032348116018066819 11980297548522174027100229)
                ·
                  refine ⟨2246305790347907630081293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11980297548522174027100229 2246305790347907630081293)
                  ·
                    refine ⟨842364671380465361280485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2246305790347907630081293 842364671380465361280485)
                    ·
                      rfl

theorem cell22_2460749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_2460749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460749 prefixEnd_2460749 := by exact prefixLift 2460749
  have htrace : WordTrace (prefixWord ++ tailWord_2460749) baseStart_2460749 baseEnd_2460749 := by
    simpa [prefixWord, tailWord_2460749, baseEnd_2460749] using wordTrace_append hprefix tailTrace_2460749
  have hstable : (prefixWord ++ tailWord_2460749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460749).length < 2 ^ (prefixWord ++ tailWord_2460749).sum := by decide
  have hdescent : baseEnd_2460749 < baseStart_2460749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460766 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2460766 : Nat := 118140960795 + 2460766 * 2 ^ 59
def prefixEnd_2460766 : Nat := 4983230072969 + 3 ^ 40 * 2460766 * 2
def baseEnd_2460766 : Nat := 842370490827882983605433

theorem tailTrace_2460766 : CollatzResearch.WordTrace tailWord_2460766 prefixEnd_2460766 842370490827882983605433 := by
  unfold tailWord_2460766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11218938675384065277359269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59834339602048348145916101 11218938675384065277359269)
  ·
    refine ⟨2103551001634512239504863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11218938675384065277359269 2103551001634512239504863)
    ·
      refine ⟨3155326502451768359257295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2103551001634512239504863 3155326502451768359257295)
      ·
        refine ⟨4732989753677652538885943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3155326502451768359257295 4732989753677652538885943)
        ·
          refine ⟨7099484630516478808328915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4732989753677652538885943 7099484630516478808328915)
          ·
            refine ⟨10649226945774718212493373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7099484630516478808328915 10649226945774718212493373)
            ·
              refine ⟨3993460104665519329685015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10649226945774718212493373 3993460104665519329685015)
              ·
                refine ⟨5990190156998278994527523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3993460104665519329685015 5990190156998278994527523)
                ·
                  refine ⟨8985285235497418491791285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5990190156998278994527523 8985285235497418491791285)
                  ·
                    refine ⟨842370490827882983605433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8985285235497418491791285 842370490827882983605433)
                    ·
                      rfl

theorem cell22_2460766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2460766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460766 prefixEnd_2460766 := by exact prefixLift 2460766
  have htrace : WordTrace (prefixWord ++ tailWord_2460766) baseStart_2460766 baseEnd_2460766 := by
    simpa [prefixWord, tailWord_2460766, baseEnd_2460766] using wordTrace_append hprefix tailTrace_2460766
  have hstable : (prefixWord ++ tailWord_2460766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460766).length < 2 ^ (prefixWord ++ tailWord_2460766).sum := by decide
  have hdescent : baseEnd_2460766 < baseStart_2460766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460777 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 3, 3]
def baseStart_2460777 : Nat := 118140960795 + 2460777 * 2 ^ 59
def prefixEnd_2460777 : Nat := 4983230072969 + 3 ^ 40 * 2460777 * 2
def baseEnd_2460777 : Nat := 842374256352682621580399

theorem tailTrace_2460777 : CollatzResearch.WordTrace tailWord_2460777 prefixEnd_2460777 842374256352682621580399 := by
  unfold tailWord_2460777
  simp only [CollatzResearch.WordTrace]
  refine ⟨89751910606032671097524585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59834607070688447398349723 89751910606032671097524585)
  ·
    refine ⟨67313932954524503323143439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89751910606032671097524585 67313932954524503323143439)
    ·
      refine ⟨100970899431786754984715159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67313932954524503323143439 100970899431786754984715159)
      ·
        refine ⟨151456349147680132477072739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100970899431786754984715159 151456349147680132477072739)
        ·
          refine ⟨227184523721520198715609109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151456349147680132477072739 227184523721520198715609109)
          ·
            refine ⟨10649274549446259314794177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 227184523721520198715609109 10649274549446259314794177)
            ·
              refine ⟨7986955912084694486095633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10649274549446259314794177 7986955912084694486095633)
              ·
                refine ⟨5990216934063520864571725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7986955912084694486095633 5990216934063520864571725)
                ·
                  refine ⟨2246331350273820324214397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5990216934063520864571725 2246331350273820324214397)
                  ·
                    refine ⟨842374256352682621580399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2246331350273820324214397 842374256352682621580399)
                    ·
                      rfl

theorem cell22_2460777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 3].length) (baseStart_2460777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460777 prefixEnd_2460777 := by exact prefixLift 2460777
  have htrace : WordTrace (prefixWord ++ tailWord_2460777) baseStart_2460777 baseEnd_2460777 := by
    simpa [prefixWord, tailWord_2460777, baseEnd_2460777] using wordTrace_append hprefix tailTrace_2460777
  have hstable : (prefixWord ++ tailWord_2460777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460777).length < 2 ^ (prefixWord ++ tailWord_2460777).sum := by decide
  have hdescent : baseEnd_2460777 < baseStart_2460777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2460798 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2460798 : Nat := 118140960795 + 2460798 * 2 ^ 59
def prefixEnd_2460798 : Nat := 4983230072969 + 3 ^ 40 * 2460798 * 2
def baseEnd_2460798 : Nat := 842381445081845566805335

theorem tailTrace_2460798 : CollatzResearch.WordTrace tailWord_2460798 prefixEnd_2460798 842381445081845566805335 := by
  unfold tailWord_2460798
  simp only [CollatzResearch.WordTrace]
  refine ⟨11219084567369573960504881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59835117692637727789359365 11219084567369573960504881)
  ·
    refine ⟨8414313425527180470378661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11219084567369573960504881 8414313425527180470378661)
    ·
      refine ⟨1577683767286346338195999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8414313425527180470378661 1577683767286346338195999)
      ·
        refine ⟨2366525650929519507293999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577683767286346338195999 2366525650929519507293999)
        ·
          refine ⟨3549788476394279260940999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2366525650929519507293999 3549788476394279260940999)
          ·
            refine ⟨5324682714591418891411499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3549788476394279260940999 5324682714591418891411499)
            ·
              refine ⟨7987024071887128337117249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5324682714591418891411499 7987024071887128337117249)
              ·
                refine ⟨5990268053915346252837937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7987024071887128337117249 5990268053915346252837937)
                ·
                  refine ⟨4492701040436509689628453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5990268053915346252837937 4492701040436509689628453)
                  ·
                    refine ⟨842381445081845566805335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4492701040436509689628453 842381445081845566805335)
                    ·
                      rfl

theorem cell22_2460798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2460798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2460798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2460798 prefixEnd_2460798 := by exact prefixLift 2460798
  have htrace : WordTrace (prefixWord ++ tailWord_2460798) baseStart_2460798 baseEnd_2460798 := by
    simpa [prefixWord, tailWord_2460798, baseEnd_2460798] using wordTrace_append hprefix tailTrace_2460798
  have hstable : (prefixWord ++ tailWord_2460798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2460798).length < 2 ^ (prefixWord ++ tailWord_2460798).sum := by decide
  have hdescent : baseEnd_2460798 < baseStart_2460798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2460798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
