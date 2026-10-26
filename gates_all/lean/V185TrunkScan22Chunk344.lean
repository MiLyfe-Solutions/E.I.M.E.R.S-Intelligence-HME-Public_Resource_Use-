import V185TrunkScan22Chunk343

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3069792 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 4, 3]
def baseStart_3069792 : Nat := 118140960795 + 3069792 * 2 ^ 59
def prefixEnd_3069792 : Nat := 4983230072969 + 3 ^ 40 * 3069792 * 2
def baseEnd_3069792 : Nat := 1050852536884639105588193

theorem tailTrace_3069792 : CollatzResearch.WordTrace tailWord_3069792 prefixEnd_3069792 1050852536884639105588193 := by
  unfold tailWord_3069792
  simp only [CollatzResearch.WordTrace]
  refine ⟨55982256247337668789373815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74643008329783558385831753 55982256247337668789373815)
  ·
    refine ⟨83973384371006503184060723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55982256247337668789373815 83973384371006503184060723)
    ·
      refine ⟨125960076556509754776091085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83973384371006503184060723 125960076556509754776091085)
      ·
        refine ⟨47235028708691158041034157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125960076556509754776091085 47235028708691158041034157)
        ·
          refine ⟨17713135765759184265387809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47235028708691158041034157 17713135765759184265387809)
          ·
            refine ⟨13284851824319388199040857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17713135765759184265387809 13284851824319388199040857)
            ·
              refine ⟨9963638868239541149280643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13284851824319388199040857 9963638868239541149280643)
              ·
                refine ⟨14945458302359311723920965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9963638868239541149280643 14945458302359311723920965)
                ·
                  refine ⟨2802273431692370948235181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14945458302359311723920965 2802273431692370948235181)
                  ·
                    refine ⟨1050852536884639105588193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2802273431692370948235181 1050852536884639105588193)
                    ·
                      rfl

theorem cell22_3069792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 4, 3].length) (baseStart_3069792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069792 prefixEnd_3069792 := by exact prefixLift 3069792
  have htrace : WordTrace (prefixWord ++ tailWord_3069792) baseStart_3069792 baseEnd_3069792 := by
    simpa [prefixWord, tailWord_3069792, baseEnd_3069792] using wordTrace_append hprefix tailTrace_3069792
  have hstable : (prefixWord ++ tailWord_3069792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069792).length < 2 ^ (prefixWord ++ tailWord_3069792).sum := by decide
  have hdescent : baseEnd_3069792 < baseStart_3069792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069794 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 6]
def baseStart_3069794 : Nat := 118140960795 + 3069794 * 2 ^ 59
def prefixEnd_3069794 : Nat := 4983230072969 + 3 ^ 40 * 3069794 * 2
def baseEnd_3069794 : Nat := 350284407175170589012729

theorem tailTrace_3069794 : CollatzResearch.WordTrace tailWord_3069794 prefixEnd_3069794 350284407175170589012729 := by
  unfold tailWord_3069794
  simp only [CollatzResearch.WordTrace]
  refine ⟨27991146360167022980080109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74643056960445394613546957 27991146360167022980080109)
  ·
    refine ⟨10496679885062633617530041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27991146360167022980080109 10496679885062633617530041)
    ·
      refine ⟨7872509913796975213147531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10496679885062633617530041 7872509913796975213147531)
      ·
        refine ⟨11808764870695462819721297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7872509913796975213147531 11808764870695462819721297)
        ·
          refine ⟨8856573653021597114790973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11808764870695462819721297 8856573653021597114790973)
          ·
            refine ⟨3321215119883098918046615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8856573653021597114790973 3321215119883098918046615)
            ·
              refine ⟨4981822679824648377069923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321215119883098918046615 4981822679824648377069923)
              ·
                refine ⟨7472734019736972565604885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4981822679824648377069923 7472734019736972565604885)
                ·
                  refine ⟨350284407175170589012729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7472734019736972565604885 350284407175170589012729)
                  ·
                    rfl

theorem cell22_3069794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_3069794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069794 prefixEnd_3069794 := by exact prefixLift 3069794
  have htrace : WordTrace (prefixWord ++ tailWord_3069794) baseStart_3069794 baseEnd_3069794 := by
    simpa [prefixWord, tailWord_3069794, baseEnd_3069794] using wordTrace_append hprefix tailTrace_3069794
  have hstable : (prefixWord ++ tailWord_3069794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069794).length < 2 ^ (prefixWord ++ tailWord_3069794).sum := by decide
  have hdescent : baseEnd_3069794 < baseStart_3069794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069805 : List Nat := [1, 5, 1, 1, 1, 1, 3, 9]
def baseStart_3069805 : Nat := 118140960795 + 3069805 * 2 ^ 59
def prefixEnd_3069805 : Nat := 4983230072969 + 3 ^ 40 * 3069805 * 2
def baseEnd_3069805 : Nat := 116761887450034600557017

theorem tailTrace_3069805 : CollatzResearch.WordTrace tailWord_3069805 prefixEnd_3069805 116761887450034600557017 := by
  unfold tailWord_3069805
  simp only [CollatzResearch.WordTrace]
  refine ⟨111964986643628240798970869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74643324429085493865980579 111964986643628240798970869)
  ·
    refine ⟨10496717497840147574903519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111964986643628240798970869 10496717497840147574903519)
    ·
      refine ⟨15745076246760221362355279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10496717497840147574903519 15745076246760221362355279)
      ·
        refine ⟨23617614370140332043532919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15745076246760221362355279 23617614370140332043532919)
        ·
          refine ⟨35426421555210498065299379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23617614370140332043532919 35426421555210498065299379)
          ·
            refine ⟨53139632332815747097949069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35426421555210498065299379 53139632332815747097949069)
            ·
              refine ⟨19927362124805905161730901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53139632332815747097949069 19927362124805905161730901)
              ·
                refine ⟨116761887450034600557017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19927362124805905161730901 116761887450034600557017)
                ·
                  rfl

theorem cell22_3069805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 9].length) (baseStart_3069805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069805 prefixEnd_3069805 := by exact prefixLift 3069805
  have htrace : WordTrace (prefixWord ++ tailWord_3069805) baseStart_3069805 baseEnd_3069805 := by
    simpa [prefixWord, tailWord_3069805, baseEnd_3069805] using wordTrace_append hprefix tailTrace_3069805
  have hstable : (prefixWord ++ tailWord_3069805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069805).length < 2 ^ (prefixWord ++ tailWord_3069805).sum := by decide
  have hdescent : baseEnd_3069805 < baseStart_3069805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069852 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_3069852 : Nat := 118140960795 + 3069852 * 2 ^ 59
def prefixEnd_3069852 : Nat := 4983230072969 + 3 ^ 40 * 3069852 * 2
def baseEnd_3069852 : Nat := 1050873076110818949088009

theorem tailTrace_3069852 : CollatzResearch.WordTrace tailWord_3069852 prefixEnd_3069852 1050873076110818949088009 := by
  unfold tailWord_3069852
  simp only [CollatzResearch.WordTrace]
  refine ⟨55983350437228983912965905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74644467249638645217287873 55983350437228983912965905)
  ·
    refine ⟨41987512827921737934724429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55983350437228983912965905 41987512827921737934724429)
    ·
      refine ⟨15745317310470651725521661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41987512827921737934724429 15745317310470651725521661)
      ·
        refine ⟨5904493991426494397070623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15745317310470651725521661 5904493991426494397070623)
        ·
          refine ⟨8856740987139741595605935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5904493991426494397070623 8856740987139741595605935)
          ·
            refine ⟨13285111480709612393408903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8856740987139741595605935 13285111480709612393408903)
            ·
              refine ⟨19927667221064418590113355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13285111480709612393408903 19927667221064418590113355)
              ·
                refine ⟨29891500831596627885170033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19927667221064418590113355 29891500831596627885170033)
                ·
                  refine ⟨22418625623697470913877525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29891500831596627885170033 22418625623697470913877525)
                  ·
                    refine ⟨1050873076110818949088009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22418625623697470913877525 1050873076110818949088009)
                    ·
                      rfl

theorem cell22_3069852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_3069852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069852 prefixEnd_3069852 := by exact prefixLift 3069852
  have htrace : WordTrace (prefixWord ++ tailWord_3069852) baseStart_3069852 baseEnd_3069852 := by
    simpa [prefixWord, tailWord_3069852, baseEnd_3069852] using wordTrace_append hprefix tailTrace_3069852
  have hstable : (prefixWord ++ tailWord_3069852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069852).length < 2 ^ (prefixWord ++ tailWord_3069852).sum := by decide
  have hdescent : baseEnd_3069852 < baseStart_3069852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069895 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 10]
def baseStart_3069895 : Nat := 118140960795 + 3069895 * 2 ^ 59
def prefixEnd_3069895 : Nat := 4983230072969 + 3 ^ 40 * 3069895 * 2
def baseEnd_3069895 : Nat := 350295931963193723420959

theorem tailTrace_3069895 : CollatzResearch.WordTrace tailWord_3069895 prefixEnd_3069895 350295931963193723420959 := by
  unfold tailWord_3069895
  simp only [CollatzResearch.WordTrace]
  refine ⟨111968269213302186169747139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74645512808868124113164759 111968269213302186169747139)
  ·
    refine ⟨167952403819953279254620709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111968269213302186169747139 167952403819953279254620709)
    ·
      refine ⟨31491075716241239860241383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167952403819953279254620709 31491075716241239860241383)
      ·
        refine ⟨47236613574361859790362075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31491075716241239860241383 47236613574361859790362075)
        ·
          refine ⟨70854920361542789685543113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47236613574361859790362075 70854920361542789685543113)
          ·
            refine ⟨53141190271157092264157335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70854920361542789685543113 53141190271157092264157335)
            ·
              refine ⟨79711785406735638396236003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53141190271157092264157335 79711785406735638396236003)
              ·
                refine ⟨119567678110103457594354005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79711785406735638396236003 119567678110103457594354005)
                ·
                  refine ⟨350295931963193723420959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 119567678110103457594354005 350295931963193723420959)
                  ·
                    rfl

theorem cell22_3069895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 10].length) (baseStart_3069895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069895 prefixEnd_3069895 := by exact prefixLift 3069895
  have htrace : WordTrace (prefixWord ++ tailWord_3069895) baseStart_3069895 baseEnd_3069895 := by
    simpa [prefixWord, tailWord_3069895, baseEnd_3069895] using wordTrace_append hprefix tailTrace_3069895
  have hstable : (prefixWord ++ tailWord_3069895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069895).length < 2 ^ (prefixWord ++ tailWord_3069895).sum := by decide
  have hdescent : baseEnd_3069895 < baseStart_3069895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069897 : List Nat := [1, 2, 1, 1, 2, 1, 2, 7, 1, 4]
def baseStart_3069897 : Nat := 118140960795 + 3069897 * 2 ^ 59
def prefixEnd_3069897 : Nat := 4983230072969 + 3 ^ 40 * 3069897 * 2
def baseEnd_3069897 : Nat := 1050888480530453831712871

theorem tailTrace_3069897 : CollatzResearch.WordTrace tailWord_3069897 prefixEnd_3069897 1050888480530453831712871 := by
  unfold tailWord_3069897
  simp only [CollatzResearch.WordTrace]
  refine ⟨111968342159294940511319945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74645561439529960340879963 111968342159294940511319945)
  ·
    refine ⟨83976256619471205383489959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111968342159294940511319945 83976256619471205383489959)
    ·
      refine ⟨125964384929206808075234939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83976256619471205383489959 125964384929206808075234939)
      ·
        refine ⟨188946577393810212112852409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125964384929206808075234939 188946577393810212112852409)
        ·
          refine ⟨141709933045357659084639307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188946577393810212112852409 141709933045357659084639307)
          ·
            refine ⟨212564899568036488626958961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141709933045357659084639307 212564899568036488626958961)
            ·
              refine ⟨159423674676027366470219221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212564899568036488626958961 159423674676027366470219221)
              ·
                refine ⟨3736492375219391401645763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 159423674676027366470219221 3736492375219391401645763)
                ·
                  refine ⟨5604738562829087102468645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736492375219391401645763 5604738562829087102468645)
                  ·
                    refine ⟨1050888480530453831712871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5604738562829087102468645 1050888480530453831712871)
                    ·
                      rfl

theorem cell22_3069897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_3069897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069897 prefixEnd_3069897 := by exact prefixLift 3069897
  have htrace : WordTrace (prefixWord ++ tailWord_3069897) baseStart_3069897 baseEnd_3069897 := by
    simpa [prefixWord, tailWord_3069897, baseEnd_3069897] using wordTrace_append hprefix tailTrace_3069897
  have hstable : (prefixWord ++ tailWord_3069897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069897).length < 2 ^ (prefixWord ++ tailWord_3069897).sum := by decide
  have hdescent : baseEnd_3069897 < baseStart_3069897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069912 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 6]
def baseStart_3069912 : Nat := 118140960795 + 3069912 * 2 ^ 59
def prefixEnd_3069912 : Nat := 4983230072969 + 3 ^ 40 * 3069912 * 2
def baseEnd_3069912 : Nat := 350297871778999597529275

theorem tailTrace_3069912 : CollatzResearch.WordTrace tailWord_3069912 prefixEnd_3069912 350297871778999597529275 := by
  unfold tailWord_3069912
  simp only [CollatzResearch.WordTrace]
  refine ⟨55984444627120299036557995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74645926169493732048743993 55984444627120299036557995)
  ·
    refine ⟨83976666940680448554836993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55984444627120299036557995 83976666940680448554836993)
    ·
      refine ⟨62982500205510336416127745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83976666940680448554836993 62982500205510336416127745)
      ·
        refine ⟨47236875154132752312095809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62982500205510336416127745 47236875154132752312095809)
        ·
          refine ⟨35427656365599564234071857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47236875154132752312095809 35427656365599564234071857)
          ·
            refine ⟨26570742274199673175553893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35427656365599564234071857 26570742274199673175553893)
            ·
              refine ⟨4982014176412438720416355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26570742274199673175553893 4982014176412438720416355)
              ·
                refine ⟨7473021264618658080624533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4982014176412438720416355 7473021264618658080624533)
                ·
                  refine ⟨350297871778999597529275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7473021264618658080624533 350297871778999597529275)
                  ·
                    rfl

theorem cell22_3069912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 6].length) (baseStart_3069912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069912 prefixEnd_3069912 := by exact prefixLift 3069912
  have htrace : WordTrace (prefixWord ++ tailWord_3069912) baseStart_3069912 baseEnd_3069912 := by
    simpa [prefixWord, tailWord_3069912, baseEnd_3069912] using wordTrace_append hprefix tailTrace_3069912
  have hstable : (prefixWord ++ tailWord_3069912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069912).length < 2 ^ (prefixWord ++ tailWord_3069912).sum := by decide
  have hdescent : baseEnd_3069912 < baseStart_3069912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069957 : List Nat := [1, 3, 1, 1, 2, 6, 8]
def baseStart_3069957 : Nat := 118140960795 + 3069957 * 2 ^ 59
def prefixEnd_3069957 : Nat := 4983230072969 + 3 ^ 40 * 3069957 * 2
def baseEnd_3069957 : Nat := 38922556287282728711581

theorem tailTrace_3069957 : CollatzResearch.WordTrace tailWord_3069957 prefixEnd_3069957 38922556287282728711581 := by
  unfold tailWord_3069957
  simp only [CollatzResearch.WordTrace]
  refine ⟨111970530539077570758504125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74647020359385047172336083 111970530539077570758504125)
  ·
    refine ⟨41988948952154089034439047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111970530539077570758504125 41988948952154089034439047)
    ·
      refine ⟨62983423428231133551658571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41988948952154089034439047 62983423428231133551658571)
      ·
        refine ⟨94475135142346700327487857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62983423428231133551658571 94475135142346700327487857)
        ·
          refine ⟨70856351356760025245615893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94475135142346700327487857 70856351356760025245615893)
          ·
            refine ⟨3321391469848126183388245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70856351356760025245615893 3321391469848126183388245)
            ·
              refine ⟨38922556287282728711581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3321391469848126183388245 38922556287282728711581)
              ·
                rfl

theorem cell22_3069957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 8].length) (baseStart_3069957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069957 prefixEnd_3069957 := by exact prefixLift 3069957
  have htrace : WordTrace (prefixWord ++ tailWord_3069957) baseStart_3069957 baseEnd_3069957 := by
    simpa [prefixWord, tailWord_3069957, baseEnd_3069957] using wordTrace_append hprefix tailTrace_3069957
  have hstable : (prefixWord ++ tailWord_3069957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069957).length < 2 ^ (prefixWord ++ tailWord_3069957).sum := by decide
  have hdescent : baseEnd_3069957 < baseStart_3069957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069959 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 2, 4]
def baseStart_3069959 : Nat := 118140960795 + 3069959 * 2 ^ 59
def prefixEnd_3069959 : Nat := 4983230072969 + 3 ^ 40 * 3069959 * 2
def baseEnd_3069959 : Nat := 1050909704397506336662681

theorem tailTrace_3069959 : CollatzResearch.WordTrace tailWord_3069959 prefixEnd_3069959 1050909704397506336662681 := by
  unfold tailWord_3069959
  simp only [CollatzResearch.WordTrace]
  refine ⟨111970603485070325100076931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74647068990046883400051287 111970603485070325100076931)
  ·
    refine ⟨167955905227605487650115397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111970603485070325100076931 167955905227605487650115397)
    ·
      refine ⟨31491732230176028934396637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167955905227605487650115397 31491732230176028934396637)
      ·
        refine ⟨11809399586316010850398739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31491732230176028934396637 11809399586316010850398739)
        ·
          refine ⟨17714099379474016275598109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11809399586316010850398739 17714099379474016275598109)
          ·
            refine ⟨6642787267302756103349291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17714099379474016275598109 6642787267302756103349291)
            ·
              refine ⟨9964180900954134155023937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6642787267302756103349291 9964180900954134155023937)
              ·
                refine ⟨7473135675715600616267953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9964180900954134155023937 7473135675715600616267953)
                ·
                  refine ⟨5604851756786700462200965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7473135675715600616267953 5604851756786700462200965)
                  ·
                    refine ⟨1050909704397506336662681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5604851756786700462200965 1050909704397506336662681)
                    ·
                      rfl

theorem cell22_3069959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_3069959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069959 prefixEnd_3069959 := by exact prefixLift 3069959
  have htrace : WordTrace (prefixWord ++ tailWord_3069959) baseStart_3069959 baseEnd_3069959 := by
    simpa [prefixWord, tailWord_3069959, baseEnd_3069959] using wordTrace_append hprefix tailTrace_3069959
  have hstable : (prefixWord ++ tailWord_3069959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069959).length < 2 ^ (prefixWord ++ tailWord_3069959).sum := by decide
  have hdescent : baseEnd_3069959 < baseStart_3069959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069978 : List Nat := [3, 1, 1, 3, 1, 5, 2, 1, 2, 3]
def baseStart_3069978 : Nat := 118140960795 + 3069978 * 2 ^ 59
def prefixEnd_3069978 : Nat := 4983230072969 + 3 ^ 40 * 3069978 * 2
def baseEnd_3069978 : Nat := 1050916208485796620437623

theorem tailTrace_3069978 : CollatzResearch.WordTrace tailWord_3069978 prefixEnd_3069978 1050916208485796620437623 := by
  unfold tailWord_3069978
  simp only [CollatzResearch.WordTrace]
  refine ⟨27992824118000372836254647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74647530981334327563345725 27992824118000372836254647)
  ·
    refine ⟨41989236177000559254381971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27992824118000372836254647 41989236177000559254381971)
    ·
      refine ⟨62983854265500838881572957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41989236177000559254381971 62983854265500838881572957)
      ·
        refine ⟨23618945349562814580589859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62983854265500838881572957 23618945349562814580589859)
        ·
          refine ⟨35428418024344221870884789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23618945349562814580589859 35428418024344221870884789)
          ·
            refine ⟨3321414189782270800395449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35428418024344221870884789 3321414189782270800395449)
            ·
              refine ⟨2491060642336703100296587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3321414189782270800395449 2491060642336703100296587)
              ·
                refine ⟨3736590963505054650444881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491060642336703100296587 3736590963505054650444881)
                ·
                  refine ⟨2802443222628790987833661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3736590963505054650444881 2802443222628790987833661)
                  ·
                    refine ⟨1050916208485796620437623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2802443222628790987833661 1050916208485796620437623)
                    ·
                      rfl

theorem cell22_3069978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_3069978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3069978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3069978 prefixEnd_3069978 := by exact prefixLift 3069978
  have htrace : WordTrace (prefixWord ++ tailWord_3069978) baseStart_3069978 baseEnd_3069978 := by
    simpa [prefixWord, tailWord_3069978, baseEnd_3069978] using wordTrace_append hprefix tailTrace_3069978
  have hstable : (prefixWord ++ tailWord_3069978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069978).length < 2 ^ (prefixWord ++ tailWord_3069978).sum := by decide
  have hdescent : baseEnd_3069978 < baseStart_3069978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070049 : List Nat := [1, 2, 3, 1, 1, 2, 1, 6, 1, 4]
def baseStart_3070049 : Nat := 118140960795 + 3070049 * 2 ^ 59
def prefixEnd_3070049 : Nat := 4983230072969 + 3 ^ 40 * 3070049 * 2
def baseEnd_3070049 : Nat := 1050940513236776101912405

theorem tailTrace_3070049 : CollatzResearch.WordTrace tailWord_3070049 prefixEnd_3070049 1050940513236776101912405 := by
  unfold tailWord_3070049
  simp only [CollatzResearch.WordTrace]
  refine ⟨111973886054744270470853201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74649257369829513647235467 111973886054744270470853201)
  ·
    refine ⟨83980414541058202853139901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111973886054744270470853201 83980414541058202853139901)
    ·
      refine ⟨31492655452896826069927463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83980414541058202853139901 31492655452896826069927463)
      ·
        refine ⟨47238983179345239104891195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31492655452896826069927463 47238983179345239104891195)
        ·
          refine ⟨70858474769017858657336793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47238983179345239104891195 70858474769017858657336793)
          ·
            refine ⟨53143856076763393993002595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70858474769017858657336793 53143856076763393993002595)
            ·
              refine ⟨79715784115145090989503893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53143856076763393993002595 79715784115145090989503893)
              ·
                refine ⟨3736677380397426140132995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79715784115145090989503893 3736677380397426140132995)
                ·
                  refine ⟨5605016070596139210199493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736677380397426140132995 5605016070596139210199493)
                  ·
                    refine ⟨1050940513236776101912405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5605016070596139210199493 1050940513236776101912405)
                    ·
                      rfl

theorem cell22_3070049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_3070049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070049 prefixEnd_3070049 := by exact prefixLift 3070049
  have htrace : WordTrace (prefixWord ++ tailWord_3070049) baseStart_3070049 baseEnd_3070049 := by
    simpa [prefixWord, tailWord_3070049, baseEnd_3070049] using wordTrace_append hprefix tailTrace_3070049
  have hstable : (prefixWord ++ tailWord_3070049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070049).length < 2 ^ (prefixWord ++ tailWord_3070049).sum := by decide
  have hdescent : baseEnd_3070049 < baseStart_3070049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070066 : List Nat := [3, 2, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_3070066 : Nat := 118140960795 + 3070066 * 2 ^ 59
def prefixEnd_3070066 : Nat := 4983230072969 + 3 ^ 40 * 3070066 * 2
def baseEnd_3070066 : Nat := 1050946332684193724237353

theorem tailTrace_3070066 : CollatzResearch.WordTrace tailWord_3070066 prefixEnd_3070066 1050946332684193724237353 := by
  unfold tailWord_3070066
  simp only [CollatzResearch.WordTrace]
  refine ⟨27993626523920670593555513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74649670730455121582814701 27993626523920670593555513)
  ·
    refine ⟨20995219892940502945166635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27993626523920670593555513 20995219892940502945166635)
    ·
      refine ⟨31492829839410754417749953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20995219892940502945166635 31492829839410754417749953)
      ·
        refine ⟨23619622379558065813312465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31492829839410754417749953 23619622379558065813312465)
        ·
          refine ⟨17714716784668549359984349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23619622379558065813312465 17714716784668549359984349)
          ·
            refine ⟨6643018794250706009994131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17714716784668549359984349 6643018794250706009994131)
            ·
              refine ⟨9964528191376059014991197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6643018794250706009994131 9964528191376059014991197)
              ·
                refine ⟨3736698071766022130621699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9964528191376059014991197 3736698071766022130621699)
                ·
                  refine ⟨5605047107649033195932549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736698071766022130621699 5605047107649033195932549)
                  ·
                    refine ⟨1050946332684193724237353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5605047107649033195932549 1050946332684193724237353)
                    ·
                      rfl

theorem cell22_3070066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_3070066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070066 prefixEnd_3070066 := by exact prefixLift 3070066
  have htrace : WordTrace (prefixWord ++ tailWord_3070066) baseStart_3070066 baseEnd_3070066 := by
    simpa [prefixWord, tailWord_3070066, baseEnd_3070066] using wordTrace_append hprefix tailTrace_3070066
  have hstable : (prefixWord ++ tailWord_3070066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070066).length < 2 ^ (prefixWord ++ tailWord_3070066).sum := by decide
  have hdescent : baseEnd_3070066 < baseStart_3070066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070081 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 6]
def baseStart_3070081 : Nat := 118140960795 + 3070081 * 2 ^ 59
def prefixEnd_3070081 : Nat := 4983230072969 + 3 ^ 40 * 3070081 * 2
def baseEnd_3070081 : Nat := 350317155830246228370769

theorem tailTrace_3070081 : CollatzResearch.WordTrace tailWord_3070081 prefixEnd_3070081 350317155830246228370769 := by
  unfold tailWord_3070081
  simp only [CollatzResearch.WordTrace]
  refine ⟨111975053190628339936018097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74650035460418893290678731 111975053190628339936018097)
  ·
    refine ⟨83981289892971254952013573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111975053190628339936018097 83981289892971254952013573)
    ·
      refine ⟨15746491854932110303502545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83981289892971254952013573 15746491854932110303502545)
      ·
        refine ⟨11809868891199082727626909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15746491854932110303502545 11809868891199082727626909)
        ·
          refine ⟨4428700834199656022860091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11809868891199082727626909 4428700834199656022860091)
          ·
            refine ⟨6643051251299484034290137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428700834199656022860091 6643051251299484034290137)
            ·
              refine ⟨4982288438474613025717603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6643051251299484034290137 4982288438474613025717603)
              ·
                refine ⟨7473432657711919538576405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4982288438474613025717603 7473432657711919538576405)
                ·
                  refine ⟨350317155830246228370769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7473432657711919538576405 350317155830246228370769)
                  ·
                    rfl

theorem cell22_3070081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 6].length) (baseStart_3070081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070081 prefixEnd_3070081 := by exact prefixLift 3070081
  have htrace : WordTrace (prefixWord ++ tailWord_3070081) baseStart_3070081 baseEnd_3070081 := by
    simpa [prefixWord, tailWord_3070081, baseEnd_3070081] using wordTrace_append hprefix tailTrace_3070081
  have hstable : (prefixWord ++ tailWord_3070081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070081).length < 2 ^ (prefixWord ++ tailWord_3070081).sum := by decide
  have hdescent : baseEnd_3070081 < baseStart_3070081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070100 : List Nat := [2, 4, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_3070100 : Nat := 118140960795 + 3070100 * 2 ^ 59
def prefixEnd_3070100 : Nat := 4983230072969 + 3 ^ 40 * 3070100 * 2
def baseEnd_3070100 : Nat := 1050957971579028968887249

theorem tailTrace_3070100 : CollatzResearch.WordTrace tailWord_3070100 prefixEnd_3070100 1050957971579028968887249 := by
  unfold tailWord_3070100
  simp only [CollatzResearch.WordTrace]
  refine ⟨55987873088779753090479877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74650497451706337453973169 55987873088779753090479877)
  ·
    refine ⟨10497726204146203704464977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55987873088779753090479877 10497726204146203704464977)
    ·
      refine ⟨7873294653109652778348733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10497726204146203704464977 7873294653109652778348733)
      ·
        refine ⟨2952485494916119791880775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7873294653109652778348733 2952485494916119791880775)
        ·
          refine ⟨4428728242374179687821163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952485494916119791880775 4428728242374179687821163)
          ·
            refine ⟨6643092363561269531731745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428728242374179687821163 6643092363561269531731745)
            ·
              refine ⟨4982319272670952148798809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6643092363561269531731745 4982319272670952148798809)
              ·
                refine ⟨3736739454503214111599107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4982319272670952148798809 3736739454503214111599107)
                ·
                  refine ⟨5605109181754821167398661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736739454503214111599107 5605109181754821167398661)
                  ·
                    refine ⟨1050957971579028968887249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5605109181754821167398661 1050957971579028968887249)
                    ·
                      rfl

theorem cell22_3070100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_3070100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070100 prefixEnd_3070100 := by exact prefixLift 3070100
  have htrace : WordTrace (prefixWord ++ tailWord_3070100) baseStart_3070100 baseEnd_3070100 := by
    simpa [prefixWord, tailWord_3070100, baseEnd_3070100] using wordTrace_append hprefix tailTrace_3070100
  have hstable : (prefixWord ++ tailWord_3070100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070100).length < 2 ^ (prefixWord ++ tailWord_3070100).sum := by decide
  have hdescent : baseEnd_3070100 < baseStart_3070100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070107 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 2, 7]
def baseStart_3070107 : Nat := 118140960795 + 3070107 * 2 ^ 59
def prefixEnd_3070107 : Nat := 4983230072969 + 3 ^ 40 * 3070107 * 2
def baseEnd_3070107 : Nat := 1050960367822083283962227

theorem tailTrace_3070107 : CollatzResearch.WordTrace tailWord_3070107 prefixEnd_3070107 1050960367822083283962227 := by
  unfold tailWord_3070107
  simp only [CollatzResearch.WordTrace]
  refine ⟨111976001488534146376464575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74650667659022764250976383 111976001488534146376464575)
  ·
    refine ⟨167964002232801219564696863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111976001488534146376464575 167964002232801219564696863)
    ·
      refine ⟨251946003349201829347045295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167964002232801219564696863 251946003349201829347045295)
      ·
        refine ⟨377919005023802744020567943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251946003349201829347045295 377919005023802744020567943)
        ·
          refine ⟨566878507535704116030851915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377919005023802744020567943 566878507535704116030851915)
          ·
            refine ⟨850317761303556174046277873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566878507535704116030851915 850317761303556174046277873)
            ·
              refine ⟨637738320977667130534708405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850317761303556174046277873 637738320977667130534708405)
              ·
                refine ⟨59787967591656293487628913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 637738320977667130534708405 59787967591656293487628913)
                ·
                  refine ⟨44840975693742220115721685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59787967591656293487628913 44840975693742220115721685)
                  ·
                    refine ⟨1050960367822083283962227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44840975693742220115721685 1050960367822083283962227)
                    ·
                      rfl

theorem cell22_3070107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_3070107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070107 prefixEnd_3070107 := by exact prefixLift 3070107
  have htrace : WordTrace (prefixWord ++ tailWord_3070107) baseStart_3070107 baseEnd_3070107 := by
    simpa [prefixWord, tailWord_3070107, baseEnd_3070107] using wordTrace_append hprefix tailTrace_3070107
  have hstable : (prefixWord ++ tailWord_3070107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070107).length < 2 ^ (prefixWord ++ tailWord_3070107).sum := by decide
  have hdescent : baseEnd_3070107 < baseStart_3070107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070109 : List Nat := [1, 4, 2, 1, 1, 4, 1, 8]
def baseStart_3070109 : Nat := 118140960795 + 3070109 * 2 ^ 59
def prefixEnd_3070109 : Nat := 4983230072969 + 3 ^ 40 * 3070109 * 2
def baseEnd_3070109 : Nat := 116773450273661771712469

theorem tailTrace_3070109 : CollatzResearch.WordTrace tailWord_3070109 prefixEnd_3070109 116773450273661771712469 := by
  unfold tailWord_3070109
  simp only [CollatzResearch.WordTrace]
  refine ⟨111976074434526900718037381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74650716289684600478691587 111976074434526900718037381)
  ·
    refine ⟨20995513956473793884632009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111976074434526900718037381 20995513956473793884632009)
    ·
      refine ⟨15746635467355345413474007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20995513956473793884632009 15746635467355345413474007)
      ·
        refine ⟨23619953201033018120211011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15746635467355345413474007 23619953201033018120211011)
        ·
          refine ⟨35429929801549527180316517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23619953201033018120211011 35429929801549527180316517)
          ·
            refine ⟨6643111837790536346309347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35429929801549527180316517 6643111837790536346309347)
            ·
              refine ⟨9964667756685804519464021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6643111837790536346309347 9964667756685804519464021)
              ·
                refine ⟨116773450273661771712469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9964667756685804519464021 116773450273661771712469)
                ·
                  rfl

theorem cell22_3070109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 8].length) (baseStart_3070109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070109 prefixEnd_3070109 := by exact prefixLift 3070109
  have htrace : WordTrace (prefixWord ++ tailWord_3070109) baseStart_3070109 baseEnd_3070109 := by
    simpa [prefixWord, tailWord_3070109, baseEnd_3070109] using wordTrace_append hprefix tailTrace_3070109
  have hstable : (prefixWord ++ tailWord_3070109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070109).length < 2 ^ (prefixWord ++ tailWord_3070109).sum := by decide
  have hdescent : baseEnd_3070109 < baseStart_3070109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070132 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 6]
def baseStart_3070132 : Nat := 118140960795 + 3070132 * 2 ^ 59
def prefixEnd_3070132 : Nat := 4983230072969 + 3 ^ 40 * 3070132 * 2
def baseEnd_3070132 : Nat := 350322975277663850695717

theorem tailTrace_3070132 : CollatzResearch.WordTrace tailWord_3070132 prefixEnd_3070132 350322975277663850695717 := by
  unfold tailWord_3070132
  simp only [CollatzResearch.WordTrace]
  refine ⟨55988456656721787823062325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74651275542295717097416433 55988456656721787823062325)
  ·
    refine ⟨5248917811567667608412093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55988456656721787823062325 5248917811567667608412093)
    ·
      refine ⟨1968344179337875353154535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5248917811567667608412093 1968344179337875353154535)
      ·
        refine ⟨2952516269006813029731803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1968344179337875353154535 2952516269006813029731803)
        ·
          refine ⟨4428774403510219544597705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952516269006813029731803 4428774403510219544597705)
          ·
            refine ⟨3321580802632664658448279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4428774403510219544597705 3321580802632664658448279)
            ·
              refine ⟨4982371203948996987672419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321580802632664658448279 4982371203948996987672419)
              ·
                refine ⟨7473556805923495481508629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4982371203948996987672419 7473556805923495481508629)
                ·
                  refine ⟨350322975277663850695717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7473556805923495481508629 350322975277663850695717)
                  ·
                    rfl

theorem cell22_3070132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_3070132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070132 prefixEnd_3070132 := by exact prefixLift 3070132
  have htrace : WordTrace (prefixWord ++ tailWord_3070132) baseStart_3070132 baseEnd_3070132 := by
    simpa [prefixWord, tailWord_3070132, baseEnd_3070132] using wordTrace_append hprefix tailTrace_3070132
  have hstable : (prefixWord ++ tailWord_3070132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070132).length < 2 ^ (prefixWord ++ tailWord_3070132).sum := by decide
  have hdescent : baseEnd_3070132 < baseStart_3070132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070216 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 6]
def baseStart_3070216 : Nat := 118140960795 + 3070216 * 2 ^ 59
def prefixEnd_3070216 : Nat := 4983230072969 + 3 ^ 40 * 3070216 * 2
def baseEnd_3070216 : Nat := 350332560249881110995631

theorem tailTrace_3070216 : CollatzResearch.WordTrace tailWord_3070216 prefixEnd_3070216 350332560249881110995631 := by
  unfold tailWord_3070216
  simp only [CollatzResearch.WordTrace]
  refine ⟨55989988522569628996091251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74653318030092838661455001 55989988522569628996091251)
  ·
    refine ⟨83984982783854443494136877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55989988522569628996091251 83984982783854443494136877)
    ·
      refine ⟨31494368543945416310301329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83984982783854443494136877 31494368543945416310301329)
      ·
        refine ⟨23620776407959062232725997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31494368543945416310301329 23620776407959062232725997)
        ·
          refine ⟨8857791152984648337272249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23620776407959062232725997 8857791152984648337272249)
          ·
            refine ⟨6643343364738486252954187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8857791152984648337272249 6643343364738486252954187)
            ·
              refine ⟨9965015047107729379431281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6643343364738486252954187 9965015047107729379431281)
              ·
                refine ⟨7473761285330797034573461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9965015047107729379431281 7473761285330797034573461)
                ·
                  refine ⟨350332560249881110995631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7473761285330797034573461 350332560249881110995631)
                  ·
                    rfl

theorem cell22_3070216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 6].length) (baseStart_3070216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070216 prefixEnd_3070216 := by exact prefixLift 3070216
  have htrace : WordTrace (prefixWord ++ tailWord_3070216) baseStart_3070216 baseEnd_3070216 := by
    simpa [prefixWord, tailWord_3070216, baseEnd_3070216] using wordTrace_append hprefix tailTrace_3070216
  have hstable : (prefixWord ++ tailWord_3070216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070216).length < 2 ^ (prefixWord ++ tailWord_3070216).sum := by decide
  have hdescent : baseEnd_3070216 < baseStart_3070216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070231 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 1, 5]
def baseStart_3070231 : Nat := 118140960795 + 3070231 * 2 ^ 59
def prefixEnd_3070231 : Nat := 4983230072969 + 3 ^ 40 * 3070231 * 2
def baseEnd_3070231 : Nat := 1051002815556188293861847

theorem tailTrace_3070231 : CollatzResearch.WordTrace tailWord_3070231 prefixEnd_3070231 1051002815556188293861847 := by
  unfold tailWord_3070231
  simp only [CollatzResearch.WordTrace]
  refine ⟨111980524140084915553978547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74653682760056610369319031 111980524140084915553978547)
  ·
    refine ⟨167970786210127373330967821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111980524140084915553978547 167970786210127373330967821)
    ·
      refine ⟨62989044828797764999112933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167970786210127373330967821 62989044828797764999112933)
      ·
        refine ⟨11810445905399580937333675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62989044828797764999112933 11810445905399580937333675)
        ·
          refine ⟨17715668858099371406000513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11810445905399580937333675 17715668858099371406000513)
          ·
            refine ⟨13286751643574528554500385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17715668858099371406000513 13286751643574528554500385)
            ·
              refine ⟨9965063732680896415875289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13286751643574528554500385 9965063732680896415875289)
              ·
                refine ⟨7473797799510672311906467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9965063732680896415875289 7473797799510672311906467)
                ·
                  refine ⟨11210696699266008467859701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7473797799510672311906467 11210696699266008467859701)
                  ·
                    refine ⟨1051002815556188293861847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11210696699266008467859701 1051002815556188293861847)
                    ·
                      rfl

theorem cell22_3070231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_3070231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070231 prefixEnd_3070231 := by exact prefixLift 3070231
  have htrace : WordTrace (prefixWord ++ tailWord_3070231) baseStart_3070231 baseEnd_3070231 := by
    simpa [prefixWord, tailWord_3070231, baseEnd_3070231] using wordTrace_append hprefix tailTrace_3070231
  have hstable : (prefixWord ++ tailWord_3070231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070231).length < 2 ^ (prefixWord ++ tailWord_3070231).sum := by decide
  have hdescent : baseEnd_3070231 < baseStart_3070231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070404 : List Nat := [2, 3, 3, 2, 2, 2, 2, 1, 1, 4]
def baseStart_3070404 : Nat := 118140960795 + 3070404 * 2 ^ 59
def prefixEnd_3070404 : Nat := 4983230072969 + 3 ^ 40 * 3070404 * 2
def baseEnd_3070404 : Nat := 1051062036991673509286317

theorem tailTrace_3070404 : CollatzResearch.WordTrace tailWord_3070404 prefixEnd_3070404 1051062036991673509286317 := by
  unfold tailWord_3070404
  simp only [CollatzResearch.WordTrace]
  refine ⟨55993416984229083050013133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74657889312305444066684177 55993416984229083050013133)
  ·
    refine ⟨20997531369085906143754925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55993416984229083050013133 20997531369085906143754925)
    ·
      refine ⟨7874074263407214803908097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20997531369085906143754925 7874074263407214803908097)
      ·
        refine ⟨5905555697555411102931073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7874074263407214803908097 5905555697555411102931073)
        ·
          refine ⟨4429166773166558327198305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5905555697555411102931073 4429166773166558327198305)
          ·
            refine ⟨3321875079874918745398729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4429166773166558327198305 3321875079874918745398729)
            ·
              refine ⟨2491406309906189059049047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3321875079874918745398729 2491406309906189059049047)
              ·
                refine ⟨3737109464859283588573571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491406309906189059049047 3737109464859283588573571)
                ·
                  refine ⟨5605664197288925382860357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3737109464859283588573571 5605664197288925382860357)
                  ·
                    refine ⟨1051062036991673509286317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5605664197288925382860357 1051062036991673509286317)
                    ·
                      rfl

theorem cell22_3070404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_3070404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070404 prefixEnd_3070404 := by exact prefixLift 3070404
  have htrace : WordTrace (prefixWord ++ tailWord_3070404) baseStart_3070404 baseEnd_3070404 := by
    simpa [prefixWord, tailWord_3070404, baseEnd_3070404] using wordTrace_append hprefix tailTrace_3070404
  have hstable : (prefixWord ++ tailWord_3070404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070404).length < 2 ^ (prefixWord ++ tailWord_3070404).sum := by decide
  have hdescent : baseEnd_3070404 < baseStart_3070404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070434 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3070434 : Nat := 118140960795 + 3070434 * 2 ^ 59
def prefixEnd_3070434 : Nat := 4983230072969 + 3 ^ 40 * 3070434 * 2
def baseEnd_3070434 : Nat := 1051072306604763431036225

theorem tailTrace_3070434 : CollatzResearch.WordTrace tailWord_3070434 prefixEnd_3070434 1051072306604763431036225 := by
  unfold tailWord_3070434
  simp only [CollatzResearch.WordTrace]
  refine ⟨27996982039587370305904589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74658618772232987482412237 27996982039587370305904589)
  ·
    refine ⟨10498868264845263864714221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27996982039587370305904589 10498868264845263864714221)
    ·
      refine ⟨3937075599316973949267833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10498868264845263864714221 3937075599316973949267833)
      ·
        refine ⟨2952806699487730461950875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3937075599316973949267833 2952806699487730461950875)
        ·
          refine ⟨4429210049231595692926313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952806699487730461950875 4429210049231595692926313)
          ·
            refine ⟨3321907536923696769694735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4429210049231595692926313 3321907536923696769694735)
            ·
              refine ⟨4982861305385545154542103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321907536923696769694735 4982861305385545154542103)
              ·
                refine ⟨7474291958078317731813155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4982861305385545154542103 7474291958078317731813155)
                ·
                  refine ⟨11211437937117476597719733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7474291958078317731813155 11211437937117476597719733)
                  ·
                    refine ⟨1051072306604763431036225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11211437937117476597719733 1051072306604763431036225)
                    ·
                      rfl

theorem cell22_3070434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3070434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070434 prefixEnd_3070434 := by exact prefixLift 3070434
  have htrace : WordTrace (prefixWord ++ tailWord_3070434) baseStart_3070434 baseEnd_3070434 := by
    simpa [prefixWord, tailWord_3070434, baseEnd_3070434] using wordTrace_append hprefix tailTrace_3070434
  have hstable : (prefixWord ++ tailWord_3070434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070434).length < 2 ^ (prefixWord ++ tailWord_3070434).sum := by decide
  have hdescent : baseEnd_3070434 < baseStart_3070434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070492 : List Nat := [2, 2, 3, 1, 2, 4, 2, 1, 5]
def baseStart_3070492 : Nat := 118140960795 + 3070492 * 2 ^ 59
def prefixEnd_3070492 : Nat := 4983230072969 + 3 ^ 40 * 3070492 * 2
def baseEnd_3070492 : Nat := 350364053730023537695349

theorem tailTrace_3070492 : CollatzResearch.WordTrace tailWord_3070492 prefixEnd_3070492 350364053730023537695349 := by
  unfold tailWord_3070492
  simp only [CollatzResearch.WordTrace]
  refine ⟨55995021796069678564614865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74660029061426238086153153 55995021796069678564614865)
  ·
    refine ⟨41996266347052258923461149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55995021796069678564614865 41996266347052258923461149)
    ·
      refine ⟨15748599880144597096297931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41996266347052258923461149 15748599880144597096297931)
      ·
        refine ⟨23622899820216895644446897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15748599880144597096297931 23622899820216895644446897)
        ·
          refine ⟨17717174865162671733335173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23622899820216895644446897 17717174865162671733335173)
          ·
            refine ⟨3321970287218000950000345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17717174865162671733335173 3321970287218000950000345)
            ·
              refine ⟨2491477715413500712500259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3321970287218000950000345 2491477715413500712500259)
              ·
                refine ⟨3737216573120251068750389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491477715413500712500259 3737216573120251068750389)
                ·
                  refine ⟨350364053730023537695349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3737216573120251068750389 350364053730023537695349)
                  ·
                    rfl

theorem cell22_3070492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_3070492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070492 prefixEnd_3070492 := by exact prefixLift 3070492
  have htrace : WordTrace (prefixWord ++ tailWord_3070492) baseStart_3070492 baseEnd_3070492 := by
    simpa [prefixWord, tailWord_3070492, baseEnd_3070492] using wordTrace_append hprefix tailTrace_3070492
  have hstable : (prefixWord ++ tailWord_3070492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070492).length < 2 ^ (prefixWord ++ tailWord_3070492).sum := by decide
  have hdescent : baseEnd_3070492 < baseStart_3070492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070520 : List Nat := [2, 1, 2, 1, 4, 1, 2, 5, 4]
def baseStart_3070520 : Nat := 118140960795 + 3070520 * 2 ^ 59
def prefixEnd_3070520 : Nat := 4983230072969 + 3 ^ 40 * 3070520 * 2
def baseEnd_3070520 : Nat := 350367248720762624461987

theorem tailTrace_3070520 : CollatzResearch.WordTrace tailWord_3070520 prefixEnd_3070520 350367248720762624461987 := by
  unfold tailWord_3070520
  simp only [CollatzResearch.WordTrace]
  refine ⟨55995532418018958955624507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74660709890691945274166009 55995532418018958955624507)
  ·
    refine ⟨83993298627028438433436761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55995532418018958955624507 83993298627028438433436761)
    ·
      refine ⟨62994973970271328825077571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83993298627028438433436761 62994973970271328825077571)
      ·
        refine ⟨94492460955406993237616357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62994973970271328825077571 94492460955406993237616357)
        ·
          refine ⟨17717336429138811232053067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94492460955406993237616357 17717336429138811232053067)
          ·
            refine ⟨26576004643708216848079601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17717336429138811232053067 26576004643708216848079601)
            ·
              refine ⟨19932003482781162636059701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26576004643708216848079601 19932003482781162636059701)
              ·
                refine ⟨1868625326510733997130597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19932003482781162636059701 1868625326510733997130597)
                ·
                  refine ⟨350367248720762624461987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1868625326510733997130597 350367248720762624461987)
                  ·
                    rfl

theorem cell22_3070520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 4].length) (baseStart_3070520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070520 prefixEnd_3070520 := by exact prefixLift 3070520
  have htrace : WordTrace (prefixWord ++ tailWord_3070520) baseStart_3070520 baseEnd_3070520 := by
    simpa [prefixWord, tailWord_3070520, baseEnd_3070520] using wordTrace_append hprefix tailTrace_3070520
  have hstable : (prefixWord ++ tailWord_3070520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070520).length < 2 ^ (prefixWord ++ tailWord_3070520).sum := by decide
  have hdescent : baseEnd_3070520 < baseStart_3070520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070522 : List Nat := [3, 1, 1, 1, 3, 4, 3, 1, 1, 4]
def baseStart_3070522 : Nat := 118140960795 + 3070522 * 2 ^ 59
def prefixEnd_3070522 : Nat := 4983230072969 + 3 ^ 40 * 3070522 * 2
def baseEnd_3070522 : Nat := 1051102430803160534835955

theorem tailTrace_3070522 : CollatzResearch.WordTrace tailWord_3070522 prefixEnd_3070522 1051102430803160534835955 := by
  unfold tailWord_3070522
  simp only [CollatzResearch.WordTrace]
  refine ⟨27997784445507668063205455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74660758521353781501881213 27997784445507668063205455)
  ·
    refine ⟨41996676668261502094808183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27997784445507668063205455 41996676668261502094808183)
    ·
      refine ⟨62995015002392253142212275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41996676668261502094808183 62995015002392253142212275)
      ·
        refine ⟨94492522503588379713318413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62995015002392253142212275 94492522503588379713318413)
        ·
          refine ⟨35434695938845642392494405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94492522503588379713318413 35434695938845642392494405)
          ·
            refine ⟨6644005488533557948592701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35434695938845642392494405 6644005488533557948592701)
            ·
              refine ⟨2491502058200084230722263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6644005488533557948592701 2491502058200084230722263)
              ·
                refine ⟨3737253087300126346083395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491502058200084230722263 3737253087300126346083395)
                ·
                  refine ⟨5605879630950189519125093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3737253087300126346083395 5605879630950189519125093)
                  ·
                    refine ⟨1051102430803160534835955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5605879630950189519125093 1051102430803160534835955)
                    ·
                      rfl

theorem cell22_3070522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_3070522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070522 prefixEnd_3070522 := by exact prefixLift 3070522
  have htrace : WordTrace (prefixWord ++ tailWord_3070522) baseStart_3070522 baseEnd_3070522 := by
    simpa [prefixWord, tailWord_3070522, baseEnd_3070522] using wordTrace_append hprefix tailTrace_3070522
  have hstable : (prefixWord ++ tailWord_3070522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070522).length < 2 ^ (prefixWord ++ tailWord_3070522).sum := by decide
  have hdescent : baseEnd_3070522 < baseStart_3070522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070597 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 3, 3]
def baseStart_3070597 : Nat := 118140960795 + 3070597 * 2 ^ 59
def prefixEnd_3070597 : Nat := 4983230072969 + 3 ^ 40 * 3070597 * 2
def baseEnd_3070597 : Nat := 1051128104835885339210725

theorem tailTrace_3070597 : CollatzResearch.WordTrace tailWord_3070597 prefixEnd_3070597 1051128104835885339210725 := by
  unfold tailWord_3070597
  simp only [CollatzResearch.WordTrace]
  refine ⟨111993873256758960061802045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74662582171172640041201363 111993873256758960061802045)
  ·
    refine ⟨41997702471284610023175767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111993873256758960061802045 41997702471284610023175767)
    ·
      refine ⟨62996553706926915034763651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41997702471284610023175767 62996553706926915034763651)
      ·
        refine ⟨94494830560390372552145477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62996553706926915034763651 94494830560390372552145477)
        ·
          refine ⟨17717780730073194853527277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94494830560390372552145477 17717780730073194853527277)
          ·
            refine ⟨6644167773777448070072729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17717780730073194853527277 6644167773777448070072729)
            ·
              refine ⟨4983125830333086052554547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6644167773777448070072729 4983125830333086052554547)
              ·
                refine ⟨7474688745499629078831821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4983125830333086052554547 7474688745499629078831821)
                ·
                  refine ⟨2803008279562360904561933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7474688745499629078831821 2803008279562360904561933)
                  ·
                    refine ⟨1051128104835885339210725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2803008279562360904561933 1051128104835885339210725)
                    ·
                      rfl

theorem cell22_3070597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_3070597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070597 prefixEnd_3070597 := by exact prefixLift 3070597
  have htrace : WordTrace (prefixWord ++ tailWord_3070597) baseStart_3070597 baseEnd_3070597 := by
    simpa [prefixWord, tailWord_3070597, baseEnd_3070597] using wordTrace_append hprefix tailTrace_3070597
  have hstable : (prefixWord ++ tailWord_3070597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070597).length < 2 ^ (prefixWord ++ tailWord_3070597).sum := by decide
  have hdescent : baseEnd_3070597 < baseStart_3070597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070655 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 6]
def baseStart_3070655 : Nat := 118140960795 + 3070655 * 2 ^ 59
def prefixEnd_3070655 : Nat := 4983230072969 + 3 ^ 40 * 3070655 * 2
def baseEnd_3070655 : Nat := 350382653140397507086849

theorem tailTrace_3070655 : CollatzResearch.WordTrace tailWord_3070655 prefixEnd_3070655 350382653140397507086849 := by
  unfold tailWord_3070655
  simp only [CollatzResearch.WordTrace]
  refine ⟨111995988690548835967413419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74663992460365890644942279 111995988690548835967413419)
  ·
    refine ⟨167993983035823253951120129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111995988690548835967413419 167993983035823253951120129)
    ·
      refine ⟨125995487276867440463340097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167993983035823253951120129 125995487276867440463340097)
      ·
        refine ⟨94496615457650580347505073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125995487276867440463340097 94496615457650580347505073)
        ·
          refine ⟨70872461593237935260628805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94496615457650580347505073 70872461593237935260628805)
          ·
            refine ⟨13288586548732112861367901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70872461593237935260628805 13288586548732112861367901)
            ·
              refine ⟨4983219955774542323012963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13288586548732112861367901 4983219955774542323012963)
              ·
                refine ⟨7474829933661813484519445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4983219955774542323012963 7474829933661813484519445)
                ·
                  refine ⟨350382653140397507086849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7474829933661813484519445 350382653140397507086849)
                  ·
                    rfl

theorem cell22_3070655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 6].length) (baseStart_3070655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070655 prefixEnd_3070655 := by exact prefixLift 3070655
  have htrace : WordTrace (prefixWord ++ tailWord_3070655) baseStart_3070655 baseEnd_3070655 := by
    simpa [prefixWord, tailWord_3070655, baseEnd_3070655] using wordTrace_append hprefix tailTrace_3070655
  have hstable : (prefixWord ++ tailWord_3070655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070655).length < 2 ^ (prefixWord ++ tailWord_3070655).sum := by decide
  have hdescent : baseEnd_3070655 < baseStart_3070655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070702 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3070702 : Nat := 118140960795 + 3070702 * 2 ^ 59
def prefixEnd_3070702 : Nat := 4983230072969 + 3 ^ 40 * 3070702 * 2
def baseEnd_3070702 : Nat := 1051164048481700065335403

theorem tailTrace_3070702 : CollatzResearch.WordTrace tailWord_3070702 prefixEnd_3070702 1051164048481700065335403 := by
  unfold tailWord_3070702
  simp only [CollatzResearch.WordTrace]
  refine ⟨13999712865172320374296795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74665135280919041996249573 13999712865172320374296795)
  ·
    refine ⟨20999569297758480561445193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13999712865172320374296795 20999569297758480561445193)
    ·
      refine ⟨15749676973318860421083895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20999569297758480561445193 15749676973318860421083895)
      ·
        refine ⟨23624515459978290631625843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15749676973318860421083895 23624515459978290631625843)
        ·
          refine ⟨35436773189967435947438765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23624515459978290631625843 35436773189967435947438765)
          ·
            refine ⟨13288789946237788480289537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35436773189967435947438765 13288789946237788480289537)
            ·
              refine ⟨9966592459678341360217153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13288789946237788480289537 9966592459678341360217153)
              ·
                refine ⟨7474944344758756020162865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9966592459678341360217153 7474944344758756020162865)
                ·
                  refine ⟨5606208258569067015122149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7474944344758756020162865 5606208258569067015122149)
                  ·
                    refine ⟨1051164048481700065335403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5606208258569067015122149 1051164048481700065335403)
                    ·
                      rfl

theorem cell22_3070702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3070702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070702 prefixEnd_3070702 := by exact prefixLift 3070702
  have htrace : WordTrace (prefixWord ++ tailWord_3070702) baseStart_3070702 baseEnd_3070702 := by
    simpa [prefixWord, tailWord_3070702, baseEnd_3070702] using wordTrace_append hprefix tailTrace_3070702
  have hstable : (prefixWord ++ tailWord_3070702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070702).length < 2 ^ (prefixWord ++ tailWord_3070702).sum := by decide
  have hdescent : baseEnd_3070702 < baseStart_3070702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070706 : List Nat := [3, 2, 1, 3, 1, 4, 2, 2, 4]
def baseStart_3070706 : Nat := 118140960795 + 3070706 * 2 ^ 59
def prefixEnd_3070706 : Nat := 4983230072969 + 3 ^ 40 * 3070706 * 2
def baseEnd_3070706 : Nat := 350388472587815129411797

theorem tailTrace_3070706 : CollatzResearch.WordTrace tailWord_3070706 prefixEnd_3070706 350388472587815129411797 := by
  unfold tailWord_3070706
  simp only [CollatzResearch.WordTrace]
  refine ⟨27999462203341017919379993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74665232542242714451679981 27999462203341017919379993)
  ·
    refine ⟨20999596652505763439534995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27999462203341017919379993 20999596652505763439534995)
    ·
      refine ⟨31499394978758645159302493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20999596652505763439534995 31499394978758645159302493)
      ·
        refine ⟨11812273117034491934738435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31499394978758645159302493 11812273117034491934738435)
        ·
          refine ⟨17718409675551737902107653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11812273117034491934738435 17718409675551737902107653)
          ·
            refine ⟨3322201814165950856645185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17718409675551737902107653 3322201814165950856645185)
            ·
              refine ⟨2491651360624463142483889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3322201814165950856645185 2491651360624463142483889)
              ·
                refine ⟨1868738520468347356862917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2491651360624463142483889 1868738520468347356862917)
                ·
                  refine ⟨350388472587815129411797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1868738520468347356862917 350388472587815129411797)
                  ·
                    rfl

theorem cell22_3070706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_3070706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070706 prefixEnd_3070706 := by exact prefixLift 3070706
  have htrace : WordTrace (prefixWord ++ tailWord_3070706) baseStart_3070706 baseEnd_3070706 := by
    simpa [prefixWord, tailWord_3070706, baseEnd_3070706] using wordTrace_append hprefix tailTrace_3070706
  have hstable : (prefixWord ++ tailWord_3070706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070706).length < 2 ^ (prefixWord ++ tailWord_3070706).sum := by decide
  have hdescent : baseEnd_3070706 < baseStart_3070706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070730 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_3070730 : Nat := 118140960795 + 3070730 * 2 ^ 59
def prefixEnd_3070730 : Nat := 4983230072969 + 3 ^ 40 * 3070730 * 2
def baseEnd_3070730 : Nat := 1051173633453917325635317

theorem tailTrace_3070730 : CollatzResearch.WordTrace tailWord_3070730 prefixEnd_3070730 1051173633453917325635317 := by
  unfold tailWord_3070730
  simp only [CollatzResearch.WordTrace]
  refine ⟨27999681041319280944098411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74665816110184749184262429 27999681041319280944098411)
  ·
    refine ⟨41999521561978921416147617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27999681041319280944098411 41999521561978921416147617)
    ·
      refine ⟨31499641171484191062110713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41999521561978921416147617 31499641171484191062110713)
      ·
        refine ⟨23624730878613143296583035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31499641171484191062110713 23624730878613143296583035)
        ·
          refine ⟨35437096317919714944874553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23624730878613143296583035 35437096317919714944874553)
          ·
            refine ⟨26577822238439786208655915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35437096317919714944874553 26577822238439786208655915)
            ·
              refine ⟨39866733357659679312983873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26577822238439786208655915 39866733357659679312983873)
              ·
                refine ⟨29900050018244759484737905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39866733357659679312983873 29900050018244759484737905)
                ·
                  refine ⟨22425037513683569613553429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29900050018244759484737905 22425037513683569613553429)
                  ·
                    refine ⟨1051173633453917325635317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22425037513683569613553429 1051173633453917325635317)
                    ·
                      rfl

theorem cell22_3070730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_3070730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070730 prefixEnd_3070730 := by exact prefixLift 3070730
  have htrace : WordTrace (prefixWord ++ tailWord_3070730) baseStart_3070730 baseEnd_3070730 := by
    simpa [prefixWord, tailWord_3070730, baseEnd_3070730] using wordTrace_append hprefix tailTrace_3070730
  have hstable : (prefixWord ++ tailWord_3070730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070730).length < 2 ^ (prefixWord ++ tailWord_3070730).sum := by decide
  have hdescent : baseEnd_3070730 < baseStart_3070730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070766 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_3070766 : Nat := 118140960795 + 3070766 * 2 ^ 59
def prefixEnd_3070766 : Nat := 4983230072969 + 3 ^ 40 * 3070766 * 2
def baseEnd_3070766 : Nat := 1051185956989625231735207

theorem tailTrace_3070766 : CollatzResearch.WordTrace tailWord_3070766 prefixEnd_3070766 1051185956989625231735207 := by
  unfold tailWord_3070766
  simp only [CollatzResearch.WordTrace]
  refine ⟨14000004649143337740588019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74666691462097801283136101 14000004649143337740588019)
  ·
    refine ⟨21000006973715006610882029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14000004649143337740588019 21000006973715006610882029)
    ·
      refine ⟨7875002615143127479080761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21000006973715006610882029 7875002615143127479080761)
      ·
        refine ⟨5906251961357345609310571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7875002615143127479080761 5906251961357345609310571)
        ·
          refine ⟨8859377942036018413965857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5906251961357345609310571 8859377942036018413965857)
          ·
            refine ⟨6644533456527013810474393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8859377942036018413965857 6644533456527013810474393)
            ·
              refine ⟨4983400092395260357855795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6644533456527013810474393 4983400092395260357855795)
              ·
                refine ⟨7475100138592890536783693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4983400092395260357855795 7475100138592890536783693)
                ·
                  refine ⟨2803162551972333951293885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7475100138592890536783693 2803162551972333951293885)
                  ·
                    refine ⟨1051185956989625231735207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2803162551972333951293885 1051185956989625231735207)
                    ·
                      rfl

theorem cell22_3070766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_3070766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070766 prefixEnd_3070766 := by exact prefixLift 3070766
  have htrace : WordTrace (prefixWord ++ tailWord_3070766) baseStart_3070766 baseEnd_3070766 := by
    simpa [prefixWord, tailWord_3070766, baseEnd_3070766] using wordTrace_append hprefix tailTrace_3070766
  have hstable : (prefixWord ++ tailWord_3070766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070766).length < 2 ^ (prefixWord ++ tailWord_3070766).sum := by decide
  have hdescent : baseEnd_3070766 < baseStart_3070766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070824 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 6]
def baseStart_3070824 : Nat := 118140960795 + 3070824 * 2 ^ 59
def prefixEnd_3070824 : Nat := 4983230072969 + 3 ^ 40 * 3070824 * 2
def baseEnd_3070824 : Nat := 350401937191644137928343

theorem tailTrace_3070824 : CollatzResearch.WordTrace tailWord_3070824 prefixEnd_3070824 350401937191644137928343 := by
  unfold tailWord_3070824
  simp only [CollatzResearch.WordTrace]
  refine ⟨56001076313468288915157763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74668101751291051886877017 56001076313468288915157763)
  ·
    refine ⟨84001614470202433372736645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56001076313468288915157763 84001614470202433372736645)
    ·
      refine ⟨15750302713162956257388121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84001614470202433372736645 15750302713162956257388121)
      ·
        refine ⟨11812727034872217193041091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15750302713162956257388121 11812727034872217193041091)
        ·
          refine ⟨17719090552308325789561637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11812727034872217193041091 17719090552308325789561637)
          ·
            refine ⟨3322329478557811085542807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17719090552308325789561637 3322329478557811085542807)
            ·
              refine ⟨4983494217836716628314211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3322329478557811085542807 4983494217836716628314211)
              ·
                refine ⟨7475241326755074942471317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4983494217836716628314211 7475241326755074942471317)
                ·
                  refine ⟨350401937191644137928343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7475241326755074942471317 350401937191644137928343)
                  ·
                    rfl

theorem cell22_3070824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 6].length) (baseStart_3070824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070824 prefixEnd_3070824 := by exact prefixLift 3070824
  have htrace : WordTrace (prefixWord ++ tailWord_3070824) baseStart_3070824 baseEnd_3070824 := by
    simpa [prefixWord, tailWord_3070824, baseEnd_3070824] using wordTrace_append hprefix tailTrace_3070824
  have hstable : (prefixWord ++ tailWord_3070824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070824).length < 2 ^ (prefixWord ++ tailWord_3070824).sum := by decide
  have hdescent : baseEnd_3070824 < baseStart_3070824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070835 : List Nat := [1, 1, 1, 2, 2, 1, 5, 9]
def baseStart_3070835 : Nat := 118140960795 + 3070835 * 2 ^ 59
def prefixEnd_3070835 : Nat := 4983230072969 + 3 ^ 40 * 3070835 * 2
def baseEnd_3070835 : Nat := 116801064122192450195555

theorem tailTrace_3070835 : CollatzResearch.WordTrace tailWord_3070835 prefixEnd_3070835 116801064122192450195555 := by
  unfold tailWord_3070835
  simp only [CollatzResearch.WordTrace]
  refine ⟨112002553829896726708965959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74668369219931151139310639 112002553829896726708965959)
  ·
    refine ⟨168003830744845090063448939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112002553829896726708965959 168003830744845090063448939)
    ·
      refine ⟨252005746117267635095173409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168003830744845090063448939 252005746117267635095173409)
      ·
        refine ⟨189004309587950726321380057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252005746117267635095173409 189004309587950726321380057)
        ·
          refine ⟨141753232190963044741035043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189004309587950726321380057 141753232190963044741035043)
          ·
            refine ⟨212629848286444567111552565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141753232190963044741035043 212629848286444567111552565)
            ·
              refine ⟨19934048276854178166708053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212629848286444567111552565 19934048276854178166708053)
              ·
                refine ⟨116801064122192450195555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19934048276854178166708053 116801064122192450195555)
                ·
                  rfl

theorem cell22_3070835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 9].length) (baseStart_3070835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070835 prefixEnd_3070835 := by exact prefixLift 3070835
  have htrace : WordTrace (prefixWord ++ tailWord_3070835) baseStart_3070835 baseEnd_3070835 := by
    simpa [prefixWord, tailWord_3070835, baseEnd_3070835] using wordTrace_append hprefix tailTrace_3070835
  have hstable : (prefixWord ++ tailWord_3070835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070835).length < 2 ^ (prefixWord ++ tailWord_3070835).sum := by decide
  have hdescent : baseEnd_3070835 < baseStart_3070835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070867 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 7, 3]
def baseStart_3070867 : Nat := 118140960795 + 3070867 * 2 ^ 59
def prefixEnd_3070867 : Nat := 4983230072969 + 3 ^ 40 * 3070867 * 2
def baseEnd_3070867 : Nat := 1051220531353694634959897

theorem tailTrace_3070867 : CollatzResearch.WordTrace tailWord_3070867 prefixEnd_3070867 1051220531353694634959897 := by
  unfold tailWord_3070867
  simp only [CollatzResearch.WordTrace]
  refine ⟨112003720965780796174130855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74669147310520530782753903 112003720965780796174130855)
  ·
    refine ⟨168005581448671194261196283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112003720965780796174130855 168005581448671194261196283)
    ·
      refine ⟨252008372173006791391794425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168005581448671194261196283 252008372173006791391794425)
      ·
        refine ⟨189006279129755093543845819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252008372173006791391794425 189006279129755093543845819)
        ·
          refine ⟨283509418694632640315768729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189006279129755093543845819 283509418694632640315768729)
          ·
            refine ⟨212632064020974480236826547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283509418694632640315768729 212632064020974480236826547)
            ·
              refine ⟨318948096031461720355239821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212632064020974480236826547 318948096031461720355239821)
              ·
                refine ⟨119605536011798145133214933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318948096031461720355239821 119605536011798145133214933)
                ·
                  refine ⟨2803254750276519026559725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 119605536011798145133214933 2803254750276519026559725)
                  ·
                    refine ⟨1051220531353694634959897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2803254750276519026559725 1051220531353694634959897)
                    ·
                      rfl

theorem cell22_3070867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 3].length) (baseStart_3070867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070867 prefixEnd_3070867 := by exact prefixLift 3070867
  have htrace : WordTrace (prefixWord ++ tailWord_3070867) baseStart_3070867 baseEnd_3070867 := by
    simpa [prefixWord, tailWord_3070867, baseEnd_3070867] using wordTrace_append hprefix tailTrace_3070867
  have hstable : (prefixWord ++ tailWord_3070867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070867).length < 2 ^ (prefixWord ++ tailWord_3070867).sum := by decide
  have hdescent : baseEnd_3070867 < baseStart_3070867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070884 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_3070884 : Nat := 118140960795 + 3070884 * 2 ^ 59
def prefixEnd_3070884 : Nat := 4983230072969 + 3 ^ 40 * 3070884 * 2
def baseEnd_3070884 : Nat := 1051226350801112257284845

theorem tailTrace_3070884 : CollatzResearch.WordTrace tailWord_3070884 prefixEnd_3070884 1051226350801112257284845 := by
  unfold tailWord_3070884
  simp only [CollatzResearch.WordTrace]
  refine ⟨56002170503359604038749853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74669560671146138718333137 56002170503359604038749853)
  ·
    refine ⟨21000813938759851514531195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56002170503359604038749853 21000813938759851514531195)
    ·
      refine ⟨31501220908139777271796793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21000813938759851514531195 31501220908139777271796793)
      ·
        refine ⟨23625915681104832953847595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31501220908139777271796793 23625915681104832953847595)
        ·
          refine ⟨35438873521657249430771393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23625915681104832953847595 35438873521657249430771393)
          ·
            refine ⟨26579155141242937073078545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35438873521657249430771393 26579155141242937073078545)
            ·
              refine ⟨19934366355932202804808909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26579155141242937073078545 19934366355932202804808909)
              ·
                refine ⟨7475387383474576051803341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19934366355932202804808909 7475387383474576051803341)
                ·
                  refine ⟨2803270268802966019426253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7475387383474576051803341 2803270268802966019426253)
                  ·
                    refine ⟨1051226350801112257284845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2803270268802966019426253 1051226350801112257284845)
                    ·
                      rfl

theorem cell22_3070884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_3070884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070884 prefixEnd_3070884 := by exact prefixLift 3070884
  have htrace : WordTrace (prefixWord ++ tailWord_3070884) baseStart_3070884 baseEnd_3070884 := by
    simpa [prefixWord, tailWord_3070884, baseEnd_3070884] using wordTrace_append hprefix tailTrace_3070884
  have hstable : (prefixWord ++ tailWord_3070884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070884).length < 2 ^ (prefixWord ++ tailWord_3070884).sum := by decide
  have hdescent : baseEnd_3070884 < baseStart_3070884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070946 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3070946 : Nat := 118140960795 + 3070946 * 2 ^ 59
def prefixEnd_3070946 : Nat := 4983230072969 + 3 ^ 40 * 3070946 * 2
def baseEnd_3070946 : Nat := 1051247574668164762234655

theorem tailTrace_3070946 : CollatzResearch.WordTrace tailWord_3070946 prefixEnd_3070946 1051247574668164762234655 := by
  unfold tailWord_3070946
  simp only [CollatzResearch.WordTrace]
  refine ⟨28001650583123648166564173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74671068221663061777504461 28001650583123648166564173)
  ·
    refine ⟨10500618968671368062461565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28001650583123648166564173 10500618968671368062461565)
    ·
      refine ⟨3937732113251763023423087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10500618968671368062461565 3937732113251763023423087)
      ·
        refine ⟨5906598169877644535134631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3937732113251763023423087 5906598169877644535134631)
        ·
          refine ⟨8859897254816466802701947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5906598169877644535134631 8859897254816466802701947)
          ·
            refine ⟨13289845882224700204052921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8859897254816466802701947 13289845882224700204052921)
            ·
              refine ⟨9967384411668525153039691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13289845882224700204052921 9967384411668525153039691)
              ·
                refine ⟨14951076617502787729559537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9967384411668525153039691 14951076617502787729559537)
                ·
                  refine ⟨11213307463127090797169653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14951076617502787729559537 11213307463127090797169653)
                  ·
                    refine ⟨1051247574668164762234655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11213307463127090797169653 1051247574668164762234655)
                    ·
                      rfl

theorem cell22_3070946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3070946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070946 prefixEnd_3070946 := by exact prefixLift 3070946
  have htrace : WordTrace (prefixWord ++ tailWord_3070946) baseStart_3070946 baseEnd_3070946 := by
    simpa [prefixWord, tailWord_3070946, baseEnd_3070946] using wordTrace_append hprefix tailTrace_3070946
  have hstable : (prefixWord ++ tailWord_3070946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070946).length < 2 ^ (prefixWord ++ tailWord_3070946).sum := by decide
  have hdescent : baseEnd_3070946 < baseStart_3070946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070961 : List Nat := [1, 2, 2, 2, 4, 2, 2, 2, 1, 4]
def baseStart_3070961 : Nat := 118140960795 + 3070961 * 2 ^ 59
def prefixEnd_3070961 : Nat := 4983230072969 + 3 ^ 40 * 3070961 * 2
def baseEnd_3070961 : Nat := 1051252709474709723109609

theorem tailTrace_3070961 : CollatzResearch.WordTrace tailWord_3070961 prefixEnd_3070961 1051252709474709723109609 := by
  unfold tailWord_3070961
  simp only [CollatzResearch.WordTrace]
  refine ⟨112007149427440250228052737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74671432951626833485368491 112007149427440250228052737)
  ·
    refine ⟨84005362070580187671039553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112007149427440250228052737 84005362070580187671039553)
    ·
      refine ⟨63004021552935140753279665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84005362070580187671039553 63004021552935140753279665)
      ·
        refine ⟨47253016164701355564959749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63004021552935140753279665 47253016164701355564959749)
        ·
          refine ⟨8859940530881504168429953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47253016164701355564959749 8859940530881504168429953)
          ·
            refine ⟨6644955398161128126322465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8859940530881504168429953 6644955398161128126322465)
            ·
              refine ⟨4983716548620846094741849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6644955398161128126322465 4983716548620846094741849)
              ·
                refine ⟨3737787411465634571056387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4983716548620846094741849 3737787411465634571056387)
                ·
                  refine ⟨5606681117198451856584581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3737787411465634571056387 5606681117198451856584581)
                  ·
                    refine ⟨1051252709474709723109609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5606681117198451856584581 1051252709474709723109609)
                    ·
                      rfl

theorem cell22_3070961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_3070961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070961 prefixEnd_3070961 := by exact prefixLift 3070961
  have htrace : WordTrace (prefixWord ++ tailWord_3070961) baseStart_3070961 baseEnd_3070961 := by
    simpa [prefixWord, tailWord_3070961, baseEnd_3070961] using wordTrace_append hprefix tailTrace_3070961
  have hstable : (prefixWord ++ tailWord_3070961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070961).length < 2 ^ (prefixWord ++ tailWord_3070961).sum := by decide
  have hdescent : baseEnd_3070961 < baseStart_3070961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070987 : List Nat := [1, 1, 1, 1, 6, 2, 10]
def baseStart_3070987 : Nat := 118140960795 + 3070987 * 2 ^ 59
def prefixEnd_3070987 : Nat := 4983230072969 + 3 ^ 40 * 3070987 * 2
def baseEnd_3070987 : Nat := 38935615178002011924427

theorem tailTrace_3070987 : CollatzResearch.WordTrace tailWord_3070987 prefixEnd_3070987 38935615178002011924427 := by
  unfold tailWord_3070987
  simp only [CollatzResearch.WordTrace]
  refine ⟨112008097725346056668499215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74672065150230704445666143 112008097725346056668499215)
  ·
    refine ⟨168012146588019085002748823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112008097725346056668499215 168012146588019085002748823)
    ·
      refine ⟨252018219882028627504123235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168012146588019085002748823 252018219882028627504123235)
      ·
        refine ⟨378027329823042941256184853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252018219882028627504123235 378027329823042941256184853)
        ·
          refine ⟨17720031085455137871383665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 378027329823042941256184853 17720031085455137871383665)
          ·
            refine ⟨13290023314091353403537749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17720031085455137871383665 13290023314091353403537749)
            ·
              refine ⟨38935615178002011924427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13290023314091353403537749 38935615178002011924427)
              ·
                rfl

theorem cell22_3070987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 10].length) (baseStart_3070987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3070987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3070987 prefixEnd_3070987 := by exact prefixLift 3070987
  have htrace : WordTrace (prefixWord ++ tailWord_3070987) baseStart_3070987 baseEnd_3070987 := by
    simpa [prefixWord, tailWord_3070987, baseEnd_3070987] using wordTrace_append hprefix tailTrace_3070987
  have hstable : (prefixWord ++ tailWord_3070987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070987).length < 2 ^ (prefixWord ++ tailWord_3070987).sum := by decide
  have hdescent : baseEnd_3070987 < baseStart_3070987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071019 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 5, 3]
def baseStart_3071019 : Nat := 118140960795 + 3071019 * 2 ^ 59
def prefixEnd_3071019 : Nat := 4983230072969 + 3 ^ 40 * 3071019 * 2
def baseEnd_3071019 : Nat := 1051272564060016905159431

theorem tailTrace_3071019 : CollatzResearch.WordTrace tailWord_3071019 prefixEnd_3071019 1051272564060016905159431 := by
  unfold tailWord_3071019
  simp only [CollatzResearch.WordTrace]
  refine ⟨112009264861230126133664111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74672843240820084089109407 112009264861230126133664111)
  ·
    refine ⟨168013897291845189200496167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112009264861230126133664111 168013897291845189200496167)
    ·
      refine ⟨252020845937767783800744251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168013897291845189200496167 252020845937767783800744251)
      ·
        refine ⟨378031268906651675701116377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252020845937767783800744251 378031268906651675701116377)
        ·
          refine ⟨283523451679988756775837283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378031268906651675701116377 283523451679988756775837283)
          ·
            refine ⟨425285177519983135163755925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283523451679988756775837283 425285177519983135163755925)
            ·
              refine ⟨19935242696249209460801059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 425285177519983135163755925 19935242696249209460801059)
              ·
                refine ⟨29902864044373814191201589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19935242696249209460801059 29902864044373814191201589)
                ·
                  refine ⟨2803393504160045080425149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29902864044373814191201589 2803393504160045080425149)
                  ·
                    refine ⟨1051272564060016905159431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2803393504160045080425149 1051272564060016905159431)
                    ·
                      rfl

theorem cell22_3071019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 3].length) (baseStart_3071019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071019 prefixEnd_3071019 := by exact prefixLift 3071019
  have htrace : WordTrace (prefixWord ++ tailWord_3071019) baseStart_3071019 baseEnd_3071019 := by
    simpa [prefixWord, tailWord_3071019, baseEnd_3071019] using wordTrace_append hprefix tailTrace_3071019
  have hstable : (prefixWord ++ tailWord_3071019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071019).length < 2 ^ (prefixWord ++ tailWord_3071019).sum := by decide
  have hdescent : baseEnd_3071019 < baseStart_3071019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071064 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 2, 5]
def baseStart_3071064 : Nat := 118140960795 + 3071064 * 2 ^ 59
def prefixEnd_3071064 : Nat := 4983230072969 + 3 ^ 40 * 3071064 * 2
def baseEnd_3071064 : Nat := 1051287968479651787784293

theorem tailTrace_3071064 : CollatzResearch.WordTrace tailWord_3071064 prefixEnd_3071064 1051287968479651787784293 := by
  unfold tailWord_3071064
  simp only [CollatzResearch.WordTrace]
  refine ⟨56005453073033549409526123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74673937430711399212701497 56005453073033549409526123)
  ·
    refine ⟨84008179609550324114289185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56005453073033549409526123 84008179609550324114289185)
    ·
      refine ⟨63006134707162743085716889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84008179609550324114289185 63006134707162743085716889)
      ·
        refine ⟨47254601030372057314287667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63006134707162743085716889 47254601030372057314287667)
        ·
          refine ⟨70881901545558085971431501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47254601030372057314287667 70881901545558085971431501)
          ·
            refine ⟨26580713079584282239286813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70881901545558085971431501 26580713079584282239286813)
            ·
              refine ⟨9967767404844105839732555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26580713079584282239286813 9967767404844105839732555)
              ·
                refine ⟨14951651107266158759598833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9967767404844105839732555 14951651107266158759598833)
                ·
                  refine ⟨11213738330449619069699125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14951651107266158759598833 11213738330449619069699125)
                  ·
                    refine ⟨1051287968479651787784293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11213738330449619069699125 1051287968479651787784293)
                    ·
                      rfl

theorem cell22_3071064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_3071064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071064 prefixEnd_3071064 := by exact prefixLift 3071064
  have htrace : WordTrace (prefixWord ++ tailWord_3071064) baseStart_3071064 baseEnd_3071064 := by
    simpa [prefixWord, tailWord_3071064, baseEnd_3071064] using wordTrace_append hprefix tailTrace_3071064
  have hstable : (prefixWord ++ tailWord_3071064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071064).length < 2 ^ (prefixWord ++ tailWord_3071064).sum := by decide
  have hdescent : baseEnd_3071064 < baseStart_3071064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071070 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3071070 : Nat := 118140960795 + 3071070 * 2 ^ 59
def prefixEnd_3071070 : Nat := 4983230072969 + 3 ^ 40 * 3071070 * 2
def baseEnd_3071070 : Nat := 1051290022402269772134275

theorem tailTrace_3071070 : CollatzResearch.WordTrace tailWord_3071070 prefixEnd_3071070 1051290022402269772134275 := by
  unfold tailWord_3071070
  simp only [CollatzResearch.WordTrace]
  refine ⟨14001390623005670230471333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74674083322696907895847109 14001390623005670230471333)
  ·
    refine ⟨2625260741813563168213375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14001390623005670230471333 2625260741813563168213375)
    ·
      refine ⟨3937891112720344752320063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2625260741813563168213375 3937891112720344752320063)
      ·
        refine ⟨5906836669080517128480095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3937891112720344752320063 5906836669080517128480095)
        ·
          refine ⟨8860255003620775692720143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5906836669080517128480095 8860255003620775692720143)
          ·
            refine ⟨13290382505431163539080215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8860255003620775692720143 13290382505431163539080215)
            ·
              refine ⟨19935573758146745308620323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13290382505431163539080215 19935573758146745308620323)
              ·
                refine ⟨29903360637220117962930485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19935573758146745308620323 29903360637220117962930485)
                ·
                  refine ⟨2803440059739386059024733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29903360637220117962930485 2803440059739386059024733)
                  ·
                    refine ⟨1051290022402269772134275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2803440059739386059024733 1051290022402269772134275)
                    ·
                      rfl

theorem cell22_3071070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3071070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071070 prefixEnd_3071070 := by exact prefixLift 3071070
  have htrace : WordTrace (prefixWord ++ tailWord_3071070) baseStart_3071070 baseEnd_3071070 := by
    simpa [prefixWord, tailWord_3071070, baseEnd_3071070] using wordTrace_append hprefix tailTrace_3071070
  have hstable : (prefixWord ++ tailWord_3071070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071070).length < 2 ^ (prefixWord ++ tailWord_3071070).sum := by decide
  have hdescent : baseEnd_3071070 < baseStart_3071070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071143 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3071143 : Nat := 118140960795 + 3071143 * 2 ^ 59
def prefixEnd_3071143 : Nat := 4983230072969 + 3 ^ 40 * 3071143 * 2
def baseEnd_3071143 : Nat := 1051315011794121915059051

theorem tailTrace_3071143 : CollatzResearch.WordTrace tailWord_3071143 prefixEnd_3071143 1051315011794121915059051 := by
  unfold tailWord_3071143
  simp only [CollatzResearch.WordTrace]
  refine ⟨112013787512780895311178083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74675858341853930207452055 112013787512780895311178083)
  ·
    refine ⟨168020681269171342966767125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112013787512780895311178083 168020681269171342966767125)
    ·
      refine ⟨7875969434492406701567209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 168020681269171342966767125 7875969434492406701567209)
      ·
        refine ⟨5906977075869305026175407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7875969434492406701567209 5906977075869305026175407)
        ·
          refine ⟨8860465613803957539263111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5906977075869305026175407 8860465613803957539263111)
          ·
            refine ⟨13290698420705936308894667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8860465613803957539263111 13290698420705936308894667)
            ·
              refine ⟨19936047631058904463342001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13290698420705936308894667 19936047631058904463342001)
              ·
                refine ⟨14952035723294178347506501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19936047631058904463342001 14952035723294178347506501)
                ·
                  refine ⟨2803506698117658440157469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14952035723294178347506501 2803506698117658440157469)
                  ·
                    refine ⟨1051315011794121915059051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2803506698117658440157469 1051315011794121915059051)
                    ·
                      rfl

theorem cell22_3071143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3071143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071143 prefixEnd_3071143 := by exact prefixLift 3071143
  have htrace : WordTrace (prefixWord ++ tailWord_3071143) baseStart_3071143 baseEnd_3071143 := by
    simpa [prefixWord, tailWord_3071143, baseEnd_3071143] using wordTrace_append hprefix tailTrace_3071143
  have hstable : (prefixWord ++ tailWord_3071143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071143).length < 2 ^ (prefixWord ++ tailWord_3071143).sum := by decide
  have hdescent : baseEnd_3071143 < baseStart_3071143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071171 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 3, 3]
def baseStart_3071171 : Nat := 118140960795 + 3071171 * 2 ^ 59
def prefixEnd_3071171 : Nat := 4983230072969 + 3 ^ 40 * 3071171 * 2
def baseEnd_3071171 : Nat := 1051324596766339175358965

theorem tailTrace_3071171 : CollatzResearch.WordTrace tailWord_3071171 prefixEnd_3071171 1051324596766339175358965 := by
  unfold tailWord_3071171
  simp only [CollatzResearch.WordTrace]
  refine ⟨112014808756679456093197367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74676539171119637395464911 112014808756679456093197367)
  ·
    refine ⟨168022213135019184139796051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112014808756679456093197367 168022213135019184139796051)
    ·
      refine ⟨252033319702528776209694077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168022213135019184139796051 252033319702528776209694077)
      ·
        refine ⟨94512494888448291078635279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252033319702528776209694077 94512494888448291078635279)
        ·
          refine ⟨141768742332672436617952919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94512494888448291078635279 141768742332672436617952919)
          ·
            refine ⟨212653113499008654926929379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141768742332672436617952919 212653113499008654926929379)
            ·
              refine ⟨318979670248512982390394069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212653113499008654926929379 318979670248512982390394069)
              ·
                refine ⟨7476086021449523024774861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 318979670248512982390394069 7476086021449523024774861)
                ·
                  refine ⟨2803532258043571134290573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7476086021449523024774861 2803532258043571134290573)
                  ·
                    refine ⟨1051324596766339175358965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2803532258043571134290573 1051324596766339175358965)
                    ·
                      rfl

theorem cell22_3071171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 3].length) (baseStart_3071171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071171 prefixEnd_3071171 := by exact prefixLift 3071171
  have htrace : WordTrace (prefixWord ++ tailWord_3071171) baseStart_3071171 baseEnd_3071171 := by
    simpa [prefixWord, tailWord_3071171, baseEnd_3071171] using wordTrace_append hprefix tailTrace_3071171
  have hstable : (prefixWord ++ tailWord_3071171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071171).length < 2 ^ (prefixWord ++ tailWord_3071171).sum := by decide
  have hdescent : baseEnd_3071171 < baseStart_3071171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071231 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 3, 4]
def baseStart_3071231 : Nat := 118140960795 + 3071231 * 2 ^ 59
def prefixEnd_3071231 : Nat := 4983230072969 + 3 ^ 40 * 3071231 * 2
def baseEnd_3071231 : Nat := 1051345135992519018858781

theorem tailTrace_3071231 : CollatzResearch.WordTrace tailWord_3071231 prefixEnd_3071231 1051345135992519018858781 := by
  unfold tailWord_3071231
  simp only [CollatzResearch.WordTrace]
  refine ⟨112016997136462086340381547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74677998090974724226921031 112016997136462086340381547)
  ·
    refine ⟨168025495704693129510572321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112016997136462086340381547 168025495704693129510572321)
    ·
      refine ⟨126019121778519847132929241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168025495704693129510572321 126019121778519847132929241)
      ·
        refine ⟨94514341333889885349696931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126019121778519847132929241 94514341333889885349696931)
        ·
          refine ⟨141771512000834828024545397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94514341333889885349696931 141771512000834828024545397)
          ·
            refine ⟨13291079250078265127301131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141771512000834828024545397 13291079250078265127301131)
            ·
              refine ⟨19936618875117397690951697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13291079250078265127301131 19936618875117397690951697)
              ·
                refine ⟨14952464156338048268213773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19936618875117397690951697 14952464156338048268213773)
                ·
                  refine ⟨5607174058626768100580165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14952464156338048268213773 5607174058626768100580165)
                  ·
                    refine ⟨1051345135992519018858781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5607174058626768100580165 1051345135992519018858781)
                    ·
                      rfl

theorem cell22_3071231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_3071231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071231 prefixEnd_3071231 := by exact prefixLift 3071231
  have htrace : WordTrace (prefixWord ++ tailWord_3071231) baseStart_3071231 baseEnd_3071231 := by
    simpa [prefixWord, tailWord_3071231, baseEnd_3071231] using wordTrace_append hprefix tailTrace_3071231
  have hstable : (prefixWord ++ tailWord_3071231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071231).length < 2 ^ (prefixWord ++ tailWord_3071231).sum := by decide
  have hdescent : baseEnd_3071231 < baseStart_3071231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071246 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_3071246 : Nat := 118140960795 + 3071246 * 2 ^ 59
def prefixEnd_3071246 : Nat := 4983230072969 + 3 ^ 40 * 3071246 * 2
def baseEnd_3071246 : Nat := 350450090266354659911245

theorem tailTrace_3071246 : CollatzResearch.WordTrace tailWord_3071246 prefixEnd_3071246 350450090266354659911245 := by
  unfold tailWord_3071246
  simp only [CollatzResearch.WordTrace]
  refine ⟨14002193028925967987772199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74678362820938495934785061 14002193028925967987772199)
  ·
    refine ⟨21003289543388951981658299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14002193028925967987772199 21003289543388951981658299)
    ·
      refine ⟨31504934315083427972487449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21003289543388951981658299 31504934315083427972487449)
      ·
        refine ⟨23628700736312570979365587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31504934315083427972487449 23628700736312570979365587)
        ·
          refine ⟨35443051104468856469048381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23628700736312570979365587 35443051104468856469048381)
          ·
            refine ⟨13291144164175821175893143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35443051104468856469048381 13291144164175821175893143)
            ·
              refine ⟨19936716246263731763839715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13291144164175821175893143 19936716246263731763839715)
              ·
                refine ⟨29905074369395597645759573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19936716246263731763839715 29905074369395597645759573)
                ·
                  refine ⟨350450090266354659911245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29905074369395597645759573 350450090266354659911245)
                  ·
                    rfl

theorem cell22_3071246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_3071246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071246 prefixEnd_3071246 := by exact prefixLift 3071246
  have htrace : WordTrace (prefixWord ++ tailWord_3071246) baseStart_3071246 baseEnd_3071246 := by
    simpa [prefixWord, tailWord_3071246, baseEnd_3071246] using wordTrace_append hprefix tailTrace_3071246
  have hstable : (prefixWord ++ tailWord_3071246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071246).length < 2 ^ (prefixWord ++ tailWord_3071246).sum := by decide
  have hdescent : baseEnd_3071246 < baseStart_3071246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071276 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_3071276 : Nat := 118140960795 + 3071276 * 2 ^ 59
def prefixEnd_3071276 : Nat := 4983230072969 + 3 ^ 40 * 3071276 * 2
def baseEnd_3071276 : Nat := 1051360540412153901483643

theorem tailTrace_3071276 : CollatzResearch.WordTrace tailWord_3071276 prefixEnd_3071276 1051360540412153901483643 := by
  unfold tailWord_3071276
  simp only [CollatzResearch.WordTrace]
  refine ⟨56009319210649529512884841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74679092280866039350513121 56009319210649529512884841)
  ·
    refine ⟨42006989407987147134663631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56009319210649529512884841 42006989407987147134663631)
    ·
      refine ⟨63010484111980720701995447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42006989407987147134663631 63010484111980720701995447)
      ·
        refine ⟨94515726167971081052993171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63010484111980720701995447 94515726167971081052993171)
        ·
          refine ⟨141773589251956621579489757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94515726167971081052993171 141773589251956621579489757)
          ·
            refine ⟨53165095969483733092308659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141773589251956621579489757 53165095969483733092308659)
            ·
              refine ⟨79747643954225599638462989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53165095969483733092308659 79747643954225599638462989)
              ·
                refine ⟨29905366482834599864423621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79747643954225599638462989 29905366482834599864423621)
                ·
                  refine ⟨5607256215531487474579429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29905366482834599864423621 5607256215531487474579429)
                  ·
                    refine ⟨1051360540412153901483643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5607256215531487474579429 1051360540412153901483643)
                    ·
                      rfl

theorem cell22_3071276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_3071276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071276 prefixEnd_3071276 := by exact prefixLift 3071276
  have htrace : WordTrace (prefixWord ++ tailWord_3071276) baseStart_3071276 baseEnd_3071276 := by
    simpa [prefixWord, tailWord_3071276, baseEnd_3071276] using wordTrace_append hprefix tailTrace_3071276
  have hstable : (prefixWord ++ tailWord_3071276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071276).length < 2 ^ (prefixWord ++ tailWord_3071276).sum := by decide
  have hdescent : baseEnd_3071276 < baseStart_3071276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071308 : List Nat := [2, 2, 1, 3, 2, 2, 4, 6]
def baseStart_3071308 : Nat := 118140960795 + 3071308 * 2 ^ 59
def prefixEnd_3071308 : Nat := 4983230072969 + 3 ^ 40 * 3071308 * 2
def baseEnd_3071308 : Nat := 116819054962901831631505

theorem tailTrace_3071308 : CollatzResearch.WordTrace tailWord_3071308 prefixEnd_3071308 116819054962901831631505 := by
  unfold tailWord_3071308
  simp only [CollatzResearch.WordTrace]
  refine ⟨56009902778591564245467289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74679870371455418993956385 56009902778591564245467289)
  ·
    refine ⟨42007427083943673184100467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56009902778591564245467289 42007427083943673184100467)
    ·
      refine ⟨63011140625915509776150701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42007427083943673184100467 63011140625915509776150701)
      ·
        refine ⟨23629177734718316166056513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63011140625915509776150701 23629177734718316166056513)
        ·
          refine ⟨17721883301038737124542385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23629177734718316166056513 17721883301038737124542385)
          ·
            refine ⟨13291412475779052843406789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17721883301038737124542385 13291412475779052843406789)
            ·
              refine ⟨2492139839208572408138773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13291412475779052843406789 2492139839208572408138773)
              ·
                refine ⟨116819054962901831631505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2492139839208572408138773 116819054962901831631505)
                ·
                  rfl

theorem cell22_3071308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 6].length) (baseStart_3071308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071308 prefixEnd_3071308 := by exact prefixLift 3071308
  have htrace : WordTrace (prefixWord ++ tailWord_3071308) baseStart_3071308 baseEnd_3071308 := by
    simpa [prefixWord, tailWord_3071308, baseEnd_3071308] using wordTrace_append hprefix tailTrace_3071308
  have hstable : (prefixWord ++ tailWord_3071308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071308).length < 2 ^ (prefixWord ++ tailWord_3071308).sum := by decide
  have hdescent : baseEnd_3071308 < baseStart_3071308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071340 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 3, 3]
def baseStart_3071340 : Nat := 118140960795 + 3071340 * 2 ^ 59
def prefixEnd_3071340 : Nat := 4983230072969 + 3 ^ 40 * 3071340 * 2
def baseEnd_3071340 : Nat := 1051382448920079067883447

theorem tailTrace_3071340 : CollatzResearch.WordTrace tailWord_3071340 prefixEnd_3071340 1051382448920079067883447 := by
  unfold tailWord_3071340
  simp only [CollatzResearch.WordTrace]
  refine ⟨56010486346533598978049737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74680648462044798637399649 56010486346533598978049737)
  ·
    refine ⟨42007864759900199233537303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56010486346533598978049737 42007864759900199233537303)
    ·
      refine ⟨63011797139850298850305955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42007864759900199233537303 63011797139850298850305955)
      ·
        refine ⟨94517695709775448275458933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63011797139850298850305955 94517695709775448275458933)
        ·
          refine ⟨8861033972791448275824275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94517695709775448275458933 8861033972791448275824275)
          ·
            refine ⟨13291550959187172413736413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8861033972791448275824275 13291550959187172413736413)
            ·
              refine ⟨4984331609695189655151155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13291550959187172413736413 4984331609695189655151155)
              ·
                refine ⟨7476497414542784482726733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4984331609695189655151155 7476497414542784482726733)
                ·
                  refine ⟨2803686530453544181022525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7476497414542784482726733 2803686530453544181022525)
                  ·
                    refine ⟨1051382448920079067883447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2803686530453544181022525 1051382448920079067883447)
                    ·
                      rfl

theorem cell22_3071340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_3071340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071340 prefixEnd_3071340 := by exact prefixLift 3071340
  have htrace : WordTrace (prefixWord ++ tailWord_3071340) baseStart_3071340 baseEnd_3071340 := by
    simpa [prefixWord, tailWord_3071340, baseEnd_3071340] using wordTrace_append hprefix tailTrace_3071340
  have hstable : (prefixWord ++ tailWord_3071340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071340).length < 2 ^ (prefixWord ++ tailWord_3071340).sum := by decide
  have hdescent : baseEnd_3071340 < baseStart_3071340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071351 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 1, 7]
def baseStart_3071351 : Nat := 118140960795 + 3071351 * 2 ^ 59
def prefixEnd_3071351 : Nat := 4983230072969 + 3 ^ 40 * 3071351 * 2
def baseEnd_3071351 : Nat := 1051386214444878705858413

theorem tailTrace_3071351 : CollatzResearch.WordTrace tailWord_3071351 prefixEnd_3071351 1051386214444878705858413 := by
  unfold tailWord_3071351
  simp only [CollatzResearch.WordTrace]
  refine ⟨112021373896027346834749907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74680915930684897889833271 112021373896027346834749907)
  ·
    refine ⟨168032060844041020252124861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112021373896027346834749907 168032060844041020252124861)
    ·
      refine ⟨63012022816515382594546823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168032060844041020252124861 63012022816515382594546823)
      ·
        refine ⟨94518034224773073891820235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63012022816515382594546823 94518034224773073891820235)
        ·
          refine ⟨141777051337159610837730353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94518034224773073891820235 141777051337159610837730353)
          ·
            refine ⟨106332788502869708128297765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141777051337159610837730353 106332788502869708128297765)
            ·
              refine ⟨19937397844288070274055831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106332788502869708128297765 19937397844288070274055831)
              ·
                refine ⟨29906096766432105411083747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19937397844288070274055831 29906096766432105411083747)
                ·
                  refine ⟨44859145149648158116625621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29906096766432105411083747 44859145149648158116625621)
                  ·
                    refine ⟨1051386214444878705858413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44859145149648158116625621 1051386214444878705858413)
                    ·
                      rfl

theorem cell22_3071351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_3071351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071351 prefixEnd_3071351 := by exact prefixLift 3071351
  have htrace : WordTrace (prefixWord ++ tailWord_3071351) baseStart_3071351 baseEnd_3071351 := by
    simpa [prefixWord, tailWord_3071351, baseEnd_3071351] using wordTrace_append hprefix tailTrace_3071351
  have hstable : (prefixWord ++ tailWord_3071351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071351).length < 2 ^ (prefixWord ++ tailWord_3071351).sum := by decide
  have hdescent : baseEnd_3071351 < baseStart_3071351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071477 : List Nat := [1, 3, 5, 1, 1, 1, 4, 6]
def baseStart_3071477 : Nat := 118140960795 + 3071477 * 2 ^ 59
def prefixEnd_3071477 : Nat := 4983230072969 + 3 ^ 40 * 3071477 * 2
def baseEnd_3071477 : Nat := 116825482979984041912003

theorem tailTrace_3071477 : CollatzResearch.WordTrace tailWord_3071477 prefixEnd_3071477 116825482979984041912003 := by
  unfold tailWord_3071477
  simp only [CollatzResearch.WordTrace]
  refine ⟨112025969493570870353836685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74683979662380580235891123 112025969493570870353836685)
  ·
    refine ⟨42009738560089076382688757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112025969493570870353836685 42009738560089076382688757)
    ·
      refine ⟨3938412990008350910877071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42009738560089076382688757 3938412990008350910877071)
      ·
        refine ⟨5907619485012526366315607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3938412990008350910877071 5907619485012526366315607)
        ·
          refine ⟨8861429227518789549473411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5907619485012526366315607 8861429227518789549473411)
          ·
            refine ⟨13292143841278184324210117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8861429227518789549473411 13292143841278184324210117)
            ·
              refine ⟨2492276970239659560789397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13292143841278184324210117 2492276970239659560789397)
              ·
                refine ⟨116825482979984041912003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2492276970239659560789397 116825482979984041912003)
                ·
                  rfl

theorem cell22_3071477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 6].length) (baseStart_3071477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071477 prefixEnd_3071477 := by exact prefixLift 3071477
  have htrace : WordTrace (prefixWord ++ tailWord_3071477) baseStart_3071477 baseEnd_3071477 := by
    simpa [prefixWord, tailWord_3071477, baseEnd_3071477] using wordTrace_append hprefix tailTrace_3071477
  have hstable : (prefixWord ++ tailWord_3071477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071477).length < 2 ^ (prefixWord ++ tailWord_3071477).sum := by decide
  have hdescent : baseEnd_3071477 < baseStart_3071477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071522 : List Nat := [3, 3, 1, 1, 1, 1, 6, 1, 5]
def baseStart_3071522 : Nat := 118140960795 + 3071522 * 2 ^ 59
def prefixEnd_3071522 : Nat := 4983230072969 + 3 ^ 40 * 3071522 * 2
def baseEnd_3071522 : Nat := 350481583746497086610963

theorem tailTrace_3071522 : CollatzResearch.WordTrace tailWord_3071522 prefixEnd_3071522 350481583746497086610963 := by
  unfold tailWord_3071522
  simp only [CollatzResearch.WordTrace]
  refine ⟨28006902694601960759806205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74685073852271895359483213 28006902694601960759806205)
  ·
    refine ⟨10502588510475735284927327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28006902694601960759806205 10502588510475735284927327)
    ·
      refine ⟨15753882765713602927390991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10502588510475735284927327 15753882765713602927390991)
      ·
        refine ⟨23630824148570404391086487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15753882765713602927390991 23630824148570404391086487)
        ·
          refine ⟨35446236222855606586629731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23630824148570404391086487 35446236222855606586629731)
          ·
            refine ⟨53169354334283409879944597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35446236222855606586629731 53169354334283409879944597)
            ·
              refine ⟨2492313484419534838122403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53169354334283409879944597 2492313484419534838122403)
              ·
                refine ⟨3738470226629302257183605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2492313484419534838122403 3738470226629302257183605)
                ·
                  refine ⟨350481583746497086610963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3738470226629302257183605 350481583746497086610963)
                  ·
                    rfl

theorem cell22_3071522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_3071522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071522 prefixEnd_3071522 := by exact prefixLift 3071522
  have htrace : WordTrace (prefixWord ++ tailWord_3071522) baseStart_3071522 baseEnd_3071522 := by
    simpa [prefixWord, tailWord_3071522, baseEnd_3071522] using wordTrace_append hprefix tailTrace_3071522
  have hstable : (prefixWord ++ tailWord_3071522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071522).length < 2 ^ (prefixWord ++ tailWord_3071522).sum := by decide
  have hdescent : baseEnd_3071522 < baseStart_3071522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071563 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 3, 6]
def baseStart_3071563 : Nat := 118140960795 + 3071563 * 2 ^ 59
def prefixEnd_3071563 : Nat := 4983230072969 + 3 ^ 40 * 3071563 * 2
def baseEnd_3071563 : Nat := 1051458786377380819557763

theorem tailTrace_3071563 : CollatzResearch.WordTrace tailWord_3071563 prefixEnd_3071563 1051458786377380819557763 := by
  unfold tailWord_3071563
  simp only [CollatzResearch.WordTrace]
  refine ⟨112029106171259307041467343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74686070780839538027644895 112029106171259307041467343)
  ·
    refine ⟨168043659256888960562201015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112029106171259307041467343 168043659256888960562201015)
    ·
      refine ⟨252065488885333440843301523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168043659256888960562201015 252065488885333440843301523)
      ·
        refine ⟨378098233328000161264952285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252065488885333440843301523 378098233328000161264952285)
        ·
          refine ⟨141786837498000060474357107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 378098233328000161264952285 141786837498000060474357107)
          ·
            refine ⟨212680256247000090711535661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141786837498000060474357107 212680256247000090711535661)
            ·
              refine ⟨79755096092625034016825873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212680256247000090711535661 79755096092625034016825873)
              ·
                refine ⟨59816322069468775512619405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79755096092625034016825873 59816322069468775512619405)
                ·
                  refine ⟨22431120776050790817232277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59816322069468775512619405 22431120776050790817232277)
                  ·
                    refine ⟨1051458786377380819557763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22431120776050790817232277 1051458786377380819557763)
                    ·
                      rfl

theorem cell22_3071563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 6].length) (baseStart_3071563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071563 prefixEnd_3071563 := by exact prefixLift 3071563
  have htrace : WordTrace (prefixWord ++ tailWord_3071563) baseStart_3071563 baseEnd_3071563 := by
    simpa [prefixWord, tailWord_3071563, baseEnd_3071563] using wordTrace_append hprefix tailTrace_3071563
  have hstable : (prefixWord ++ tailWord_3071563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071563).length < 2 ^ (prefixWord ++ tailWord_3071563).sum := by decide
  have hdescent : baseEnd_3071563 < baseStart_3071563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071597 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_3071597 : Nat := 118140960795 + 3071597 * 2 ^ 59
def prefixEnd_3071597 : Nat := 4983230072969 + 3 ^ 40 * 3071597 * 2
def baseEnd_3071597 : Nat := 1051470425272216064207659

theorem tailTrace_3071597 : CollatzResearch.WordTrace tailWord_3071597 prefixEnd_3071597 1051470425272216064207659 := by
  unfold tailWord_3071597
  simp only [CollatzResearch.WordTrace]
  refine ⟨112030346253136130848205045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74686897502090753898803363 112030346253136130848205045)
  ·
    refine ⟨10502844961231512267019223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112030346253136130848205045 10502844961231512267019223)
    ·
      refine ⟨15754267441847268400528835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10502844961231512267019223 15754267441847268400528835)
      ·
        refine ⟨23631401162770902600793253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15754267441847268400528835 23631401162770902600793253)
        ·
          refine ⟨4430887718019544237648735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23631401162770902600793253 4430887718019544237648735)
          ·
            refine ⟨6646331577029316356473103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4430887718019544237648735 6646331577029316356473103)
            ·
              refine ⟨9969497365543974534709655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6646331577029316356473103 9969497365543974534709655)
              ·
                refine ⟨14954246048315961802064483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9969497365543974534709655 14954246048315961802064483)
                ·
                  refine ⟨22431369072473942703096725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14954246048315961802064483 22431369072473942703096725)
                  ·
                    refine ⟨1051470425272216064207659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22431369072473942703096725 1051470425272216064207659)
                    ·
                      rfl

theorem cell22_3071597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_3071597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071597 prefixEnd_3071597 := by exact prefixLift 3071597
  have htrace : WordTrace (prefixWord ++ tailWord_3071597) baseStart_3071597 baseEnd_3071597 := by
    simpa [prefixWord, tailWord_3071597, baseEnd_3071597] using wordTrace_append hprefix tailTrace_3071597
  have hstable : (prefixWord ++ tailWord_3071597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071597).length < 2 ^ (prefixWord ++ tailWord_3071597).sum := by decide
  have hdescent : baseEnd_3071597 < baseStart_3071597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071627 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 3, 3]
def baseStart_3071627 : Nat := 118140960795 + 3071627 * 2 ^ 59
def prefixEnd_3071627 : Nat := 4983230072969 + 3 ^ 40 * 3071627 * 2
def baseEnd_3071627 : Nat := 1051480694885305985957567

theorem tailTrace_3071627 : CollatzResearch.WordTrace tailWord_3071627 prefixEnd_3071627 1051480694885305985957567 := by
  unfold tailWord_3071627
  simp only [CollatzResearch.WordTrace]
  refine ⟨112031440443027445971797135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74687626962018297314531423 112031440443027445971797135)
  ·
    refine ⟨168047160664541168957695703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112031440443027445971797135 168047160664541168957695703)
    ·
      refine ⟨252070740996811753436543555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168047160664541168957695703 252070740996811753436543555)
      ·
        refine ⟨378106111495217630154815333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252070740996811753436543555 378106111495217630154815333)
        ·
          refine ⟨70894895905353305654027875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 378106111495217630154815333 70894895905353305654027875)
          ·
            refine ⟨106342343858029958481041813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70894895905353305654027875 106342343858029958481041813)
            ·
              refine ⟨4984797368345154303798835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106342343858029958481041813 4984797368345154303798835)
              ·
                refine ⟨7477196052517731455698253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4984797368345154303798835 7477196052517731455698253)
                ·
                  refine ⟨2803948519694149295886845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7477196052517731455698253 2803948519694149295886845)
                  ·
                    refine ⟨1051480694885305985957567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2803948519694149295886845 1051480694885305985957567)
                    ·
                      rfl

theorem cell22_3071627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 3].length) (baseStart_3071627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071627 prefixEnd_3071627 := by exact prefixLift 3071627
  have htrace : WordTrace (prefixWord ++ tailWord_3071627) baseStart_3071627 baseEnd_3071627 := by
    simpa [prefixWord, tailWord_3071627, baseEnd_3071627] using wordTrace_append hprefix tailTrace_3071627
  have hstable : (prefixWord ++ tailWord_3071627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071627).length < 2 ^ (prefixWord ++ tailWord_3071627).sum := by decide
  have hdescent : baseEnd_3071627 < baseStart_3071627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071678 : List Nat := [4, 2, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_3071678 : Nat := 118140960795 + 3071678 * 2 ^ 59
def prefixEnd_3071678 : Nat := 4983230072969 + 3 ^ 40 * 3071678 * 2
def baseEnd_3071678 : Nat := 1051498153227558852932411

theorem tailTrace_3071678 : CollatzResearch.WordTrace tailWord_3071678 prefixEnd_3071678 1051498153227558852932411 := by
  unfold tailWord_3071678
  simp only [CollatzResearch.WordTrace]
  refine ⟨14004162570730335210237961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74688867043895121121269125 14004162570730335210237961)
  ·
    refine ⟨10503121928047751407678471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14004162570730335210237961 10503121928047751407678471)
    ·
      refine ⟨15754682892071627111517707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10503121928047751407678471 15754682892071627111517707)
      ·
        refine ⟨23632024338107440667276561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15754682892071627111517707 23632024338107440667276561)
        ·
          refine ⟨17724018253580580500457421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23632024338107440667276561 17724018253580580500457421)
          ·
            refine ⟨6646506845092717687671533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17724018253580580500457421 6646506845092717687671533)
            ·
              refine ⟨2492440066909769132876825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6646506845092717687671533 2492440066909769132876825)
              ·
                refine ⟨1869330050182326849657619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2492440066909769132876825 1869330050182326849657619)
                ·
                  refine ⟨2803995075273490274486429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869330050182326849657619 2803995075273490274486429)
                  ·
                    refine ⟨1051498153227558852932411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2803995075273490274486429 1051498153227558852932411)
                    ·
                      rfl

theorem cell22_3071678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_3071678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071678 prefixEnd_3071678 := by exact prefixLift 3071678
  have htrace : WordTrace (prefixWord ++ tailWord_3071678) baseStart_3071678 baseEnd_3071678 := by
    simpa [prefixWord, tailWord_3071678, baseEnd_3071678] using wordTrace_append hprefix tailTrace_3071678
  have hstable : (prefixWord ++ tailWord_3071678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071678).length < 2 ^ (prefixWord ++ tailWord_3071678).sum := by decide
  have hdescent : baseEnd_3071678 < baseStart_3071678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071717 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_3071717 : Nat := 118140960795 + 3071717 * 2 ^ 59
def prefixEnd_3071717 : Nat := 4983230072969 + 3 ^ 40 * 3071717 * 2
def baseEnd_3071717 : Nat := 1051511503724575751207291

theorem tailTrace_3071717 : CollatzResearch.WordTrace tailWord_3071717 prefixEnd_3071717 1051511503724575751207291 := by
  unfold tailWord_3071717
  simp only [CollatzResearch.WordTrace]
  refine ⟨112034723012701391342573405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74689815341800927561715603 112034723012701391342573405)
  ·
    refine ⟨42013021129763021753465027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112034723012701391342573405 42013021129763021753465027)
    ·
      refine ⟨63019531694644532630197541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42013021129763021753465027 63019531694644532630197541)
      ·
        refine ⟨11816162192745849868162039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63019531694644532630197541 11816162192745849868162039)
        ·
          refine ⟨17724243289118774802243059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11816162192745849868162039 17724243289118774802243059)
          ·
            refine ⟨26586364933678162203364589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17724243289118774802243059 26586364933678162203364589)
            ·
              refine ⟨9969886850129310826261721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26586364933678162203364589 9969886850129310826261721)
              ·
                refine ⟨7477415137596983119696291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9969886850129310826261721 7477415137596983119696291)
                ·
                  refine ⟨11216122706395474679544437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7477415137596983119696291 11216122706395474679544437)
                  ·
                    refine ⟨1051511503724575751207291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11216122706395474679544437 1051511503724575751207291)
                    ·
                      rfl

theorem cell22_3071717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_3071717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071717 prefixEnd_3071717 := by exact prefixLift 3071717
  have htrace : WordTrace (prefixWord ++ tailWord_3071717) baseStart_3071717 baseEnd_3071717 := by
    simpa [prefixWord, tailWord_3071717, baseEnd_3071717] using wordTrace_append hprefix tailTrace_3071717
  have hstable : (prefixWord ++ tailWord_3071717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071717).length < 2 ^ (prefixWord ++ tailWord_3071717).sum := by decide
  have hdescent : baseEnd_3071717 < baseStart_3071717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071796 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_3071796 : Nat := 118140960795 + 3071796 * 2 ^ 59
def prefixEnd_3071796 : Nat := 4983230072969 + 3 ^ 40 * 3071796 * 2
def baseEnd_3071796 : Nat := 1051538547039045878482049

theorem tailTrace_3071796 : CollatzResearch.WordTrace tailWord_3071796 prefixEnd_3071796 1051538547039045878482049 := by
  unfold tailWord_3071796
  simp only [CollatzResearch.WordTrace]
  refine ⟨56018802189707593917349621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74691736252943458556466161 56018802189707593917349621)
  ·
    refine ⟨5251762705285086929751527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56018802189707593917349621 5251762705285086929751527)
    ·
      refine ⟨7877644057927630394627291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5251762705285086929751527 7877644057927630394627291)
      ·
        refine ⟨11816466086891445591940937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7877644057927630394627291 11816466086891445591940937)
        ·
          refine ⟨8862349565168584193955703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11816466086891445591940937 8862349565168584193955703)
          ·
            refine ⟨13293524347752876290933555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8862349565168584193955703 13293524347752876290933555)
            ·
              refine ⟨19940286521629314436400333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13293524347752876290933555 19940286521629314436400333)
              ·
                refine ⟨7477607445610992913650125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19940286521629314436400333 7477607445610992913650125)
                ·
                  refine ⟨2804102792104122342618797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7477607445610992913650125 2804102792104122342618797)
                  ·
                    refine ⟨1051538547039045878482049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2804102792104122342618797 1051538547039045878482049)
                    ·
                      rfl

theorem cell22_3071796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_3071796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071796 prefixEnd_3071796 := by exact prefixLift 3071796
  have htrace : WordTrace (prefixWord ++ tailWord_3071796) baseStart_3071796 baseEnd_3071796 := by
    simpa [prefixWord, tailWord_3071796, baseEnd_3071796] using wordTrace_append hprefix tailTrace_3071796
  have hstable : (prefixWord ++ tailWord_3071796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071796).length < 2 ^ (prefixWord ++ tailWord_3071796).sum := by decide
  have hdescent : baseEnd_3071796 < baseStart_3071796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071839 : List Nat := [1, 1, 2, 3, 1, 4, 2, 3, 1, 4]
def baseStart_3071839 : Nat := 118140960795 + 3071839 * 2 ^ 59
def prefixEnd_3071839 : Nat := 4983230072969 + 3 ^ 40 * 3071839 * 2
def baseEnd_3071839 : Nat := 1051553266817808099656917

theorem tailTrace_3071839 : CollatzResearch.WordTrace tailWord_3071839 prefixEnd_3071839 1051553266817808099656917 := by
  unfold tailWord_3071839
  simp only [CollatzResearch.WordTrace]
  refine ⟨112039172718259406178514571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74692781812172937452343047 112039172718259406178514571)
  ·
    refine ⟨168058759077389109267771857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112039172718259406178514571 168058759077389109267771857)
    ·
      refine ⟨126044069308041831950828893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168058759077389109267771857 126044069308041831950828893)
      ·
        refine ⟨47266525990515686981560835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126044069308041831950828893 47266525990515686981560835)
        ·
          refine ⟨70899788985773530472341253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47266525990515686981560835 70899788985773530472341253)
          ·
            refine ⟨13293710434832536963563985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70899788985773530472341253 13293710434832536963563985)
            ·
              refine ⟨9970282826124402722672989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13293710434832536963563985 9970282826124402722672989)
              ·
                refine ⟨3738856059796651021002371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9970282826124402722672989 3738856059796651021002371)
                ·
                  refine ⟨5608284089694976531503557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738856059796651021002371 5608284089694976531503557)
                  ·
                    refine ⟨1051553266817808099656917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5608284089694976531503557 1051553266817808099656917)
                    ·
                      rfl

theorem cell22_3071839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_3071839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071839 prefixEnd_3071839 := by exact prefixLift 3071839
  have htrace : WordTrace (prefixWord ++ tailWord_3071839) baseStart_3071839 baseEnd_3071839 := by
    simpa [prefixWord, tailWord_3071839, baseEnd_3071839] using wordTrace_append hprefix tailTrace_3071839
  have hstable : (prefixWord ++ tailWord_3071839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071839).length < 2 ^ (prefixWord ++ tailWord_3071839).sum := by decide
  have hdescent : baseEnd_3071839 < baseStart_3071839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071867 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 6, 4]
def baseStart_3071867 : Nat := 118140960795 + 3071867 * 2 ^ 59
def prefixEnd_3071867 : Nat := 4983230072969 + 3 ^ 40 * 3071867 * 2
def baseEnd_3071867 : Nat := 1051562851790025359956831

theorem tailTrace_3071867 : CollatzResearch.WordTrace tailWord_3071867 prefixEnd_3071867 1051562851790025359956831 := by
  unfold tailWord_3071867
  simp only [CollatzResearch.WordTrace]
  refine ⟨112040193962157966960533855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74693462641438644640355903 112040193962157966960533855)
  ·
    refine ⟨168060290943236950440800783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112040193962157966960533855 168060290943236950440800783)
    ·
      refine ⟨252090436414855425661201175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168060290943236950440800783 252090436414855425661201175)
      ·
        refine ⟨378135654622283138491801763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252090436414855425661201175 378135654622283138491801763)
        ·
          refine ⟨567203481933424707737702645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378135654622283138491801763 567203481933424707737702645)
          ·
            refine ⟨53175326431258566350409623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 567203481933424707737702645 53175326431258566350409623)
            ·
              refine ⟨79762989646887849525614435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53175326431258566350409623 79762989646887849525614435)
              ·
                refine ⟨119644484470331774288421653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79762989646887849525614435 119644484470331774288421653)
                ·
                  refine ⟨5608335209546801919769765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119644484470331774288421653 5608335209546801919769765)
                  ·
                    refine ⟨1051562851790025359956831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5608335209546801919769765 1051562851790025359956831)
                    ·
                      rfl

theorem cell22_3071867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 4].length) (baseStart_3071867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071867 prefixEnd_3071867 := by exact prefixLift 3071867
  have htrace : WordTrace (prefixWord ++ tailWord_3071867) baseStart_3071867 baseEnd_3071867 := by
    simpa [prefixWord, tailWord_3071867, baseEnd_3071867] using wordTrace_append hprefix tailTrace_3071867
  have hstable : (prefixWord ++ tailWord_3071867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071867).length < 2 ^ (prefixWord ++ tailWord_3071867).sum := by decide
  have hdescent : baseEnd_3071867 < baseStart_3071867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071903 : List Nat := [1, 1, 2, 5, 3, 1, 2, 2, 2, 3]
def baseStart_3071903 : Nat := 118140960795 + 3071903 * 2 ^ 59
def prefixEnd_3071903 : Nat := 4983230072969 + 3 ^ 40 * 3071903 * 2
def baseEnd_3071903 : Nat := 1051575175325733266056721

theorem tailTrace_3071903 : CollatzResearch.WordTrace tailWord_3071903 prefixEnd_3071903 1051575175325733266056721 := by
  unfold tailWord_3071903
  simp only [CollatzResearch.WordTrace]
  refine ⟨112041506990027545108844363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74694337993351696739229575 112041506990027545108844363)
  ·
    refine ⟨168062260485041317663266545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112041506990027545108844363 168062260485041317663266545)
    ·
      refine ⟨126046695363780988247449909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168062260485041317663266545 126046695363780988247449909)
      ·
        refine ⟨11816877690354467648198429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126046695363780988247449909 11816877690354467648198429)
        ·
          refine ⟨4431329133882925368074411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11816877690354467648198429 4431329133882925368074411)
          ·
            refine ⟨6646993700824388052111617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4431329133882925368074411 6646993700824388052111617)
            ·
              refine ⟨4985245275618291039083713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6646993700824388052111617 4985245275618291039083713)
              ·
                refine ⟨3738933956713718279312785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4985245275618291039083713 3738933956713718279312785)
                ·
                  refine ⟨2804200467535288709484589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3738933956713718279312785 2804200467535288709484589)
                  ·
                    refine ⟨1051575175325733266056721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2804200467535288709484589 1051575175325733266056721)
                    ·
                      rfl

theorem cell22_3071903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 3].length) (baseStart_3071903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071903 prefixEnd_3071903 := by exact prefixLift 3071903
  have htrace : WordTrace (prefixWord ++ tailWord_3071903) baseStart_3071903 baseEnd_3071903 := by
    simpa [prefixWord, tailWord_3071903, baseEnd_3071903] using wordTrace_append hprefix tailTrace_3071903
  have hstable : (prefixWord ++ tailWord_3071903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071903).length < 2 ^ (prefixWord ++ tailWord_3071903).sum := by decide
  have hdescent : baseEnd_3071903 < baseStart_3071903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071905 : List Nat := [1, 2, 3, 4, 2, 2, 2, 2, 4]
def baseStart_3071905 : Nat := 118140960795 + 3071905 * 2 ^ 59
def prefixEnd_3071905 : Nat := 4983230072969 + 3 ^ 40 * 3071905 * 2
def baseEnd_3071905 : Nat := 350525286655535309168905

theorem tailTrace_3071905 : CollatzResearch.WordTrace tailWord_3071905 prefixEnd_3071905 350525286655535309168905 := by
  unfold tailWord_3071905
  simp only [CollatzResearch.WordTrace]
  refine ⟨112041579936020299450417169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74694386624013532966944779 112041579936020299450417169)
  ·
    refine ⟨84031184952015224587812877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112041579936020299450417169 84031184952015224587812877)
    ·
      refine ⟨31511694357005709220429829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84031184952015224587812877 31511694357005709220429829)
      ·
        refine ⟨5908442691938570478830593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31511694357005709220429829 5908442691938570478830593)
        ·
          refine ⟨4431332018953927859122945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5908442691938570478830593 4431332018953927859122945)
          ·
            refine ⟨3323499014215445894342209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4431332018953927859122945 3323499014215445894342209)
            ·
              refine ⟨2492624260661584420756657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3323499014215445894342209 2492624260661584420756657)
              ·
                refine ⟨1869468195496188315567493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2492624260661584420756657 1869468195496188315567493)
                ·
                  refine ⟨350525286655535309168905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1869468195496188315567493 350525286655535309168905)
                  ·
                    rfl

theorem cell22_3071905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 4].length) (baseStart_3071905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071905 prefixEnd_3071905 := by exact prefixLift 3071905
  have htrace : WordTrace (prefixWord ++ tailWord_3071905) baseStart_3071905 baseEnd_3071905 := by
    simpa [prefixWord, tailWord_3071905, baseEnd_3071905] using wordTrace_append hprefix tailTrace_3071905
  have hstable : (prefixWord ++ tailWord_3071905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071905).length < 2 ^ (prefixWord ++ tailWord_3071905).sum := by decide
  have hdescent : baseEnd_3071905 < baseStart_3071905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071927 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 9]
def baseStart_3071927 : Nat := 118140960795 + 3071927 * 2 ^ 59
def prefixEnd_3071927 : Nat := 4983230072969 + 3 ^ 40 * 3071927 * 2
def baseEnd_3071927 : Nat := 350527797005401734485549

theorem tailTrace_3071927 : CollatzResearch.WordTrace tailWord_3071927 prefixEnd_3071927 350527797005401734485549 := by
  unfold tailWord_3071927
  simp only [CollatzResearch.WordTrace]
  refine ⟨112042382341940597207718035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74694921561293731471812023 112042382341940597207718035)
  ·
    refine ⟨168063573512910895811577053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112042382341940597207718035 168063573512910895811577053)
    ·
      refine ⟨63023840067341585929341395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168063573512910895811577053 63023840067341585929341395)
      ·
        refine ⟨94535760101012378894012093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63023840067341585929341395 94535760101012378894012093)
        ·
          refine ⟨35450910037879642085254535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94535760101012378894012093 35450910037879642085254535)
          ·
            refine ⟨53176365056819463127881803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35450910037879642085254535 53176365056819463127881803)
            ·
              refine ⟨79764547585229194691822705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53176365056819463127881803 79764547585229194691822705)
              ·
                refine ⟨59823410688921896018867029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79764547585229194691822705 59823410688921896018867029)
                ·
                  refine ⟨350527797005401734485549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59823410688921896018867029 350527797005401734485549)
                  ·
                    rfl

theorem cell22_3071927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 9].length) (baseStart_3071927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071927 prefixEnd_3071927 := by exact prefixLift 3071927
  have htrace : WordTrace (prefixWord ++ tailWord_3071927) baseStart_3071927 baseEnd_3071927 := by
    simpa [prefixWord, tailWord_3071927, baseEnd_3071927] using wordTrace_append hprefix tailTrace_3071927
  have hstable : (prefixWord ++ tailWord_3071927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071927).length < 2 ^ (prefixWord ++ tailWord_3071927).sum := by decide
  have hdescent : baseEnd_3071927 < baseStart_3071927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071948 : List Nat := [2, 2, 1, 4, 1, 2, 1, 5, 1, 3]
def baseStart_3071948 : Nat := 118140960795 + 3071948 * 2 ^ 59
def prefixEnd_3071948 : Nat := 4983230072969 + 3 ^ 40 * 3071948 * 2
def baseEnd_3071948 : Nat := 1051590579745368148681583

theorem tailTrace_3071948 : CollatzResearch.WordTrace tailWord_3071948 prefixEnd_3071948 1051590579745368148681583 := by
  unfold tailWord_3071948
  simp only [CollatzResearch.WordTrace]
  refine ⟨56021574137432258897116249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74695432183243011862821665 56021574137432258897116249)
  ·
    refine ⟨42016180603074194172837187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56021574137432258897116249 42016180603074194172837187)
    ·
      refine ⟨63024270904611291259255781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42016180603074194172837187 63024270904611291259255781)
      ·
        refine ⟨11817050794614617111110459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63024270904611291259255781 11817050794614617111110459)
        ·
          refine ⟨17725576191921925666665689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11817050794614617111110459 17725576191921925666665689)
          ·
            refine ⟨13294182143941444249999267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17725576191921925666665689 13294182143941444249999267)
            ·
              refine ⟨19941273215912166374998901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13294182143941444249999267 19941273215912166374998901)
              ·
                refine ⟨1869494363991765597656147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19941273215912166374998901 1869494363991765597656147)
                ·
                  refine ⟨2804241545987648396484221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869494363991765597656147 2804241545987648396484221)
                  ·
                    refine ⟨1051590579745368148681583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2804241545987648396484221 1051590579745368148681583)
                    ·
                      rfl

theorem cell22_3071948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_3071948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3071948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3071948 prefixEnd_3071948 := by exact prefixLift 3071948
  have htrace : WordTrace (prefixWord ++ tailWord_3071948) baseStart_3071948 baseEnd_3071948 := by
    simpa [prefixWord, tailWord_3071948, baseEnd_3071948] using wordTrace_append hprefix tailTrace_3071948
  have hstable : (prefixWord ++ tailWord_3071948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071948).length < 2 ^ (prefixWord ++ tailWord_3071948).sum := by decide
  have hdescent : baseEnd_3071948 < baseStart_3071948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072019 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 4, 4]
def baseStart_3072019 : Nat := 118140960795 + 3072019 * 2 ^ 59
def prefixEnd_3072019 : Nat := 4983230072969 + 3 ^ 40 * 3072019 * 2
def baseEnd_3072019 : Nat := 1051614884496347630156365

theorem tailTrace_3072019 : CollatzResearch.WordTrace tailWord_3072019 prefixEnd_3072019 1051614884496347630156365 := by
  unfold tailWord_3072019
  simp only [CollatzResearch.WordTrace]
  refine ⟨112045737857607296920067111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74697158571738197946711407 112045737857607296920067111)
  ·
    refine ⟨168068606786410945380100667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112045737857607296920067111 168068606786410945380100667)
    ·
      refine ⟨252102910179616418070151001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168068606786410945380100667 252102910179616418070151001)
      ·
        refine ⟨189077182634712313552613251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252102910179616418070151001 189077182634712313552613251)
        ·
          refine ⟨283615773952068470328919877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189077182634712313552613251 283615773952068470328919877)
          ·
            refine ⟨53177957616012838186672477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283615773952068470328919877 53177957616012838186672477)
            ·
              refine ⟨19941734106004814320002179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53177957616012838186672477 19941734106004814320002179)
              ·
                refine ⟨29912601159007221480003269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19941734106004814320002179 29912601159007221480003269)
                ·
                  refine ⟨5608612717313854027500613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29912601159007221480003269 5608612717313854027500613)
                  ·
                    refine ⟨1051614884496347630156365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5608612717313854027500613 1051614884496347630156365)
                    ·
                      rfl

theorem cell22_3072019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 4].length) (baseStart_3072019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072019 prefixEnd_3072019 := by exact prefixLift 3072019
  have htrace : WordTrace (prefixWord ++ tailWord_3072019) baseStart_3072019 baseEnd_3072019 := by
    simpa [prefixWord, tailWord_3072019, baseEnd_3072019] using wordTrace_append hprefix tailTrace_3072019
  have hstable : (prefixWord ++ tailWord_3072019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072019).length < 2 ^ (prefixWord ++ tailWord_3072019).sum := by decide
  have hdescent : baseEnd_3072019 < baseStart_3072019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072023 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 6]
def baseStart_3072023 : Nat := 118140960795 + 3072023 * 2 ^ 59
def prefixEnd_3072023 : Nat := 4983230072969 + 3 ^ 40 * 3072023 * 2
def baseEnd_3072023 : Nat := 350538751259364317685451

theorem tailTrace_3072023 : CollatzResearch.WordTrace tailWord_3072023 prefixEnd_3072023 350538751259364317685451 := by
  unfold tailWord_3072023
  simp only [CollatzResearch.WordTrace]
  refine ⟨112045883749592805603212723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74697255833061870402141815 112045883749592805603212723)
  ·
    refine ⟨168068825624389208404819085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112045883749592805603212723 168068825624389208404819085)
    ·
      refine ⟨63025809609145953151807157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168068825624389208404819085 63025809609145953151807157)
      ·
        refine ⟨5908669650857433107981921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63025809609145953151807157 5908669650857433107981921)
        ·
          refine ⟨4431502238143074830986441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5908669650857433107981921 4431502238143074830986441)
          ·
            refine ⟨3323626678607306123239831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4431502238143074830986441 3323626678607306123239831)
            ·
              refine ⟨4985440017910959184859747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3323626678607306123239831 4985440017910959184859747)
              ·
                refine ⟨7478160026866438777289621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4985440017910959184859747 7478160026866438777289621)
                ·
                  refine ⟨350538751259364317685451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7478160026866438777289621 350538751259364317685451)
                  ·
                    rfl

theorem cell22_3072023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 6].length) (baseStart_3072023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072023 prefixEnd_3072023 := by exact prefixLift 3072023
  have htrace : WordTrace (prefixWord ++ tailWord_3072023) baseStart_3072023 baseEnd_3072023 := by
    simpa [prefixWord, tailWord_3072023, baseEnd_3072023] using wordTrace_append hprefix tailTrace_3072023
  have hstable : (prefixWord ++ tailWord_3072023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072023).length < 2 ^ (prefixWord ++ tailWord_3072023).sum := by decide
  have hdescent : baseEnd_3072023 < baseStart_3072023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072096 : List Nat := [2, 1, 1, 3, 2, 3, 2, 3, 5]
def baseStart_3072096 : Nat := 118140960795 + 3072096 * 2 ^ 59
def prefixEnd_3072096 : Nat := 4983230072969 + 3 ^ 40 * 3072096 * 2
def baseEnd_3072096 : Nat := 350547081056648365327043

theorem tailTrace_3072096 : CollatzResearch.WordTrace tailWord_3072096 prefixEnd_3072096 350547081056648365327043 := by
  unfold tailWord_3072096
  simp only [CollatzResearch.WordTrace]
  refine ⟨56024273139164169535310071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74699030852218892713746761 56024273139164169535310071)
  ·
    refine ⟨84036409708746254302965107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56024273139164169535310071 84036409708746254302965107)
    ·
      refine ⟨126054614563119381454447661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84036409708746254302965107 126054614563119381454447661)
      ·
        refine ⟨47270480461169768045417873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126054614563119381454447661 47270480461169768045417873)
        ·
          refine ⟨35452860345877326034063405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47270480461169768045417873 35452860345877326034063405)
          ·
            refine ⟨13294822629703997262773777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35452860345877326034063405 13294822629703997262773777)
            ·
              refine ⟨9971116972277997947080333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13294822629703997262773777 9971116972277997947080333)
              ·
                refine ⟨3739168864604249230155125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9971116972277997947080333 3739168864604249230155125)
                ·
                  refine ⟨350547081056648365327043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3739168864604249230155125 350547081056648365327043)
                  ·
                    rfl

theorem cell22_3072096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 5].length) (baseStart_3072096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072096 prefixEnd_3072096 := by exact prefixLift 3072096
  have htrace : WordTrace (prefixWord ++ tailWord_3072096) baseStart_3072096 baseEnd_3072096 := by
    simpa [prefixWord, tailWord_3072096, baseEnd_3072096] using wordTrace_append hprefix tailTrace_3072096
  have hstable : (prefixWord ++ tailWord_3072096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072096).length < 2 ^ (prefixWord ++ tailWord_3072096).sum := by decide
  have hdescent : baseEnd_3072096 < baseStart_3072096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072139 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 2, 9]
def baseStart_3072139 : Nat := 118140960795 + 3072139 * 2 ^ 59
def prefixEnd_3072139 : Nat := 4983230072969 + 3 ^ 40 * 3072139 * 2
def baseEnd_3072139 : Nat := 1051655962948707317155997

theorem tailTrace_3072139 : CollatzResearch.WordTrace tailWord_3072139 prefixEnd_3072139 1051655962948707317155997 := by
  unfold tailWord_3072139
  simp only [CollatzResearch.WordTrace]
  refine ⟨112050114617172557414435471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74700076411448371609623647 112050114617172557414435471)
  ·
    refine ⟨168075171925758836121653207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112050114617172557414435471 168075171925758836121653207)
    ·
      refine ⟨252112757888638254182479811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168075171925758836121653207 252112757888638254182479811)
      ·
        refine ⟨378169136832957381273719717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252112757888638254182479811 378169136832957381273719717)
        ·
          refine ⟨70906713156179508988822447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 378169136832957381273719717 70906713156179508988822447)
          ·
            refine ⟨106360069734269263483233671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70906713156179508988822447 106360069734269263483233671)
            ·
              refine ⟨159540104601403895224850507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106360069734269263483233671 159540104601403895224850507)
              ·
                refine ⟨239310156902105842837275761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159540104601403895224850507 239310156902105842837275761)
                ·
                  refine ⟨179482617676579382127956821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239310156902105842837275761 179482617676579382127956821)
                  ·
                    refine ⟨1051655962948707317155997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 179482617676579382127956821 1051655962948707317155997)
                    ·
                      rfl

theorem cell22_3072139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_3072139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072139 prefixEnd_3072139 := by exact prefixLift 3072139
  have htrace : WordTrace (prefixWord ++ tailWord_3072139) baseStart_3072139 baseEnd_3072139 := by
    simpa [prefixWord, tailWord_3072139, baseEnd_3072139] using wordTrace_append hprefix tailTrace_3072139
  have hstable : (prefixWord ++ tailWord_3072139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072139).length < 2 ^ (prefixWord ++ tailWord_3072139).sum := by decide
  have hdescent : baseEnd_3072139 < baseStart_3072139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072218 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 3, 3]
def baseStart_3072218 : Nat := 118140960795 + 3072218 * 2 ^ 59
def prefixEnd_3072218 : Nat := 4983230072969 + 3 ^ 40 * 3072218 * 2
def baseEnd_3072218 : Nat := 1051683006263177444430755

theorem tailTrace_3072218 : CollatzResearch.WordTrace tailWord_3072218 prefixEnd_3072218 1051683006263177444430755 := by
  unfold tailWord_3072218
  simp only [CollatzResearch.WordTrace]
  refine ⟨28013248995971588476640327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74701997322590902604374205 28013248995971588476640327)
  ·
    refine ⟨42019873493957382714960491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28013248995971588476640327 42019873493957382714960491)
    ·
      refine ⟨63029810240936074072440737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42019873493957382714960491 63029810240936074072440737)
      ·
        refine ⟨47272357680702055554330553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63029810240936074072440737 47272357680702055554330553)
        ·
          refine ⟨35454268260526541665747915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47272357680702055554330553 35454268260526541665747915)
          ·
            refine ⟨53181402390789812498621873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35454268260526541665747915 53181402390789812498621873)
            ·
              refine ⟨39886051793092359373966405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53181402390789812498621873 39886051793092359373966405)
              ·
                refine ⟨7478634711204817382618701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39886051793092359373966405 7478634711204817382618701)
                ·
                  refine ⟨2804488016701806518482013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7478634711204817382618701 2804488016701806518482013)
                  ·
                    refine ⟨1051683006263177444430755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2804488016701806518482013 1051683006263177444430755)
                    ·
                      rfl

theorem cell22_3072218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_3072218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072218 prefixEnd_3072218 := by exact prefixLift 3072218
  have htrace : WordTrace (prefixWord ++ tailWord_3072218) baseStart_3072218 baseEnd_3072218 := by
    simpa [prefixWord, tailWord_3072218, baseEnd_3072218] using wordTrace_append hprefix tailTrace_3072218
  have hstable : (prefixWord ++ tailWord_3072218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072218).length < 2 ^ (prefixWord ++ tailWord_3072218).sum := by decide
  have hdescent : baseEnd_3072218 < baseStart_3072218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072235 : List Nat := [1, 1, 1, 1, 2, 5, 2, 5, 1, 3]
def baseStart_3072235 : Nat := 118140960795 + 3072235 * 2 ^ 59
def prefixEnd_3072235 : Nat := 4983230072969 + 3 ^ 40 * 3072235 * 2
def baseEnd_3072235 : Nat := 1051688825710595066755703

theorem tailTrace_3072235 : CollatzResearch.WordTrace tailWord_3072235 prefixEnd_3072235 1051688825710595066755703 := by
  unfold tailWord_3072235
  simp only [CollatzResearch.WordTrace]
  refine ⟨112053616024824765809930159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74702410683216510539953439 112053616024824765809930159)
  ·
    refine ⟨168080424037237148714895239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112053616024824765809930159 168080424037237148714895239)
    ·
      refine ⟨252120636055855723072342859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168080424037237148714895239 252120636055855723072342859)
      ·
        refine ⟨378180954083783584608514289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252120636055855723072342859 378180954083783584608514289)
        ·
          refine ⟨283635715562837688456385717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378180954083783584608514289 283635715562837688456385717)
          ·
            refine ⟨26590848334016033292786161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 283635715562837688456385717 26590848334016033292786161)
            ·
              refine ⟨19943136250512024969589621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26590848334016033292786161 19943136250512024969589621)
              ·
                refine ⟨1869669023485502340899027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19943136250512024969589621 1869669023485502340899027)
                ·
                  refine ⟨2804503535228253511348541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869669023485502340899027 2804503535228253511348541)
                  ·
                    refine ⟨1051688825710595066755703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2804503535228253511348541 1051688825710595066755703)
                    ·
                      rfl

theorem cell22_3072235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 1, 3].length) (baseStart_3072235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072235 prefixEnd_3072235 := by exact prefixLift 3072235
  have htrace : WordTrace (prefixWord ++ tailWord_3072235) baseStart_3072235 baseEnd_3072235 := by
    simpa [prefixWord, tailWord_3072235, baseEnd_3072235] using wordTrace_append hprefix tailTrace_3072235
  have hstable : (prefixWord ++ tailWord_3072235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072235).length < 2 ^ (prefixWord ++ tailWord_3072235).sum := by decide
  have hdescent : baseEnd_3072235 < baseStart_3072235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072252 : List Nat := [2, 2, 2, 1, 4, 2, 1, 4, 1, 3]
def baseStart_3072252 : Nat := 118140960795 + 3072252 * 2 ^ 59
def prefixEnd_3072252 : Nat := 4983230072969 + 3 ^ 40 * 3072252 * 2
def baseEnd_3072252 : Nat := 1051694645158012689080651

theorem tailTrace_3072252 : CollatzResearch.WordTrace tailWord_3072252 prefixEnd_3072252 1051694645158012689080651 := by
  unfold tailWord_3072252
  simp only [CollatzResearch.WordTrace]
  refine ⟨56027118032881588856649505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74702824043842118475532673 56027118032881588856649505)
  ·
    refine ⟨42020338524661191642487129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56027118032881588856649505 42020338524661191642487129)
    ·
      refine ⟨31515253893495893731865347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42020338524661191642487129 31515253893495893731865347)
      ·
        refine ⟨47272880840243840597798021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31515253893495893731865347 47272880840243840597798021)
        ·
          refine ⟨8863665157545720112087129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47272880840243840597798021 8863665157545720112087129)
          ·
            refine ⟨6647748868159290084065347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8863665157545720112087129 6647748868159290084065347)
            ·
              refine ⟨9971623302238935126098021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6647748868159290084065347 9971623302238935126098021)
              ·
                refine ⟨1869679369169800336143379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9971623302238935126098021 1869679369169800336143379)
                ·
                  refine ⟨2804519053754700504215069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869679369169800336143379 2804519053754700504215069)
                  ·
                    refine ⟨1051694645158012689080651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2804519053754700504215069 1051694645158012689080651)
                    ·
                      rfl

theorem cell22_3072252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_3072252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072252 prefixEnd_3072252 := by exact prefixLift 3072252
  have htrace : WordTrace (prefixWord ++ tailWord_3072252) baseStart_3072252 baseEnd_3072252 := by
    simpa [prefixWord, tailWord_3072252, baseEnd_3072252] using wordTrace_append hprefix tailTrace_3072252
  have hstable : (prefixWord ++ tailWord_3072252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072252).length < 2 ^ (prefixWord ++ tailWord_3072252).sum := by decide
  have hdescent : baseEnd_3072252 < baseStart_3072252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072286 : List Nat := [4, 3, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3072286 : Nat := 118140960795 + 3072286 * 2 ^ 59
def prefixEnd_3072286 : Nat := 4983230072969 + 3 ^ 40 * 3072286 * 2
def baseEnd_3072286 : Nat := 1051706284052847933730547

theorem tailTrace_3072286 : CollatzResearch.WordTrace tailWord_3072286 prefixEnd_3072286 1051706284052847933730547 := by
  unfold tailWord_3072286
  simp only [CollatzResearch.WordTrace]
  refine ⟨14006934518455000190004589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74703650765093334346691141 14006934518455000190004589)
  ·
    refine ⟨5252600444420625071251721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14006934518455000190004589 5252600444420625071251721)
    ·
      refine ⟨3939450333315468803438791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5252600444420625071251721 3939450333315468803438791)
      ·
        refine ⟨5909175499973203205158187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3939450333315468803438791 5909175499973203205158187)
        ·
          refine ⟨8863763249959804807737281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5909175499973203205158187 8863763249959804807737281)
          ·
            refine ⟨6647822437469853605802961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8863763249959804807737281 6647822437469853605802961)
            ·
              refine ⟨4985866828102390204352221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6647822437469853605802961 4985866828102390204352221)
              ·
                refine ⟨1869700060538396326632083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4985866828102390204352221 1869700060538396326632083)
                ·
                  refine ⟨2804550090807594489948125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869700060538396326632083 2804550090807594489948125)
                  ·
                    refine ⟨1051706284052847933730547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2804550090807594489948125 1051706284052847933730547)
                    ·
                      rfl

theorem cell22_3072286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3072286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072286 prefixEnd_3072286 := by exact prefixLift 3072286
  have htrace : WordTrace (prefixWord ++ tailWord_3072286) baseStart_3072286 baseEnd_3072286 := by
    simpa [prefixWord, tailWord_3072286, baseEnd_3072286] using wordTrace_append hprefix tailTrace_3072286
  have hstable : (prefixWord ++ tailWord_3072286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072286).length < 2 ^ (prefixWord ++ tailWord_3072286).sum := by decide
  have hdescent : baseEnd_3072286 < baseStart_3072286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072383 : List Nat := [1, 1, 2, 2, 1, 1, 2, 7, 5]
def baseStart_3072383 : Nat := 118140960795 + 3072383 * 2 ^ 59
def prefixEnd_3072383 : Nat := 4983230072969 + 3 ^ 40 * 3072383 * 2
def baseEnd_3072383 : Nat := 350579829711724004685083

theorem tailTrace_3072383 : CollatzResearch.WordTrace tailWord_3072383 prefixEnd_3072383 350579829711724004685083 := by
  unfold tailWord_3072383
  simp only [CollatzResearch.WordTrace]
  refine ⟨112059014028288587086317803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74706009352192391390878535 112059014028288587086317803)
  ·
    refine ⟨168088521042432880629476705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112059014028288587086317803 168088521042432880629476705)
    ·
      refine ⟨126066390781824660472107529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168088521042432880629476705 126066390781824660472107529)
      ·
        refine ⟨94549793086368495354080647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126066390781824660472107529 94549793086368495354080647)
        ·
          refine ⟨141824689629552743031120971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94549793086368495354080647 141824689629552743031120971)
          ·
            refine ⟨212737034444329114546681457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141824689629552743031120971 212737034444329114546681457)
            ·
              refine ⟨159552775833246835910011093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212737034444329114546681457 159552775833246835910011093)
              ·
                refine ⟨3739518183591722716640885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 159552775833246835910011093 3739518183591722716640885)
                ·
                  refine ⟨350579829711724004685083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3739518183591722716640885 350579829711724004685083)
                  ·
                    rfl

theorem cell22_3072383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 5].length) (baseStart_3072383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072383 prefixEnd_3072383 := by exact prefixLift 3072383
  have htrace : WordTrace (prefixWord ++ tailWord_3072383) baseStart_3072383 baseEnd_3072383 := by
    simpa [prefixWord, tailWord_3072383, baseEnd_3072383] using wordTrace_append hprefix tailTrace_3072383
  have hstable : (prefixWord ++ tailWord_3072383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072383).length < 2 ^ (prefixWord ++ tailWord_3072383).sum := by decide
  have hdescent : baseEnd_3072383 < baseStart_3072383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072428 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 6]
def baseStart_3072428 : Nat := 118140960795 + 3072428 * 2 ^ 59
def prefixEnd_3072428 : Nat := 4983230072969 + 3 ^ 40 * 3072428 * 2
def baseEnd_3072428 : Nat := 350584964518268965560037

theorem tailTrace_3072428 : CollatzResearch.WordTrace tailWord_3072428 prefixEnd_3072428 350584964518268965560037 := by
  unfold tailWord_3072428
  simp only [CollatzResearch.WordTrace]
  refine ⟨56030327656562779885852969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74707103542083706514470625 56030327656562779885852969)
  ·
    refine ⟨42022745742422084914389727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56030327656562779885852969 42022745742422084914389727)
    ·
      refine ⟨63034118613633127371584591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42022745742422084914389727 63034118613633127371584591)
      ·
        refine ⟨94551177920449691057376887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63034118613633127371584591 94551177920449691057376887)
        ·
          refine ⟨141826766880674536586065331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94551177920449691057376887 141826766880674536586065331)
          ·
            refine ⟨212740150321011804879097997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141826766880674536586065331 212740150321011804879097997)
            ·
              refine ⟨79777556370379426829661749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212740150321011804879097997 79777556370379426829661749)
              ·
                refine ⟨7479145909723071265280789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79777556370379426829661749 7479145909723071265280789)
                ·
                  refine ⟨350584964518268965560037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7479145909723071265280789 350584964518268965560037)
                  ·
                    rfl

theorem cell22_3072428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_3072428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072428 prefixEnd_3072428 := by exact prefixLift 3072428
  have htrace : WordTrace (prefixWord ++ tailWord_3072428) baseStart_3072428 baseEnd_3072428 := by
    simpa [prefixWord, tailWord_3072428, baseEnd_3072428] using wordTrace_append hprefix tailTrace_3072428
  have hstable : (prefixWord ++ tailWord_3072428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072428).length < 2 ^ (prefixWord ++ tailWord_3072428).sum := by decide
  have hdescent : baseEnd_3072428 < baseStart_3072428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072445 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 6]
def baseStart_3072445 : Nat := 118140960795 + 3072445 * 2 ^ 59
def prefixEnd_3072445 : Nat := 4983230072969 + 3 ^ 40 * 3072445 * 2
def baseEnd_3072445 : Nat := 350586904334074839668353

theorem tailTrace_3072445 : CollatzResearch.WordTrace tailWord_3072445 prefixEnd_3072445 350586904334074839668353 := by
  unfold tailWord_3072445
  simp only [CollatzResearch.WordTrace]
  refine ⟨112061275354063971675074789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74707516902709314450049859 112061275354063971675074789)
  ·
    refine ⟨21011489128886994689076523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112061275354063971675074789 21011489128886994689076523)
    ·
      refine ⟨31517233693330492033614785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21011489128886994689076523 31517233693330492033614785)
      ·
        refine ⟨23637925269997869025211089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31517233693330492033614785 23637925269997869025211089)
        ·
          refine ⟨17728443952498401768908317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23637925269997869025211089 17728443952498401768908317)
          ·
            refine ⟨6648166482186900663340619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17728443952498401768908317 6648166482186900663340619)
            ·
              refine ⟨9972249723280350995010929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6648166482186900663340619 9972249723280350995010929)
              ·
                refine ⟨7479187292460263246258197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9972249723280350995010929 7479187292460263246258197)
                ·
                  refine ⟨350586904334074839668353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7479187292460263246258197 350586904334074839668353)
                  ·
                    rfl

theorem cell22_3072445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_3072445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072445 prefixEnd_3072445 := by exact prefixLift 3072445
  have htrace : WordTrace (prefixWord ++ tailWord_3072445) baseStart_3072445 baseEnd_3072445 := by
    simpa [prefixWord, tailWord_3072445, baseEnd_3072445] using wordTrace_append hprefix tailTrace_3072445
  have hstable : (prefixWord ++ tailWord_3072445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072445).length < 2 ^ (prefixWord ++ tailWord_3072445).sum := by decide
  have hdescent : baseEnd_3072445 < baseStart_3072445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072473 : List Nat := [1, 2, 1, 2, 4, 1, 11]
def baseStart_3072473 : Nat := 118140960795 + 3072473 * 2 ^ 59
def prefixEnd_3072473 : Nat := 4983230072969 + 3 ^ 40 * 3072473 * 2
def baseEnd_3072473 : Nat := 38954455480534880714999

theorem tailTrace_3072473 : CollatzResearch.WordTrace tailWord_3072473 prefixEnd_3072473 38954455480534880714999 := by
  unfold tailWord_3072473
  simp only [CollatzResearch.WordTrace]
  refine ⟨112062296597962532457094073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74708197731975021638062715 112062296597962532457094073)
  ·
    refine ⟨84046722448471899342820555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112062296597962532457094073 84046722448471899342820555)
    ·
      refine ⟨126070083672707849014230833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84046722448471899342820555 126070083672707849014230833)
      ·
        refine ⟨94552562754530886760673125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126070083672707849014230833 94552562754530886760673125)
        ·
          refine ⟨17728605516474541267626211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94552562754530886760673125 17728605516474541267626211)
          ·
            refine ⟨26592908274711811901439317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17728605516474541267626211 26592908274711811901439317)
            ·
              refine ⟨38954455480534880714999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26592908274711811901439317 38954455480534880714999)
              ·
                rfl

theorem cell22_3072473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 11].length) (baseStart_3072473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072473 prefixEnd_3072473 := by exact prefixLift 3072473
  have htrace : WordTrace (prefixWord ++ tailWord_3072473) baseStart_3072473 baseEnd_3072473 := by
    simpa [prefixWord, tailWord_3072473, baseEnd_3072473] using wordTrace_append hprefix tailTrace_3072473
  have hstable : (prefixWord ++ tailWord_3072473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072473).length < 2 ^ (prefixWord ++ tailWord_3072473).sum := by decide
  have hdescent : baseEnd_3072473 < baseStart_3072473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072477 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_3072477 : Nat := 118140960795 + 3072477 * 2 ^ 59
def prefixEnd_3072477 : Nat := 4983230072969 + 3 ^ 40 * 3072477 * 2
def baseEnd_3072477 : Nat := 1051771667256187102204961

theorem tailTrace_3072477 : CollatzResearch.WordTrace tailWord_3072477 prefixEnd_3072477 1051771667256187102204961 := by
  unfold tailWord_3072477
  simp only [CollatzResearch.WordTrace]
  refine ⟨112062442489948041140239685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74708294993298694093493123 112062442489948041140239685)
  ·
    refine ⟨21011707966865257713794941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112062442489948041140239685 21011707966865257713794941)
    ·
      refine ⟨7879390487574471642673103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21011707966865257713794941 7879390487574471642673103)
      ·
        refine ⟨11819085731361707464009655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7879390487574471642673103 11819085731361707464009655)
        ·
          refine ⟨17728628597042561196014483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11819085731361707464009655 17728628597042561196014483)
          ·
            refine ⟨26592942895563841794021725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17728628597042561196014483 26592942895563841794021725)
            ·
              refine ⟨9972353585836440672758147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26592942895563841794021725 9972353585836440672758147)
              ·
                refine ⟨14958530378754661009137221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9972353585836440672758147 14958530378754661009137221)
                ·
                  refine ⟨2804724446016498939213229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14958530378754661009137221 2804724446016498939213229)
                  ·
                    refine ⟨1051771667256187102204961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2804724446016498939213229 1051771667256187102204961)
                    ·
                      rfl

theorem cell22_3072477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_3072477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072477 prefixEnd_3072477 := by exact prefixLift 3072477
  have htrace : WordTrace (prefixWord ++ tailWord_3072477) baseStart_3072477 baseEnd_3072477 := by
    simpa [prefixWord, tailWord_3072477, baseEnd_3072477] using wordTrace_append hprefix tailTrace_3072477
  have hstable : (prefixWord ++ tailWord_3072477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072477).length < 2 ^ (prefixWord ++ tailWord_3072477).sum := by decide
  have hdescent : baseEnd_3072477 < baseStart_3072477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072503 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 3, 8]
def baseStart_3072503 : Nat := 118140960795 + 3072503 * 2 ^ 59
def prefixEnd_3072503 : Nat := 4983230072969 + 3 ^ 40 * 3072503 * 2
def baseEnd_3072503 : Nat := 1051780567587531701054881

theorem tailTrace_3072503 : CollatzResearch.WordTrace tailWord_3072503 prefixEnd_3072503 1051780567587531701054881 := by
  unfold tailWord_3072503
  simp only [CollatzResearch.WordTrace]
  refine ⟨112063390787853847580686163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74708927191902565053790775 112063390787853847580686163)
  ·
    refine ⟨168095086181780771371029245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112063390787853847580686163 168095086181780771371029245)
    ·
      refine ⟨63035657318167789264135967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168095086181780771371029245 63035657318167789264135967)
      ·
        refine ⟨94553485977251683896203951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63035657318167789264135967 94553485977251683896203951)
        ·
          refine ⟨141830228965877525844305927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94553485977251683896203951 141830228965877525844305927)
          ·
            refine ⟨212745343448816288766458891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141830228965877525844305927 212745343448816288766458891)
            ·
              refine ⟨319118015173224433149688337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212745343448816288766458891 319118015173224433149688337)
              ·
                refine ⟨239338511379918324862266253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319118015173224433149688337 239338511379918324862266253)
                ·
                  refine ⟨89751941767469371823349845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239338511379918324862266253 89751941767469371823349845)
                  ·
                    refine ⟨1051780567587531701054881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89751941767469371823349845 1051780567587531701054881)
                    ·
                      rfl

theorem cell22_3072503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_3072503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072503 prefixEnd_3072503 := by exact prefixLift 3072503
  have htrace : WordTrace (prefixWord ++ tailWord_3072503) baseStart_3072503 baseEnd_3072503 := by
    simpa [prefixWord, tailWord_3072503, baseEnd_3072503] using wordTrace_append hprefix tailTrace_3072503
  have hstable : (prefixWord ++ tailWord_3072503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072503).length < 2 ^ (prefixWord ++ tailWord_3072503).sum := by decide
  have hdescent : baseEnd_3072503 < baseStart_3072503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072612 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_3072612 : Nat := 118140960795 + 3072612 * 2 ^ 59
def prefixEnd_3072612 : Nat := 4983230072969 + 3 ^ 40 * 3072612 * 2
def baseEnd_3072612 : Nat := 1051817880515091750079547

theorem tailTrace_3072612 : CollatzResearch.WordTrace tailWord_3072612 prefixEnd_3072612 1051817880515091750079547 := by
  unfold tailWord_3072612
  simp only [CollatzResearch.WordTrace]
  refine ⟨56033683172229479598202045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74711577562972639464269393 56033683172229479598202045)
  ·
    refine ⟨21012631189586054849325767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56033683172229479598202045 21012631189586054849325767)
    ·
      refine ⟨31518946784379082273988651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21012631189586054849325767 31518946784379082273988651)
      ·
        refine ⟨47278420176568623410982977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31518946784379082273988651 47278420176568623410982977)
        ·
          refine ⟨35458815132426467558237233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47278420176568623410982977 35458815132426467558237233)
          ·
            refine ⟨26594111349319850668677925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35458815132426467558237233 26594111349319850668677925)
            ·
              refine ⟨4986395877997472000377111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26594111349319850668677925 4986395877997472000377111)
              ·
                refine ⟨7479593816996208000565667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4986395877997472000377111 7479593816996208000565667)
                ·
                  refine ⟨11219390725494312000848501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7479593816996208000565667 11219390725494312000848501)
                  ·
                    refine ⟨1051817880515091750079547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11219390725494312000848501 1051817880515091750079547)
                    ·
                      rfl

theorem cell22_3072612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_3072612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072612 prefixEnd_3072612 := by exact prefixLift 3072612
  have htrace : WordTrace (prefixWord ++ tailWord_3072612) baseStart_3072612 baseEnd_3072612 := by
    simpa [prefixWord, tailWord_3072612, baseEnd_3072612] using wordTrace_append hprefix tailTrace_3072612
  have hstable : (prefixWord ++ tailWord_3072612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072612).length < 2 ^ (prefixWord ++ tailWord_3072612).sum := by decide
  have hdescent : baseEnd_3072612 < baseStart_3072612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072691 : List Nat := [1, 1, 1, 2, 3, 4, 3, 3, 1, 3]
def baseStart_3072691 : Nat := 118140960795 + 3072691 * 2 ^ 59
def prefixEnd_3072691 : Nat := 4983230072969 + 3 ^ 40 * 3072691 * 2
def baseEnd_3072691 : Nat := 1051844923829561877354305

theorem tailTrace_3072691 : CollatzResearch.WordTrace tailWord_3072691 prefixEnd_3072691 1051844923829561877354305 := by
  unfold tailWord_3072691
  simp only [CollatzResearch.WordTrace]
  refine ⟨112070247711172755688529927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74713498474115170459019951 112070247711172755688529927)
  ·
    refine ⟨168105371566759133532794891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112070247711172755688529927 168105371566759133532794891)
    ·
      refine ⟨252158057350138700299192337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168105371566759133532794891 252158057350138700299192337)
      ·
        refine ⟨189118543012604025224394253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252158057350138700299192337 189118543012604025224394253)
        ·
          refine ⟨70919453629726509459147845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189118543012604025224394253 70919453629726509459147845)
          ·
            refine ⟨13297397555573720523590221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70919453629726509459147845 13297397555573720523590221)
            ·
              refine ⟨4986524083340145196346333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13297397555573720523590221 4986524083340145196346333)
              ·
                refine ⟨1869946531252554448629875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4986524083340145196346333 1869946531252554448629875)
                ·
                  refine ⟨2804919796878831672944813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869946531252554448629875 2804919796878831672944813)
                  ·
                    refine ⟨1051844923829561877354305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2804919796878831672944813 1051844923829561877354305)
                    ·
                      rfl

theorem cell22_3072691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 1, 3].length) (baseStart_3072691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072691 prefixEnd_3072691 := by exact prefixLift 3072691
  have htrace : WordTrace (prefixWord ++ tailWord_3072691) baseStart_3072691 baseEnd_3072691 := by
    simpa [prefixWord, tailWord_3072691, baseEnd_3072691] using wordTrace_append hprefix tailTrace_3072691
  have hstable : (prefixWord ++ tailWord_3072691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072691).length < 2 ^ (prefixWord ++ tailWord_3072691).sum := by decide
  have hdescent : baseEnd_3072691 < baseStart_3072691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072751 : List Nat := [1, 1, 2, 1, 5, 3, 3, 1, 1, 4]
def baseStart_3072751 : Nat := 118140960795 + 3072751 * 2 ^ 59
def prefixEnd_3072751 : Nat := 4983230072969 + 3 ^ 40 * 3072751 * 2
def baseEnd_3072751 : Nat := 1051865463055741720854121

theorem tailTrace_3072751 : CollatzResearch.WordTrace tailWord_3072751 prefixEnd_3072751 1051865463055741720854121 := by
  unfold tailWord_3072751
  simp only [CollatzResearch.WordTrace]
  refine ⟨112072436090955385935714107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74714957393970257290476071 112072436090955385935714107)
  ·
    refine ⟨168108654136433078903571161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112072436090955385935714107 168108654136433078903571161)
    ·
      refine ⟨126081490602324809177678371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168108654136433078903571161 126081490602324809177678371)
      ·
        refine ⟨189122235903487213766517557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126081490602324809177678371 189122235903487213766517557)
        ·
          refine ⟨17730209615951926290611021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189122235903487213766517557 17730209615951926290611021)
          ·
            refine ⟨6648828605981972358979133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17730209615951926290611021 6648828605981972358979133)
            ·
              refine ⟨2493310727243239634617175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6648828605981972358979133 2493310727243239634617175)
              ·
                refine ⟨3739966090864859451925763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2493310727243239634617175 3739966090864859451925763)
                ·
                  refine ⟨5609949136297289177888645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739966090864859451925763 5609949136297289177888645)
                  ·
                    refine ⟨1051865463055741720854121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5609949136297289177888645 1051865463055741720854121)
                    ·
                      rfl

theorem cell22_3072751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 1, 4].length) (baseStart_3072751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072751 prefixEnd_3072751 := by exact prefixLift 3072751
  have htrace : WordTrace (prefixWord ++ tailWord_3072751) baseStart_3072751 baseEnd_3072751 := by
    simpa [prefixWord, tailWord_3072751, baseEnd_3072751] using wordTrace_append hprefix tailTrace_3072751
  have hstable : (prefixWord ++ tailWord_3072751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072751).length < 2 ^ (prefixWord ++ tailWord_3072751).sum := by decide
  have hdescent : baseEnd_3072751 < baseStart_3072751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072777 : List Nat := [1, 2, 1, 1, 3, 2, 5, 7]
def baseStart_3072777 : Nat := 118140960795 + 3072777 * 2 ^ 59
def prefixEnd_3072777 : Nat := 4983230072969 + 3 ^ 40 * 3072777 * 2
def baseEnd_3072777 : Nat := 116874929265231813300449

theorem tailTrace_3072777 : CollatzResearch.WordTrace tailWord_3072777 prefixEnd_3072777 116874929265231813300449 := by
  unfold tailWord_3072777
  simp only [CollatzResearch.WordTrace]
  refine ⟨112073384388861192376160585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74715589592574128250773723 112073384388861192376160585)
  ·
    refine ⟨84055038291645894282120439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112073384388861192376160585 84055038291645894282120439)
    ·
      refine ⟨126082557437468841423180659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84055038291645894282120439 126082557437468841423180659)
      ·
        refine ⟨189123836156203262134770989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126082557437468841423180659 189123836156203262134770989)
        ·
          refine ⟨70921438558576223300539121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189123836156203262134770989 70921438558576223300539121)
          ·
            refine ⟨53191078918932167475404341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70921438558576223300539121 53191078918932167475404341)
            ·
              refine ⟨4986663648649890700819157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53191078918932167475404341 4986663648649890700819157)
              ·
                refine ⟨116874929265231813300449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4986663648649890700819157 116874929265231813300449)
                ·
                  rfl

theorem cell22_3072777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 7].length) (baseStart_3072777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072777 prefixEnd_3072777 := by exact prefixLift 3072777
  have htrace : WordTrace (prefixWord ++ tailWord_3072777) baseStart_3072777 baseEnd_3072777 := by
    simpa [prefixWord, tailWord_3072777, baseEnd_3072777] using wordTrace_append hprefix tailTrace_3072777
  have hstable : (prefixWord ++ tailWord_3072777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072777).length < 2 ^ (prefixWord ++ tailWord_3072777).sum := by decide
  have hdescent : baseEnd_3072777 < baseStart_3072777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072794 : List Nat := [3, 1, 1, 3, 2, 1, 5, 6]
def baseStart_3072794 : Nat := 118140960795 + 3072794 * 2 ^ 59
def prefixEnd_3072794 : Nat := 4983230072969 + 3 ^ 40 * 3072794 * 2
def baseEnd_3072794 : Nat := 116875575870500438003221

theorem tailTrace_3072794 : CollatzResearch.WordTrace tailWord_3072794 prefixEnd_3072794 116875575870500438003221 := by
  unfold tailWord_3072794
  simp only [CollatzResearch.WordTrace]
  refine ⟨28018501107449901069882359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74716002953199736186352957 28018501107449901069882359)
  ·
    refine ⟨42027751661174851604823539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28018501107449901069882359 42027751661174851604823539)
    ·
      refine ⟨63041627491762277407235309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42027751661174851604823539 63041627491762277407235309)
      ·
        refine ⟨23640610309410854027713241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63041627491762277407235309 23640610309410854027713241)
        ·
          refine ⟨17730457732058140520784931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23640610309410854027713241 17730457732058140520784931)
          ·
            refine ⟨26595686598087210781177397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17730457732058140520784931 26595686598087210781177397)
            ·
              refine ⟨2493345618570676010735381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26595686598087210781177397 2493345618570676010735381)
              ·
                refine ⟨116875575870500438003221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2493345618570676010735381 116875575870500438003221)
                ·
                  rfl

theorem cell22_3072794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 6].length) (baseStart_3072794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072794 prefixEnd_3072794 := by exact prefixLift 3072794
  have htrace : WordTrace (prefixWord ++ tailWord_3072794) baseStart_3072794 baseEnd_3072794 := by
    simpa [prefixWord, tailWord_3072794, baseEnd_3072794] using wordTrace_append hprefix tailTrace_3072794
  have hstable : (prefixWord ++ tailWord_3072794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072794).length < 2 ^ (prefixWord ++ tailWord_3072794).sum := by decide
  have hdescent : baseEnd_3072794 < baseStart_3072794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072796 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 2, 4]
def baseStart_3072796 : Nat := 118140960795 + 3072796 * 2 ^ 59
def prefixEnd_3072796 : Nat := 4983230072969 + 3 ^ 40 * 3072796 * 2
def baseEnd_3072796 : Nat := 1051880867475376603478983

theorem tailTrace_3072796 : CollatzResearch.WordTrace tailWord_3072796 prefixEnd_3072796 1051880867475376603478983 := by
  unfold tailWord_3072796
  simp only [CollatzResearch.WordTrace]
  refine ⟨56037038687896179310551121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74716051583861572414068161 56037038687896179310551121)
  ·
    refine ⟨42027779015922134482913341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56037038687896179310551121 42027779015922134482913341)
    ·
      refine ⟨15760417130970800431092503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42027779015922134482913341 15760417130970800431092503)
      ·
        refine ⟨23640625696456200646638755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15760417130970800431092503 23640625696456200646638755)
        ·
          refine ⟨35460938544684300969958133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23640625696456200646638755 35460938544684300969958133)
          ·
            refine ⟨3324462988564153215933575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35460938544684300969958133 3324462988564153215933575)
            ·
              refine ⟨4986694482846229823900363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3324462988564153215933575 4986694482846229823900363)
              ·
                refine ⟨7480041724269344735850545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4986694482846229823900363 7480041724269344735850545)
                ·
                  refine ⟨5610031293202008551887909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7480041724269344735850545 5610031293202008551887909)
                  ·
                    refine ⟨1051880867475376603478983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5610031293202008551887909 1051880867475376603478983)
                    ·
                      rfl

theorem cell22_3072796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_3072796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072796 prefixEnd_3072796 := by exact prefixLift 3072796
  have htrace : WordTrace (prefixWord ++ tailWord_3072796) baseStart_3072796 baseEnd_3072796 := by
    simpa [prefixWord, tailWord_3072796, baseEnd_3072796] using wordTrace_append hprefix tailTrace_3072796
  have hstable : (prefixWord ++ tailWord_3072796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072796).length < 2 ^ (prefixWord ++ tailWord_3072796).sum := by decide
  have hdescent : baseEnd_3072796 < baseStart_3072796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072837 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_3072837 : Nat := 118140960795 + 3072837 * 2 ^ 59
def prefixEnd_3072837 : Nat := 4983230072969 + 3 ^ 40 * 3072837 * 2
def baseEnd_3072837 : Nat := 1051894902613266163203857

theorem tailTrace_3072837 : CollatzResearch.WordTrace tailWord_3072837 prefixEnd_3072837 1051894902613266163203857 := by
  unfold tailWord_3072837
  simp only [CollatzResearch.WordTrace]
  refine ⟨112075572768643822623344765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74717048512429215082229843 112075572768643822623344765)
  ·
    refine ⟨42028339788241433483754287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112075572768643822623344765 42028339788241433483754287)
    ·
      refine ⟨63042509682362150225631431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42028339788241433483754287 63042509682362150225631431)
      ·
        refine ⟨94563764523543225338447147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63042509682362150225631431 94563764523543225338447147)
        ·
          refine ⟨141845646785314838007670721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94563764523543225338447147 141845646785314838007670721)
          ·
            refine ⟨106384235088986128505753041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141845646785314838007670721 106384235088986128505753041)
            ·
              refine ⟨79788176316739596379314781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106384235088986128505753041 79788176316739596379314781)
              ·
                refine ⟨29920566118777348642243043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79788176316739596379314781 29920566118777348642243043)
                ·
                  refine ⟨44880849178166022963364565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29920566118777348642243043 44880849178166022963364565)
                  ·
                    refine ⟨1051894902613266163203857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44880849178166022963364565 1051894902613266163203857)
                    ·
                      rfl

theorem cell22_3072837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_3072837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072837 prefixEnd_3072837 := by exact prefixLift 3072837
  have htrace : WordTrace (prefixWord ++ tailWord_3072837) baseStart_3072837 baseEnd_3072837 := by
    simpa [prefixWord, tailWord_3072837, baseEnd_3072837] using wordTrace_append hprefix tailTrace_3072837
  have hstable : (prefixWord ++ tailWord_3072837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072837).length < 2 ^ (prefixWord ++ tailWord_3072837).sum := by decide
  have hdescent : baseEnd_3072837 < baseStart_3072837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072845 : List Nat := [1, 6, 1, 2, 3, 1, 2, 6]
def baseStart_3072845 : Nat := 118140960795 + 3072845 * 2 ^ 59
def prefixEnd_3072845 : Nat := 4983230072969 + 3 ^ 40 * 3072845 * 2
def baseEnd_3072845 : Nat := 116877515686306312111537

theorem tailTrace_3072845 : CollatzResearch.WordTrace tailWord_3072845 prefixEnd_3072845 116877515686306312111537 := by
  unfold tailWord_3072845
  simp only [CollatzResearch.WordTrace]
  refine ⟨112075864552614839989635989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74717243035076559993090659 112075864552614839989635989)
  ·
    refine ⟨5253556150903820624514187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 112075864552614839989635989 5253556150903820624514187)
    ·
      refine ⟨7880334226355730936771281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5253556150903820624514187 7880334226355730936771281)
      ·
        refine ⟨5910250669766798202578461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7880334226355730936771281 5910250669766798202578461)
        ·
          refine ⟨2216344001162549325966923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5910250669766798202578461 2216344001162549325966923)
          ·
            refine ⟨3324516001743823988950385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2216344001162549325966923 3324516001743823988950385)
            ·
              refine ⟨2493387001307867991712789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3324516001743823988950385 2493387001307867991712789)
              ·
                refine ⟨116877515686306312111537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2493387001307867991712789 116877515686306312111537)
                ·
                  rfl

theorem cell22_3072845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 6].length) (baseStart_3072845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072845 prefixEnd_3072845 := by exact prefixLift 3072845
  have htrace : WordTrace (prefixWord ++ tailWord_3072845) baseStart_3072845 baseEnd_3072845 := by
    simpa [prefixWord, tailWord_3072845, baseEnd_3072845] using wordTrace_append hprefix tailTrace_3072845
  have hstable : (prefixWord ++ tailWord_3072845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072845).length < 2 ^ (prefixWord ++ tailWord_3072845).sum := by decide
  have hdescent : baseEnd_3072845 < baseStart_3072845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072860 : List Nat := [2, 2, 4, 2, 1, 1, 3, 3, 1, 3]
def baseStart_3072860 : Nat := 118140960795 + 3072860 * 2 ^ 59
def prefixEnd_3072860 : Nat := 4983230072969 + 3 ^ 40 * 3072860 * 2
def baseEnd_3072860 : Nat := 1051902775983301769878787

theorem tailTrace_3072860 : CollatzResearch.WordTrace tailWord_3072860 prefixEnd_3072860 1051902775983301769878787 := by
  unfold tailWord_3072860
  simp only [CollatzResearch.WordTrace]
  refine ⟨56038205823780248775716017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74717607765040331700954689 56038205823780248775716017)
  ·
    refine ⟨42028654367835186581787013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56038205823780248775716017 42028654367835186581787013)
    ·
      refine ⟨7880372693969097484085065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42028654367835186581787013 7880372693969097484085065)
      ·
        refine ⟨5910279520476823113063799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7880372693969097484085065 5910279520476823113063799)
        ·
          refine ⟨8865419280715234669595699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5910279520476823113063799 8865419280715234669595699)
          ·
            refine ⟨13298128921072852004393549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8865419280715234669595699 13298128921072852004393549)
            ·
              refine ⟨4986798345402319501647581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13298128921072852004393549 4986798345402319501647581)
              ·
                refine ⟨1870049379525869813117843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4986798345402319501647581 1870049379525869813117843)
                ·
                  refine ⟨2805074069288804719676765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1870049379525869813117843 2805074069288804719676765)
                  ·
                    refine ⟨1051902775983301769878787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2805074069288804719676765 1051902775983301769878787)
                    ·
                      rfl

theorem cell22_3072860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_3072860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072860 prefixEnd_3072860 := by exact prefixLift 3072860
  have htrace : WordTrace (prefixWord ++ tailWord_3072860) baseStart_3072860 baseEnd_3072860 := by
    simpa [prefixWord, tailWord_3072860, baseEnd_3072860] using wordTrace_append hprefix tailTrace_3072860
  have hstable : (prefixWord ++ tailWord_3072860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072860).length < 2 ^ (prefixWord ++ tailWord_3072860).sum := by decide
  have hdescent : baseEnd_3072860 < baseStart_3072860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072899 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 1, 5]
def baseStart_3072899 : Nat := 118140960795 + 3072899 * 2 ^ 59
def prefixEnd_3072899 : Nat := 4983230072969 + 3 ^ 40 * 3072899 * 2
def baseEnd_3072899 : Nat := 1051916126480318668153667

theorem tailTrace_3072899 : CollatzResearch.WordTrace tailWord_3072899 prefixEnd_3072899 1051916126480318668153667 := by
  unfold tailWord_3072899
  simp only [CollatzResearch.WordTrace]
  refine ⟨112077834094419207212101751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74718556062946138141401167 112077834094419207212101751)
  ·
    refine ⟨168116751141628810818152627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112077834094419207212101751 168116751141628810818152627)
    ·
      refine ⟨252175126712443216227228941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168116751141628810818152627 252175126712443216227228941)
      ·
        refine ⟨94565672517166206085210853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252175126712443216227228941 94565672517166206085210853)
        ·
          refine ⟨17731063596968663640977035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94565672517166206085210853 17731063596968663640977035)
          ·
            refine ⟨26596595395452995461465553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17731063596968663640977035 26596595395452995461465553)
            ·
              refine ⟨19947446546589746596099165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26596595395452995461465553 19947446546589746596099165)
              ·
                refine ⟨7480292454971154973537187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19947446546589746596099165 7480292454971154973537187)
                ·
                  refine ⟨11220438682456732460305781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7480292454971154973537187 11220438682456732460305781)
                  ·
                    refine ⟨1051916126480318668153667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11220438682456732460305781 1051916126480318668153667)
                    ·
                      rfl

theorem cell22_3072899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 5].length) (baseStart_3072899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072899 prefixEnd_3072899 := by exact prefixLift 3072899
  have htrace : WordTrace (prefixWord ++ tailWord_3072899) baseStart_3072899 baseEnd_3072899 := by
    simpa [prefixWord, tailWord_3072899, baseEnd_3072899] using wordTrace_append hprefix tailTrace_3072899
  have hstable : (prefixWord ++ tailWord_3072899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072899).length < 2 ^ (prefixWord ++ tailWord_3072899).sum := by decide
  have hdescent : baseEnd_3072899 < baseStart_3072899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072903 : List Nat := [1, 1, 4, 2, 3, 3, 1, 2, 1, 4]
def baseStart_3072903 : Nat := 118140960795 + 3072903 * 2 ^ 59
def prefixEnd_3072903 : Nat := 4983230072969 + 3 ^ 40 * 3072903 * 2
def baseEnd_3072903 : Nat := 1051917495762063991053655

theorem tailTrace_3072903 : CollatzResearch.WordTrace tailWord_3072903 prefixEnd_3072903 1051917495762063991053655 := by
  unfold tailWord_3072903
  simp only [CollatzResearch.WordTrace]
  refine ⟨112077979986404715895247363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74718653324269810596831575 112077979986404715895247363)
  ·
    refine ⟨168116969979607073842871045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112077979986404715895247363 168116969979607073842871045)
    ·
      refine ⟨31521931871176326345538321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168116969979607073842871045 31521931871176326345538321)
      ·
        refine ⟨23641448903382244759153741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31521931871176326345538321 23641448903382244759153741)
        ·
          refine ⟨8865543338768341784682653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23641448903382244759153741 8865543338768341784682653)
          ·
            refine ⟨3324578752038128169255995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8865543338768341784682653 3324578752038128169255995)
            ·
              refine ⟨4986868128057192253883993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3324578752038128169255995 4986868128057192253883993)
              ·
                refine ⟨3740151096042894190412995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4986868128057192253883993 3740151096042894190412995)
                ·
                  refine ⟨5610226644064341285619493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3740151096042894190412995 5610226644064341285619493)
                  ·
                    refine ⟨1051917495762063991053655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5610226644064341285619493 1051917495762063991053655)
                    ·
                      rfl

theorem cell22_3072903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_3072903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072903 prefixEnd_3072903 := by exact prefixLift 3072903
  have htrace : WordTrace (prefixWord ++ tailWord_3072903) baseStart_3072903 baseEnd_3072903 := by
    simpa [prefixWord, tailWord_3072903, baseEnd_3072903] using wordTrace_append hprefix tailTrace_3072903
  have hstable : (prefixWord ++ tailWord_3072903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072903).length < 2 ^ (prefixWord ++ tailWord_3072903).sum := by decide
  have hdescent : baseEnd_3072903 < baseStart_3072903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072916 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3072916 : Nat := 118140960795 + 3072916 * 2 ^ 59
def prefixEnd_3072916 : Nat := 4983230072969 + 3 ^ 40 * 3072916 * 2
def baseEnd_3072916 : Nat := 1051921945927736290478615

theorem tailTrace_3072916 : CollatzResearch.WordTrace tailWord_3072916 prefixEnd_3072916 1051921945927736290478615 := by
  unfold tailWord_3072916
  simp only [CollatzResearch.WordTrace]
  refine ⟨56039227067678809557735301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74718969423571746076980401 56039227067678809557735301)
  ·
    refine ⟨10507355075189776792075369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56039227067678809557735301 10507355075189776792075369)
    ·
      refine ⟨7880516306392332594056527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10507355075189776792075369 7880516306392332594056527)
      ·
        refine ⟨11820774459588498891084791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7880516306392332594056527 11820774459588498891084791)
        ·
          refine ⟨17731161689382748336627187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11820774459588498891084791 17731161689382748336627187)
          ·
            refine ⟨26596742534074122504940781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17731161689382748336627187 26596742534074122504940781)
            ·
              refine ⟨9973778450277795939352793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26596742534074122504940781 9973778450277795939352793)
              ·
                refine ⟨7480333837708346954514595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9973778450277795939352793 7480333837708346954514595)
                ·
                  refine ⟨11220500756562520431771893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7480333837708346954514595 11220500756562520431771893)
                  ·
                    refine ⟨1051921945927736290478615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11220500756562520431771893 1051921945927736290478615)
                    ·
                      rfl

theorem cell22_3072916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3072916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072916 prefixEnd_3072916 := by exact prefixLift 3072916
  have htrace : WordTrace (prefixWord ++ tailWord_3072916) baseStart_3072916 baseEnd_3072916 := by
    simpa [prefixWord, tailWord_3072916, baseEnd_3072916] using wordTrace_append hprefix tailTrace_3072916
  have hstable : (prefixWord ++ tailWord_3072916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072916).length < 2 ^ (prefixWord ++ tailWord_3072916).sum := by decide
  have hdescent : baseEnd_3072916 < baseStart_3072916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072929 : List Nat := [1, 2, 3, 4, 1, 11]
def baseStart_3072929 : Nat := 118140960795 + 3072929 * 2 ^ 59
def prefixEnd_3072929 : Nat := 4983230072969 + 3 ^ 40 * 3072929 * 2
def baseEnd_3072929 : Nat := 12986745630782822097575

theorem tailTrace_3072929 : CollatzResearch.WordTrace tailWord_3072929 prefixEnd_3072929 12986745630782822097575 := by
  unfold tailWord_3072929
  simp only [CollatzResearch.WordTrace]
  refine ⟨112078928284310522335693841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74719285522873681557129227 112078928284310522335693841)
  ·
    refine ⟨84059196213232891751770381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112078928284310522335693841 84059196213232891751770381)
    ·
      refine ⟨31522198579962334406913893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84059196213232891751770381 31522198579962334406913893)
      ·
        refine ⟨5910412233742937701296355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31522198579962334406913893 5910412233742937701296355)
        ·
          refine ⟨8865618350614406551944533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5910412233742937701296355 8865618350614406551944533)
          ·
            refine ⟨12986745630782822097575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8865618350614406551944533 12986745630782822097575)
            ·
              rfl

theorem cell22_3072929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 11].length) (baseStart_3072929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072929 prefixEnd_3072929 := by exact prefixLift 3072929
  have htrace : WordTrace (prefixWord ++ tailWord_3072929) baseStart_3072929 baseEnd_3072929 := by
    simpa [prefixWord, tailWord_3072929, baseEnd_3072929] using wordTrace_append hprefix tailTrace_3072929
  have hstable : (prefixWord ++ tailWord_3072929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072929).length < 2 ^ (prefixWord ++ tailWord_3072929).sum := by decide
  have hdescent : baseEnd_3072929 < baseStart_3072929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072991 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 7]
def baseStart_3072991 : Nat := 118140960795 + 3072991 * 2 ^ 59
def prefixEnd_3072991 : Nat := 4983230072969 + 3 ^ 40 * 3072991 * 2
def baseEnd_3072991 : Nat := 350649206653487031617795

theorem tailTrace_3072991 : CollatzResearch.WordTrace tailWord_3072991 prefixEnd_3072991 350649206653487031617795 := by
  unfold tailWord_3072991
  simp only [CollatzResearch.WordTrace]
  refine ⟨112081189610085906924450827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74720793073390604616300551 112081189610085906924450827)
  ·
    refine ⟨168121784415128860386676241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112081189610085906924450827 168121784415128860386676241)
    ·
      refine ⟨126091338311346645290007181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168121784415128860386676241 126091338311346645290007181)
      ·
        refine ⟨47284251866754991983752693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126091338311346645290007181 47284251866754991983752693)
        ·
          refine ⟨4432898612508280498476815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47284251866754991983752693 4432898612508280498476815)
          ·
            refine ⟨6649347918762420747715223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4432898612508280498476815 6649347918762420747715223)
            ·
              refine ⟨9974021878143631121572835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6649347918762420747715223 9974021878143631121572835)
              ·
                refine ⟨14961032817215446682359253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9974021878143631121572835 14961032817215446682359253)
                ·
                  refine ⟨350649206653487031617795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14961032817215446682359253 350649206653487031617795)
                  ·
                    rfl

theorem cell22_3072991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 7].length) (baseStart_3072991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3072991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3072991 prefixEnd_3072991 := by exact prefixLift 3072991
  have htrace : WordTrace (prefixWord ++ tailWord_3072991) baseStart_3072991 baseEnd_3072991 := by
    simpa [prefixWord, tailWord_3072991, baseEnd_3072991] using wordTrace_append hprefix tailTrace_3072991
  have hstable : (prefixWord ++ tailWord_3072991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072991).length < 2 ^ (prefixWord ++ tailWord_3072991).sum := by decide
  have hdescent : baseEnd_3072991 < baseStart_3072991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073038 : List Nat := [4, 1, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_3073038 : Nat := 118140960795 + 3073038 * 2 ^ 59
def prefixEnd_3073038 : Nat := 4983230072969 + 3 ^ 40 * 3073038 * 2
def baseEnd_3073038 : Nat := 1051963709020968638928241

theorem tailTrace_3073038 : CollatzResearch.WordTrace tailWord_3073038 prefixEnd_3073038 1051963709020968638928241 := by
  unfold tailWord_3073038
  simp only [CollatzResearch.WordTrace]
  refine ⟨14010362980114454243926471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74721935893943755967607845 14010362980114454243926471)
  ·
    refine ⟨21015544470171681365889707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14010362980114454243926471 21015544470171681365889707)
    ·
      refine ⟨31523316705257522048834561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21015544470171681365889707 31523316705257522048834561)
      ·
        refine ⟨23642487528943141536625921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31523316705257522048834561 23642487528943141536625921)
        ·
          refine ⟨17731865646707356152469441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23642487528943141536625921 17731865646707356152469441)
          ·
            refine ⟨13298899235030517114352081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17731865646707356152469441 13298899235030517114352081)
            ·
              refine ⟨9974174426272887835764061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13298899235030517114352081 9974174426272887835764061)
              ·
                refine ⟨3740315409852332938411523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9974174426272887835764061 3740315409852332938411523)
                ·
                  refine ⟨5610473114778499407617285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3740315409852332938411523 5610473114778499407617285)
                  ·
                    refine ⟨1051963709020968638928241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5610473114778499407617285 1051963709020968638928241)
                    ·
                      rfl

theorem cell22_3073038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_3073038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073038 prefixEnd_3073038 := by exact prefixLift 3073038
  have htrace : WordTrace (prefixWord ++ tailWord_3073038) baseStart_3073038 baseEnd_3073038 := by
    simpa [prefixWord, tailWord_3073038, baseEnd_3073038] using wordTrace_append hprefix tailTrace_3073038
  have hstable : (prefixWord ++ tailWord_3073038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073038).length < 2 ^ (prefixWord ++ tailWord_3073038).sum := by decide
  have hdescent : baseEnd_3073038 < baseStart_3073038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073068 : List Nat := [2, 2, 1, 1, 1, 2, 5, 3, 2, 3]
def baseStart_3073068 : Nat := 118140960795 + 3073068 * 2 ^ 59
def prefixEnd_3073068 : Nat := 4983230072969 + 3 ^ 40 * 3073068 * 2
def baseEnd_3073068 : Nat := 1051973978634058560678149

theorem tailTrace_3073068 : CollatzResearch.WordTrace tailWord_3073068 prefixEnd_3073068 1051973978634058560678149 := by
  unfold tailWord_3073068
  simp only [CollatzResearch.WordTrace]
  refine ⟨56041999015403474537501929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74722665353871299383335905 56041999015403474537501929)
  ·
    refine ⟨42031499261552605903126447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56041999015403474537501929 42031499261552605903126447)
    ·
      refine ⟨63047248892328908854689671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42031499261552605903126447 63047248892328908854689671)
      ·
        refine ⟨94570873338493363282034507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63047248892328908854689671 94570873338493363282034507)
        ·
          refine ⟨141856310007740044923051761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94570873338493363282034507 141856310007740044923051761)
          ·
            refine ⟨106392232505805033692288821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141856310007740044923051761 106392232505805033692288821)
            ·
              refine ⟨9974271797419221908652077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106392232505805033692288821 9974271797419221908652077)
              ·
                refine ⟨3740351924032208215744529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9974271797419221908652077 3740351924032208215744529)
                ·
                  refine ⟨2805263943024156161808397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3740351924032208215744529 2805263943024156161808397)
                  ·
                    refine ⟨1051973978634058560678149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2805263943024156161808397 1051973978634058560678149)
                    ·
                      rfl

theorem cell22_3073068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_3073068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073068 prefixEnd_3073068 := by exact prefixLift 3073068
  have htrace : WordTrace (prefixWord ++ tailWord_3073068) baseStart_3073068 baseEnd_3073068 := by
    simpa [prefixWord, tailWord_3073068, baseEnd_3073068] using wordTrace_append hprefix tailTrace_3073068
  have hstable : (prefixWord ++ tailWord_3073068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073068).length < 2 ^ (prefixWord ++ tailWord_3073068).sum := by decide
  have hdescent : baseEnd_3073068 < baseStart_3073068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073081 : List Nat := [1, 2, 1, 5, 2, 1, 2, 8]
def baseStart_3073081 : Nat := 118140960795 + 3073081 * 2 ^ 59
def prefixEnd_3073081 : Nat := 4983230072969 + 3 ^ 40 * 3073081 * 2
def baseEnd_3073081 : Nat := 116886492088858984455901

theorem tailTrace_3073081 : CollatzResearch.WordTrace tailWord_3073081 prefixEnd_3073081 116886492088858984455901 := by
  unfold tailWord_3073081
  simp only [CollatzResearch.WordTrace]
  refine ⟨112084472179759852295227097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74722981453173234863484731 112084472179759852295227097)
  ·
    refine ⟨84063354134819889221420323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112084472179759852295227097 84063354134819889221420323)
    ·
      refine ⟨126095031202229833832130485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84063354134819889221420323 126095031202229833832130485)
      ·
        refine ⟨11821409175209046921762233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126095031202229833832130485 11821409175209046921762233)
        ·
          refine ⟨8866056881406785191321675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11821409175209046921762233 8866056881406785191321675)
          ·
            refine ⟨13299085322110177786982513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8866056881406785191321675 13299085322110177786982513)
            ·
              refine ⟨9974313991582633340236885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13299085322110177786982513 9974313991582633340236885)
              ·
                refine ⟨116886492088858984455901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9974313991582633340236885 116886492088858984455901)
                ·
                  rfl

theorem cell22_3073081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 8].length) (baseStart_3073081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073081 prefixEnd_3073081 := by exact prefixLift 3073081
  have htrace : WordTrace (prefixWord ++ tailWord_3073081) baseStart_3073081 baseEnd_3073081 := by
    simpa [prefixWord, tailWord_3073081, baseEnd_3073081] using wordTrace_append hprefix tailTrace_3073081
  have hstable : (prefixWord ++ tailWord_3073081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073081).length < 2 ^ (prefixWord ++ tailWord_3073081).sum := by decide
  have hdescent : baseEnd_3073081 < baseStart_3073081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073130 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 3, 3]
def baseStart_3073130 : Nat := 118140960795 + 3073130 * 2 ^ 59
def prefixEnd_3073130 : Nat := 4983230072969 + 3 ^ 40 * 3073130 * 2
def baseEnd_3073130 : Nat := 1051995202501111065627959

theorem tailTrace_3073130 : CollatzResearch.WordTrace tailWord_3073130 prefixEnd_3073130 1051995202501111065627959 := by
  unfold tailWord_3073130
  simp only [CollatzResearch.WordTrace]
  refine ⟨28021564839145583415940211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74724172904388222442507229 28021564839145583415940211)
  ·
    refine ⟨42032347258718375123910317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28021564839145583415940211 42032347258718375123910317)
    ·
      refine ⟨15762130222019390671466369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42032347258718375123910317 15762130222019390671466369)
      ·
        refine ⟨11821597666514543003599777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15762130222019390671466369 11821597666514543003599777)
        ·
          refine ⟨8866198249885907252699833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11821597666514543003599777 8866198249885907252699833)
          ·
            refine ⟨6649648687414430439524875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8866198249885907252699833 6649648687414430439524875)
            ·
              refine ⟨9974473031121645659287313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6649648687414430439524875 9974473031121645659287313)
              ·
                refine ⟨7480854773341234244465485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9974473031121645659287313 7480854773341234244465485)
                ·
                  refine ⟨2805320540002962841674557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7480854773341234244465485 2805320540002962841674557)
                  ·
                    refine ⟨1051995202501111065627959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2805320540002962841674557 1051995202501111065627959)
                    ·
                      rfl

theorem cell22_3073130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_3073130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073130 prefixEnd_3073130 := by exact prefixLift 3073130
  have htrace : WordTrace (prefixWord ++ tailWord_3073130) baseStart_3073130 baseEnd_3073130 := by
    simpa [prefixWord, tailWord_3073130, baseEnd_3073130] using wordTrace_append hprefix tailTrace_3073130
  have hstable : (prefixWord ++ tailWord_3073130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073130).length < 2 ^ (prefixWord ++ tailWord_3073130).sum := by decide
  have hdescent : baseEnd_3073130 < baseStart_3073130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073171 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 6]
def baseStart_3073171 : Nat := 118140960795 + 3073171 * 2 ^ 59
def prefixEnd_3073171 : Nat := 4983230072969 + 3 ^ 40 * 3073171 * 2
def baseEnd_3073171 : Nat := 350669745879666875117611

theorem tailTrace_3073171 : CollatzResearch.WordTrace tailWord_3073171 prefixEnd_3073171 350669745879666875117611 := by
  unfold tailWord_3073171
  simp only [CollatzResearch.WordTrace]
  refine ⟨112087754749433797666003367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74725169832955865110668911 112087754749433797666003367)
  ·
    refine ⟨168131632124150696499005051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112087754749433797666003367 168131632124150696499005051)
    ·
      refine ⟨252197448186226044748507577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168131632124150696499005051 252197448186226044748507577)
      ·
        refine ⟨189148086139669533561380683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252197448186226044748507577 189148086139669533561380683)
        ·
          refine ⟨283722129209504300342071025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189148086139669533561380683 283722129209504300342071025)
          ·
            refine ⟨212791596907128225256553269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283722129209504300342071025 212791596907128225256553269)
            ·
              refine ⟨19949212210043271117801869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212791596907128225256553269 19949212210043271117801869)
              ·
                refine ⟨7480954578766226669175701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19949212210043271117801869 7480954578766226669175701)
                ·
                  refine ⟨350669745879666875117611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7480954578766226669175701 350669745879666875117611)
                  ·
                    rfl

theorem cell22_3073171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 6].length) (baseStart_3073171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073171 prefixEnd_3073171 := by exact prefixLift 3073171
  have htrace : WordTrace (prefixWord ++ tailWord_3073171) baseStart_3073171 baseEnd_3073171 := by
    simpa [prefixWord, tailWord_3073171, baseEnd_3073171] using wordTrace_append hprefix tailTrace_3073171
  have hstable : (prefixWord ++ tailWord_3073171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073171).length < 2 ^ (prefixWord ++ tailWord_3073171).sum := by decide
  have hdescent : baseEnd_3073171 < baseStart_3073171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073188 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 6]
def baseStart_3073188 : Nat := 118140960795 + 3073188 * 2 ^ 59
def prefixEnd_3073188 : Nat := 4983230072969 + 3 ^ 40 * 3073188 * 2
def baseEnd_3073188 : Nat := 350671685695472749225927

theorem tailTrace_3073188 : CollatzResearch.WordTrace tailWord_3073188 prefixEnd_3073188 350671685695472749225927 := by
  unfold tailWord_3073188
  simp only [CollatzResearch.WordTrace]
  refine ⟨56044187395186104784686109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74725583193581473046248145 56044187395186104784686109)
  ·
    refine ⟨21016570273194789294257291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56044187395186104784686109 21016570273194789294257291)
    ·
      refine ⟨31524855409792183941385937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21016570273194789294257291 31524855409792183941385937)
      ·
        refine ⟨23643641557344137956039453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31524855409792183941385937 23643641557344137956039453)
        ·
          refine ⟨8866365584004051733514795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23643641557344137956039453 8866365584004051733514795)
          ·
            refine ⟨13299548376006077600272193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8866365584004051733514795 13299548376006077600272193)
            ·
              refine ⟨9974661282004558200204145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13299548376006077600272193 9974661282004558200204145)
              ·
                refine ⟨7480995961503418650153109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9974661282004558200204145 7480995961503418650153109)
                ·
                  refine ⟨350671685695472749225927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7480995961503418650153109 350671685695472749225927)
                  ·
                    rfl

theorem cell22_3073188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_3073188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073188 prefixEnd_3073188 := by exact prefixLift 3073188
  have htrace : WordTrace (prefixWord ++ tailWord_3073188) baseStart_3073188 baseEnd_3073188 := by
    simpa [prefixWord, tailWord_3073188, baseEnd_3073188] using wordTrace_append hprefix tailTrace_3073188
  have hstable : (prefixWord ++ tailWord_3073188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073188).length < 2 ^ (prefixWord ++ tailWord_3073188).sum := by decide
  have hdescent : baseEnd_3073188 < baseStart_3073188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073203 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 4, 3]
def baseStart_3073203 : Nat := 118140960795 + 3073203 * 2 ^ 59
def prefixEnd_3073203 : Nat := 4983230072969 + 3 ^ 40 * 3073203 * 2
def baseEnd_3073203 : Nat := 1052020191892963208552735

theorem tailTrace_3073203 : CollatzResearch.WordTrace tailWord_3073203 prefixEnd_3073203 1052020191892963208552735 := by
  unfold tailWord_3073203
  simp only [CollatzResearch.WordTrace]
  refine ⟨112088921885317867131168263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74725947923545244754112175 112088921885317867131168263)
  ·
    refine ⟨168133382827976800696752395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112088921885317867131168263 168133382827976800696752395)
    ·
      refine ⟨252200074241965201045128593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168133382827976800696752395 252200074241965201045128593)
      ·
        refine ⟨189150055681473900783846445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252200074241965201045128593 189150055681473900783846445)
        ·
          refine ⟨70931270880552712793942417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189150055681473900783846445 70931270880552712793942417)
          ·
            refine ⟨53198453160414534595456813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70931270880552712793942417 53198453160414534595456813)
            ·
              refine ⟨19949419935155450473296305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53198453160414534595456813 19949419935155450473296305)
              ·
                refine ⟨14962064951366587854972229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19949419935155450473296305 14962064951366587854972229)
                ·
                  refine ⟨2805387178381235222807293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14962064951366587854972229 2805387178381235222807293)
                  ·
                    refine ⟨1052020191892963208552735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2805387178381235222807293 1052020191892963208552735)
                    ·
                      rfl

theorem cell22_3073203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 3].length) (baseStart_3073203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073203 prefixEnd_3073203 := by exact prefixLift 3073203
  have htrace : WordTrace (prefixWord ++ tailWord_3073203) baseStart_3073203 baseEnd_3073203 := by
    simpa [prefixWord, tailWord_3073203, baseEnd_3073203] using wordTrace_append hprefix tailTrace_3073203
  have hstable : (prefixWord ++ tailWord_3073203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073203).length < 2 ^ (prefixWord ++ tailWord_3073203).sum := by decide
  have hdescent : baseEnd_3073203 < baseStart_3073203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073231 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 2, 7]
def baseStart_3073231 : Nat := 118140960795 + 3073231 * 2 ^ 59
def prefixEnd_3073231 : Nat := 4983230072969 + 3 ^ 40 * 3073231 * 2
def baseEnd_3073231 : Nat := 1052029776865180468852649

theorem tailTrace_3073231 : CollatzResearch.WordTrace tailWord_3073231 prefixEnd_3073231 1052029776865180468852649 := by
  unfold tailWord_3073231
  simp only [CollatzResearch.WordTrace]
  refine ⟨112089943129216427913187547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74726628752810951942125031 112089943129216427913187547)
  ·
    refine ⟨168134914693824641869781321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112089943129216427913187547 168134914693824641869781321)
    ·
      refine ⟨126101186020368481402335991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168134914693824641869781321 126101186020368481402335991)
      ·
        refine ⟨189151779030552722103503987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126101186020368481402335991 189151779030552722103503987)
        ·
          refine ⟨283727668545829083155255981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189151779030552722103503987 283727668545829083155255981)
          ·
            refine ⟨106397875704685906183220993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283727668545829083155255981 106397875704685906183220993)
            ·
              refine ⟨79798406778514429637415745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106397875704685906183220993 79798406778514429637415745)
              ·
                refine ⟨59848805083885822228061809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79798406778514429637415745 59848805083885822228061809)
                ·
                  refine ⟨44886603812914366671046357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59848805083885822228061809 44886603812914366671046357)
                  ·
                    refine ⟨1052029776865180468852649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44886603812914366671046357 1052029776865180468852649)
                    ·
                      rfl

theorem cell22_3073231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_3073231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073231 prefixEnd_3073231 := by exact prefixLift 3073231
  have htrace : WordTrace (prefixWord ++ tailWord_3073231) baseStart_3073231 baseEnd_3073231 := by
    simpa [prefixWord, tailWord_3073231, baseEnd_3073231] using wordTrace_append hprefix tailTrace_3073231
  have hstable : (prefixWord ++ tailWord_3073231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073231).length < 2 ^ (prefixWord ++ tailWord_3073231).sum := by decide
  have hdescent : baseEnd_3073231 < baseStart_3073231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073237 : List Nat := [1, 3, 2, 4, 1, 2, 1, 3, 2, 3]
def baseStart_3073237 : Nat := 118140960795 + 3073237 * 2 ^ 59
def prefixEnd_3073237 : Nat := 4983230072969 + 3 ^ 40 * 3073237 * 2
def baseEnd_3073237 : Nat := 1052031830787798453202631

theorem tailTrace_3073237 : CollatzResearch.WordTrace tailWord_3073237 prefixEnd_3073237 1052031830787798453202631 := by
  unfold tailWord_3073237
  simp only [CollatzResearch.WordTrace]
  refine ⟨112090161967194690937905965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74726774644796460625270643 112090161967194690937905965)
  ·
    refine ⟨42033810737698009101714737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112090161967194690937905965 42033810737698009101714737)
    ·
      refine ⟨31525358053273506826286053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42033810737698009101714737 31525358053273506826286053)
      ·
        refine ⟨5911004634988782529928635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31525358053273506826286053 5911004634988782529928635)
        ·
          refine ⟨8866506952483173794892953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5911004634988782529928635 8866506952483173794892953)
          ·
            refine ⟨6649880214362380346169715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8866506952483173794892953 6649880214362380346169715)
            ·
              refine ⟨9974820321543570519254573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6649880214362380346169715 9974820321543570519254573)
              ·
                refine ⟨3740557620578838944720465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9974820321543570519254573 3740557620578838944720465)
                ·
                  refine ⟨2805418215434129208540349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3740557620578838944720465 2805418215434129208540349)
                  ·
                    refine ⟨1052031830787798453202631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2805418215434129208540349 1052031830787798453202631)
                    ·
                      rfl

theorem cell22_3073237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_3073237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073237 prefixEnd_3073237 := by exact prefixLift 3073237
  have htrace : WordTrace (prefixWord ++ tailWord_3073237) baseStart_3073237 baseEnd_3073237 := by
    simpa [prefixWord, tailWord_3073237, baseEnd_3073237] using wordTrace_append hprefix tailTrace_3073237
  have hstable : (prefixWord ++ tailWord_3073237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073237).length < 2 ^ (prefixWord ++ tailWord_3073237).sum := by decide
  have hdescent : baseEnd_3073237 < baseStart_3073237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073340 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 6]
def baseStart_3073340 : Nat := 118140960795 + 3073340 * 2 ^ 59
def prefixEnd_3073340 : Nat := 4983230072969 + 3 ^ 40 * 3073340 * 2
def baseEnd_3073340 : Nat := 350689029930913505959105

theorem tailTrace_3073340 : CollatzResearch.WordTrace tailWord_3073340 prefixEnd_3073340 350689029930913505959105 := by
  unfold tailWord_3073340
  simp only [CollatzResearch.WordTrace]
  refine ⟨56046959342910769764452737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74729279123881026352603649 56046959342910769764452737)
  ·
    refine ⟨42035219507183077323339553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56046959342910769764452737 42035219507183077323339553)
    ·
      refine ⟨31526414630387307992504665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42035219507183077323339553 31526414630387307992504665)
      ·
        refine ⟨23644810972790480994378499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31526414630387307992504665 23644810972790480994378499)
        ·
          refine ⟨35467216459185721491567749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23644810972790480994378499 35467216459185721491567749)
          ·
            refine ⟨6650103086097322779668953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35467216459185721491567749 6650103086097322779668953)
            ·
              refine ⟨4987577314572992084751715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6650103086097322779668953 4987577314572992084751715)
              ·
                refine ⟨7481365971859488127127573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4987577314572992084751715 7481365971859488127127573)
                ·
                  refine ⟨350689029930913505959105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7481365971859488127127573 350689029930913505959105)
                  ·
                    rfl

theorem cell22_3073340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_3073340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073340 prefixEnd_3073340 := by exact prefixLift 3073340
  have htrace : WordTrace (prefixWord ++ tailWord_3073340) baseStart_3073340 baseEnd_3073340 := by
    simpa [prefixWord, tailWord_3073340, baseEnd_3073340] using wordTrace_append hprefix tailTrace_3073340
  have hstable : (prefixWord ++ tailWord_3073340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073340).length < 2 ^ (prefixWord ++ tailWord_3073340).sum := by decide
  have hdescent : baseEnd_3073340 < baseStart_3073340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073353 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 1, 6]
def baseStart_3073353 : Nat := 118140960795 + 3073353 * 2 ^ 59
def prefixEnd_3073353 : Nat := 4983230072969 + 3 ^ 40 * 3073353 * 2
def baseEnd_3073353 : Nat := 1052071539958412817302275

theorem tailTrace_3073353 : CollatzResearch.WordTrace tailWord_3073353 prefixEnd_3073353 1052071539958412817302275 := by
  unfold tailWord_3073353
  simp only [CollatzResearch.WordTrace]
  refine ⟨112094392834774442749128713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74729595223182961832752475 112094392834774442749128713)
  ·
    refine ⟨84070794626080832061846535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112094392834774442749128713 84070794626080832061846535)
    ·
      refine ⟨126106191939121248092769803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84070794626080832061846535 126106191939121248092769803)
      ·
        refine ⟨189159287908681872139154705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126106191939121248092769803 189159287908681872139154705)
        ·
          refine ⟨141869465931511404104366029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189159287908681872139154705 141869465931511404104366029)
          ·
            refine ⟨53201049724316776539137261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141869465931511404104366029 53201049724316776539137261)
            ·
              refine ⟨19950393646618791202176473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53201049724316776539137261 19950393646618791202176473)
              ·
                refine ⟨14962795234964093401632355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19950393646618791202176473 14962795234964093401632355)
                ·
                  refine ⟨22444192852446140102448533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14962795234964093401632355 22444192852446140102448533)
                  ·
                    refine ⟨1052071539958412817302275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22444192852446140102448533 1052071539958412817302275)
                    ·
                      rfl

theorem cell22_3073353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_3073353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073353 prefixEnd_3073353 := by exact prefixLift 3073353
  have htrace : WordTrace (prefixWord ++ tailWord_3073353) baseStart_3073353 baseEnd_3073353 := by
    simpa [prefixWord, tailWord_3073353, baseEnd_3073353] using wordTrace_append hprefix tailTrace_3073353
  have hstable : (prefixWord ++ tailWord_3073353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073353).length < 2 ^ (prefixWord ++ tailWord_3073353).sum := by decide
  have hdescent : baseEnd_3073353 < baseStart_3073353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073368 : List Nat := [2, 1, 2, 2, 1, 1, 5, 8]
def baseStart_3073368 : Nat := 118140960795 + 3073368 * 2 ^ 59
def prefixEnd_3073368 : Nat := 4983230072969 + 3 ^ 40 * 3073368 * 2
def baseEnd_3073368 : Nat := 116897408307217530908581

theorem tailTrace_3073368 : CollatzResearch.WordTrace tailWord_3073368 prefixEnd_3073368 116897408307217530908581 := by
  unfold tailWord_3073368
  simp only [CollatzResearch.WordTrace]
  refine ⟨56047469964860050155462379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74729959953146733540616505 56047469964860050155462379)
  ·
    refine ⟨84071204947290075233193569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56047469964860050155462379 84071204947290075233193569)
    ·
      refine ⟨63053403710467556424895177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84071204947290075233193569 63053403710467556424895177)
      ·
        refine ⟨47290052782850667318671383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63053403710467556424895177 47290052782850667318671383)
        ·
          refine ⟨70935079174276000978007075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47290052782850667318671383 70935079174276000978007075)
          ·
            refine ⟨106402618761414001467010613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70935079174276000978007075 106402618761414001467010613)
            ·
              refine ⟨9975245508882562637532245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106402618761414001467010613 9975245508882562637532245)
              ·
                refine ⟨116897408307217530908581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9975245508882562637532245 116897408307217530908581)
                ·
                  rfl

theorem cell22_3073368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 8].length) (baseStart_3073368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073368 prefixEnd_3073368 := by exact prefixLift 3073368
  have htrace : WordTrace (prefixWord ++ tailWord_3073368) baseStart_3073368 baseEnd_3073368 := by
    simpa [prefixWord, tailWord_3073368, baseEnd_3073368] using wordTrace_append hprefix tailTrace_3073368
  have hstable : (prefixWord ++ tailWord_3073368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073368).length < 2 ^ (prefixWord ++ tailWord_3073368).sum := by decide
  have hdescent : baseEnd_3073368 < baseStart_3073368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073434 : List Nat := [3, 1, 1, 4, 1, 1, 2, 5, 1, 3]
def baseStart_3073434 : Nat := 118140960795 + 3073434 * 2 ^ 59
def prefixEnd_3073434 : Nat := 4983230072969 + 3 ^ 40 * 3073434 * 2
def baseEnd_3073434 : Nat := 1052099267913755606027027

theorem tailTrace_3073434 : CollatzResearch.WordTrace tailWord_3073434 prefixEnd_3073434 1052099267913755606027027 := by
  unfold tailWord_3073434
  simp only [CollatzResearch.WordTrace]
  refine ⟨28024336786870248395706839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74731564764987329055218237 28024336786870248395706839)
  ·
    refine ⟨42036505180305372593560259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28024336786870248395706839 42036505180305372593560259)
    ·
      refine ⟨63054757770458058890340389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42036505180305372593560259 63054757770458058890340389)
      ·
        refine ⟨11822767081960886041938823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63054757770458058890340389 11822767081960886041938823)
        ·
          refine ⟨17734150622941329062908235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11822767081960886041938823 17734150622941329062908235)
          ·
            refine ⟨26601225934411993594362353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17734150622941329062908235 26601225934411993594362353)
            ·
              refine ⟨19950919450808995195771765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26601225934411993594362353 19950919450808995195771765)
              ·
                refine ⟨1870398698513343299603603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19950919450808995195771765 1870398698513343299603603)
                ·
                  refine ⟨2805598047770014949405405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1870398698513343299603603 2805598047770014949405405)
                  ·
                    refine ⟨1052099267913755606027027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2805598047770014949405405 1052099267913755606027027)
                    ·
                      rfl

theorem cell22_3073434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_3073434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073434 prefixEnd_3073434 := by exact prefixLift 3073434
  have htrace : WordTrace (prefixWord ++ tailWord_3073434) baseStart_3073434 baseEnd_3073434 := by
    simpa [prefixWord, tailWord_3073434, baseEnd_3073434] using wordTrace_append hprefix tailTrace_3073434
  have hstable : (prefixWord ++ tailWord_3073434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073434).length < 2 ^ (prefixWord ++ tailWord_3073434).sum := by decide
  have hdescent : baseEnd_3073434 < baseStart_3073434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073447 : List Nat := [1, 1, 6, 1, 1, 1, 4, 2, 5]
def baseStart_3073447 : Nat := 118140960795 + 3073447 * 2 ^ 59
def prefixEnd_3073447 : Nat := 4983230072969 + 3 ^ 40 * 3073447 * 2
def baseEnd_3073447 : Nat := 350701239359809301817329

theorem tailTrace_3073447 : CollatzResearch.WordTrace tailWord_3073447 prefixEnd_3073447 350701239359809301817329 := by
  unfold tailWord_3073447
  simp only [CollatzResearch.WordTrace]
  refine ⟨112097821296433896803050595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74731880864289264535367063 112097821296433896803050595)
  ·
    refine ⟨168146731944650845204575893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112097821296433896803050595 168146731944650845204575893)
    ·
      refine ⟨7881878059905508368964495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 168146731944650845204575893 7881878059905508368964495)
      ·
        refine ⟨11822817089858262553446743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7881878059905508368964495 11822817089858262553446743)
        ·
          refine ⟨17734225634787393830170115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11822817089858262553446743 17734225634787393830170115)
          ·
            refine ⟨26601338452181090745255173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17734225634787393830170115 26601338452181090745255173)
            ·
              refine ⟨4987750959783954514735345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26601338452181090745255173 4987750959783954514735345)
              ·
                refine ⟨3740813219837965886051509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4987750959783954514735345 3740813219837965886051509)
                ·
                  refine ⟨350701239359809301817329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3740813219837965886051509 350701239359809301817329)
                  ·
                    rfl

theorem cell22_3073447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 5].length) (baseStart_3073447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073447 prefixEnd_3073447 := by exact prefixLift 3073447
  have htrace : WordTrace (prefixWord ++ tailWord_3073447) baseStart_3073447 baseEnd_3073447 := by
    simpa [prefixWord, tailWord_3073447, baseEnd_3073447] using wordTrace_append hprefix tailTrace_3073447
  have hstable : (prefixWord ++ tailWord_3073447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073447).length < 2 ^ (prefixWord ++ tailWord_3073447).sum := by decide
  have hdescent : baseEnd_3073447 < baseStart_3073447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073509 : List Nat := [1, 3, 1, 5, 1, 1, 2, 4, 4]
def baseStart_3073509 : Nat := 118140960795 + 3073509 * 2 ^ 59
def prefixEnd_3073509 : Nat := 4983230072969 + 3 ^ 40 * 3073509 * 2
def baseEnd_3073509 : Nat := 350708313982160136800599

theorem tailTrace_3073509 : CollatzResearch.WordTrace tailWord_3073509 prefixEnd_3073509 350708313982160136800599 := by
  unfold tailWord_3073509
  simp only [CollatzResearch.WordTrace]
  refine ⟨112100082622209281391807581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74733388414806187594538387 112100082622209281391807581)
  ·
    refine ⟨42037530983328480521927843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112100082622209281391807581 42037530983328480521927843)
    ·
      refine ⟨63056296474992720782891765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42037530983328480521927843 63056296474992720782891765)
      ·
        refine ⟨5911527794530567573396103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63056296474992720782891765 5911527794530567573396103)
        ·
          refine ⟨8867291691795851360094155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5911527794530567573396103 8867291691795851360094155)
          ·
            refine ⟨13300937537693777040141233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8867291691795851360094155 13300937537693777040141233)
            ·
              refine ⟨9975703153270332780105925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13300937537693777040141233 9975703153270332780105925)
              ·
                refine ⟨1870444341238187396269861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9975703153270332780105925 1870444341238187396269861)
                ·
                  refine ⟨350708313982160136800599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1870444341238187396269861 350708313982160136800599)
                  ·
                    rfl

theorem cell22_3073509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_3073509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073509 prefixEnd_3073509 := by exact prefixLift 3073509
  have htrace : WordTrace (prefixWord ++ tailWord_3073509) baseStart_3073509 baseEnd_3073509 := by
    simpa [prefixWord, tailWord_3073509, baseEnd_3073509] using wordTrace_append hprefix tailTrace_3073509
  have hstable : (prefixWord ++ tailWord_3073509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073509).length < 2 ^ (prefixWord ++ tailWord_3073509).sum := by decide
  have hdescent : baseEnd_3073509 < baseStart_3073509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073522 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_3073522 : Nat := 118140960795 + 3073522 * 2 ^ 59
def prefixEnd_3073522 : Nat := 4983230072969 + 3 ^ 40 * 3073522 * 2
def baseEnd_3073522 : Nat := 1052129392112152709826757

theorem tailTrace_3073522 : CollatzResearch.WordTrace tailWord_3073522 prefixEnd_3073522 1052129392112152709826757 := by
  unfold tailWord_3073522
  simp only [CollatzResearch.WordTrace]
  refine ⟨28025139192790546153007705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74733704514108123074687213 28025139192790546153007705)
  ·
    refine ⟨21018854394592909614755779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28025139192790546153007705 21018854394592909614755779)
    ·
      refine ⟨31528281591889364422133669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21018854394592909614755779 31528281591889364422133669)
      ·
        refine ⟨5911552798479255829150063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31528281591889364422133669 5911552798479255829150063)
        ·
          refine ⟨8867329197718883743725095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5911552798479255829150063 8867329197718883743725095)
          ·
            refine ⟨13300993796578325615587643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8867329197718883743725095 13300993796578325615587643)
            ·
              refine ⟨19951490694867488423381465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13300993796578325615587643 19951490694867488423381465)
              ·
                refine ⟨14963618021150616317536099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19951490694867488423381465 14963618021150616317536099)
                ·
                  refine ⟨22445427031725924476304149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14963618021150616317536099 22445427031725924476304149)
                  ·
                    refine ⟨1052129392112152709826757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22445427031725924476304149 1052129392112152709826757)
                    ·
                      rfl

theorem cell22_3073522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_3073522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073522 prefixEnd_3073522 := by exact prefixLift 3073522
  have htrace : WordTrace (prefixWord ++ tailWord_3073522) baseStart_3073522 baseEnd_3073522 := by
    simpa [prefixWord, tailWord_3073522, baseEnd_3073522] using wordTrace_append hprefix tailTrace_3073522
  have hstable : (prefixWord ++ tailWord_3073522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073522).length < 2 ^ (prefixWord ++ tailWord_3073522).sum := by decide
  have hdescent : baseEnd_3073522 < baseStart_3073522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073537 : List Nat := [1, 2, 4, 1, 4, 1, 1, 8]
def baseStart_3073537 : Nat := 118140960795 + 3073537 * 2 ^ 59
def prefixEnd_3073537 : Nat := 4983230072969 + 3 ^ 40 * 3073537 * 2
def baseEnd_3073537 : Nat := 116903836324299741189079

theorem tailTrace_3073537 : CollatzResearch.WordTrace tailWord_3073537 prefixEnd_3073537 116903836324299741189079 := by
  unfold tailWord_3073537
  simp only [CollatzResearch.WordTrace]
  refine ⟨112101103866107842173826865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74734069244071894782551243 112101103866107842173826865)
  ·
    refine ⟨84075827899580881630370149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112101103866107842173826865 84075827899580881630370149)
    ·
      refine ⟨15764217731171415305694403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84075827899580881630370149 15764217731171415305694403)
      ·
        refine ⟨23646326596757122958541605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15764217731171415305694403 23646326596757122958541605)
        ·
          refine ⟨4433686236891960554726551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23646326596757122958541605 4433686236891960554726551)
          ·
            refine ⟨6650529355337940832089827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4433686236891960554726551 6650529355337940832089827)
            ·
              refine ⟨9975794033006911248134741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6650529355337940832089827 9975794033006911248134741)
              ·
                refine ⟨116903836324299741189079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9975794033006911248134741 116903836324299741189079)
                ·
                  rfl

theorem cell22_3073537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 8].length) (baseStart_3073537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073537 prefixEnd_3073537 := by exact prefixLift 3073537
  have htrace : WordTrace (prefixWord ++ tailWord_3073537) baseStart_3073537 baseEnd_3073537 := by
    simpa [prefixWord, tailWord_3073537, baseEnd_3073537] using wordTrace_append hprefix tailTrace_3073537
  have hstable : (prefixWord ++ tailWord_3073537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073537).length < 2 ^ (prefixWord ++ tailWord_3073537).sum := by decide
  have hdescent : baseEnd_3073537 < baseStart_3073537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073556 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3073556 : Nat := 118140960795 + 3073556 * 2 ^ 59
def prefixEnd_3073556 : Nat := 4983230072969 + 3 ^ 40 * 3073556 * 2
def baseEnd_3073556 : Nat := 1052141031006987954476653

theorem tailTrace_3073556 : CollatzResearch.WordTrace tailWord_3073556 prefixEnd_3073556 1052141031006987954476653 := by
  unfold tailWord_3073556
  simp only [CollatzResearch.WordTrace]
  refine ⟨56050898426519504209384261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74734531235359338945845681 56050898426519504209384261)
  ·
    refine ⟨10509543454972407039259549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56050898426519504209384261 10509543454972407039259549)
    ·
      refine ⟨3941078795614652639722331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10509543454972407039259549 3941078795614652639722331)
      ·
        refine ⟨5911618193421978959583497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3941078795614652639722331 5911618193421978959583497)
        ·
          refine ⟨4433713645066484219687623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5911618193421978959583497 4433713645066484219687623)
          ·
            refine ⟨6650570467599726329531435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4433713645066484219687623 6650570467599726329531435)
            ·
              refine ⟨9975855701399589494297153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6650570467599726329531435 9975855701399589494297153)
              ·
                refine ⟨7481891776049692120722865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9975855701399589494297153 7481891776049692120722865)
                ·
                  refine ⟨5611418832037269090542149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7481891776049692120722865 5611418832037269090542149)
                  ·
                    refine ⟨1052141031006987954476653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5611418832037269090542149 1052141031006987954476653)
                    ·
                      rfl

theorem cell22_3073556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3073556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073556 prefixEnd_3073556 := by exact prefixLift 3073556
  have htrace : WordTrace (prefixWord ++ tailWord_3073556) baseStart_3073556 baseEnd_3073556 := by
    simpa [prefixWord, tailWord_3073556, baseEnd_3073556] using wordTrace_append hprefix tailTrace_3073556
  have hstable : (prefixWord ++ tailWord_3073556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073556).length < 2 ^ (prefixWord ++ tailWord_3073556).sum := by decide
  have hdescent : baseEnd_3073556 < baseStart_3073556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073569 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 3, 3]
def baseStart_3073569 : Nat := 118140960795 + 3073569 * 2 ^ 59
def prefixEnd_3073569 : Nat := 4983230072969 + 3 ^ 40 * 3073569 * 2
def baseEnd_3073569 : Nat := 1052145481172660253901613

theorem tailTrace_3073569 : CollatzResearch.WordTrace tailWord_3073569 prefixEnd_3073569 1052145481172660253901613 := by
  unfold tailWord_3073569
  simp only [CollatzResearch.WordTrace]
  refine ⟨112102271001991911638991761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74734847334661274425994507 112102271001991911638991761)
  ·
    refine ⟨84076703251493933729243821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112102271001991911638991761 84076703251493933729243821)
    ·
      refine ⟨31528763719310225148466433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84076703251493933729243821 31528763719310225148466433)
      ·
        refine ⟨23646572789482668861349825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31528763719310225148466433 23646572789482668861349825)
        ·
          refine ⟨17734929592112001646012369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23646572789482668861349825 17734929592112001646012369)
          ·
            refine ⟨13301197194084001234509277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17734929592112001646012369 13301197194084001234509277)
            ·
              refine ⟨4987948947781500462940979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13301197194084001234509277 4987948947781500462940979)
              ·
                refine ⟨7481923421672250694411469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4987948947781500462940979 7481923421672250694411469)
                ·
                  refine ⟨2805721283127094010404301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7481923421672250694411469 2805721283127094010404301)
                  ·
                    refine ⟨1052145481172660253901613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2805721283127094010404301 1052145481172660253901613)
                    ·
                      rfl

theorem cell22_3073569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_3073569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073569 prefixEnd_3073569 := by exact prefixLift 3073569
  have htrace : WordTrace (prefixWord ++ tailWord_3073569) baseStart_3073569 baseEnd_3073569 := by
    simpa [prefixWord, tailWord_3073569, baseEnd_3073569] using wordTrace_append hprefix tailTrace_3073569
  have hstable : (prefixWord ++ tailWord_3073569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073569).length < 2 ^ (prefixWord ++ tailWord_3073569).sum := by decide
  have hdescent : baseEnd_3073569 < baseStart_3073569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073657 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 1, 6]
def baseStart_3073657 : Nat := 118140960795 + 3073657 * 2 ^ 59
def prefixEnd_3073657 : Nat := 4983230072969 + 3 ^ 40 * 3073657 * 2
def baseEnd_3073657 : Nat := 1052175605371057357701343

theorem tailTrace_3073657 : CollatzResearch.WordTrace tailWord_3073657 prefixEnd_3073657 1052175605371057357701343 := by
  unfold tailWord_3073657
  simp only [CollatzResearch.WordTrace]
  refine ⟨112105480625673102668195225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74736987083782068445463483 112105480625673102668195225)
  ·
    refine ⟨84079110469254827001146419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112105480625673102668195225 84079110469254827001146419)
    ·
      refine ⟨126118665703882240501719629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84079110469254827001146419 126118665703882240501719629)
      ·
        refine ⟨47294499638955840188144861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126118665703882240501719629 47294499638955840188144861)
        ·
          refine ⟨17735437364608440070554323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47294499638955840188144861 17735437364608440070554323)
          ·
            refine ⟨26603156046912660105831485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17735437364608440070554323 26603156046912660105831485)
            ·
              refine ⟨9976183517592247539686807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26603156046912660105831485 9976183517592247539686807)
              ·
                refine ⟨14964275276388371309530211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9976183517592247539686807 14964275276388371309530211)
                ·
                  refine ⟨22446412914582556964295317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14964275276388371309530211 22446412914582556964295317)
                  ·
                    refine ⟨1052175605371057357701343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22446412914582556964295317 1052175605371057357701343)
                    ·
                      rfl

theorem cell22_3073657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_3073657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073657 prefixEnd_3073657 := by exact prefixLift 3073657
  have htrace : WordTrace (prefixWord ++ tailWord_3073657) baseStart_3073657 baseEnd_3073657 := by
    simpa [prefixWord, tailWord_3073657, baseEnd_3073657] using wordTrace_append hprefix tailTrace_3073657
  have hstable : (prefixWord ++ tailWord_3073657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073657).length < 2 ^ (prefixWord ++ tailWord_3073657).sum := by decide
  have hdescent : baseEnd_3073657 < baseStart_3073657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073661 : List Nat := [1, 4, 1, 1, 4, 2, 2, 3, 4]
def baseStart_3073661 : Nat := 118140960795 + 3073661 * 2 ^ 59
def prefixEnd_3073661 : Nat := 4983230072969 + 3 ^ 40 * 3073661 * 2
def baseEnd_3073661 : Nat := 350725658217600893533777

theorem tailTrace_3073661 : CollatzResearch.WordTrace tailWord_3073661 prefixEnd_3073661 350725658217600893533777 := by
  unfold tailWord_3073661
  simp only [CollatzResearch.WordTrace]
  refine ⟨112105626517658611351340837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74737084345105740900893891 112105626517658611351340837)
  ·
    refine ⟨21019804972060989628376407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112105626517658611351340837 21019804972060989628376407)
    ·
      refine ⟨31529707458091484442564611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21019804972060989628376407 31529707458091484442564611)
      ·
        refine ⟨47294561187137226663846917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31529707458091484442564611 47294561187137226663846917)
        ·
          refine ⟨8867730222588229999471297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47294561187137226663846917 8867730222588229999471297)
          ·
            refine ⟨6650797666941172499603473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8867730222588229999471297 6650797666941172499603473)
            ·
              refine ⟨4988098250205879374702605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6650797666941172499603473 4988098250205879374702605)
              ·
                refine ⟨1870536843827204765513477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4988098250205879374702605 1870536843827204765513477)
                ·
                  refine ⟨350725658217600893533777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1870536843827204765513477 350725658217600893533777)
                  ·
                    rfl

theorem cell22_3073661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_3073661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073661 prefixEnd_3073661 := by exact prefixLift 3073661
  have htrace : WordTrace (prefixWord ++ tailWord_3073661) baseStart_3073661 baseEnd_3073661 := by
    simpa [prefixWord, tailWord_3073661, baseEnd_3073661] using wordTrace_append hprefix tailTrace_3073661
  have hstable : (prefixWord ++ tailWord_3073661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073661).length < 2 ^ (prefixWord ++ tailWord_3073661).sum := by decide
  have hdescent : baseEnd_3073661 < baseStart_3073661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073738 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 3, 3]
def baseStart_3073738 : Nat := 118140960795 + 3073738 * 2 ^ 59
def prefixEnd_3073738 : Nat := 4983230072969 + 3 ^ 40 * 3073738 * 2
def baseEnd_3073738 : Nat := 1052203333326400146426095

theorem tailTrace_3073738 : CollatzResearch.WordTrace tailWord_3073738 prefixEnd_3073738 1052203333326400146426095 := by
  unfold tailWord_3073738
  simp only [CollatzResearch.WordTrace]
  refine ⟨28027108734594913375473467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74738956625586435667929245 28027108734594913375473467)
  ·
    refine ⟨42040663101892370063210201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28027108734594913375473467 42040663101892370063210201)
    ·
      refine ⟨31530497326419277547407651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42040663101892370063210201 31530497326419277547407651)
      ·
        refine ⟨47295745989628916321111477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31530497326419277547407651 47295745989628916321111477)
        ·
          refine ⟨4433976186527710905104201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47295745989628916321111477 4433976186527710905104201)
          ·
            refine ⟨3325482139895783178828151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4433976186527710905104201 3325482139895783178828151)
            ·
              refine ⟨4988223209843674768242227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3325482139895783178828151 4988223209843674768242227)
              ·
                refine ⟨7482334814765512152363341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4988223209843674768242227 7482334814765512152363341)
                ·
                  refine ⟨2805875555537067057136253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7482334814765512152363341 2805875555537067057136253)
                  ·
                    refine ⟨1052203333326400146426095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2805875555537067057136253 1052203333326400146426095)
                    ·
                      rfl

theorem cell22_3073738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_3073738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073738 prefixEnd_3073738 := by exact prefixLift 3073738
  have htrace : WordTrace (prefixWord ++ tailWord_3073738) baseStart_3073738 baseEnd_3073738 := by
    simpa [prefixWord, tailWord_3073738, baseEnd_3073738] using wordTrace_append hprefix tailTrace_3073738
  have hstable : (prefixWord ++ tailWord_3073738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073738).length < 2 ^ (prefixWord ++ tailWord_3073738).sum := by decide
  have hdescent : baseEnd_3073738 < baseStart_3073738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073764 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_3073764 : Nat := 118140960795 + 3073764 * 2 ^ 59
def prefixEnd_3073764 : Nat := 4983230072969 + 3 ^ 40 * 3073764 * 2
def baseEnd_3073764 : Nat := 1052212233657744745276015

theorem tailTrace_3073764 : CollatzResearch.WordTrace tailWord_3073764 prefixEnd_3073764 1052212233657744745276015 := by
  unfold tailWord_3073764
  simp only [CollatzResearch.WordTrace]
  refine ⟨56054691618142729971170173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74739588824190306628226897 56054691618142729971170173)
  ·
    refine ⟨21020509356803523739188815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56054691618142729971170173 21020509356803523739188815)
    ·
      refine ⟨31530764035205285608783223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21020509356803523739188815 31530764035205285608783223)
      ·
        refine ⟨47296146052807928413174835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31530764035205285608783223 47296146052807928413174835)
        ·
          refine ⟨70944219079211892619762253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47296146052807928413174835 70944219079211892619762253)
          ·
            refine ⟨26604082154704459732410845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70944219079211892619762253 26604082154704459732410845)
            ·
              refine ⟨9976530808014172399654067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26604082154704459732410845 9976530808014172399654067)
              ·
                refine ⟨14964796212021258599481101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9976530808014172399654067 14964796212021258599481101)
                ·
                  refine ⟨5611798579507971974805413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14964796212021258599481101 5611798579507971974805413)
                  ·
                    refine ⟨1052212233657744745276015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5611798579507971974805413 1052212233657744745276015)
                    ·
                      rfl

theorem cell22_3073764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_3073764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073764 prefixEnd_3073764 := by exact prefixLift 3073764
  have htrace : WordTrace (prefixWord ++ tailWord_3073764) baseStart_3073764 baseEnd_3073764 := by
    simpa [prefixWord, tailWord_3073764, baseEnd_3073764] using wordTrace_append hprefix tailTrace_3073764
  have hstable : (prefixWord ++ tailWord_3073764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073764).length < 2 ^ (prefixWord ++ tailWord_3073764).sum := by decide
  have hdescent : baseEnd_3073764 < baseStart_3073764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073807 : List Nat := [1, 1, 2, 1, 1, 1, 4, 11]
def baseStart_3073807 : Nat := 118140960795 + 3073807 * 2 ^ 59
def prefixEnd_3073807 : Nat := 4983230072969 + 3 ^ 40 * 3073807 * 2
def baseEnd_3073807 : Nat := 116914105937389662938987

theorem tailTrace_3073807 : CollatzResearch.WordTrace tailWord_3073807 prefixEnd_3073807 116914105937389662938987 := by
  unfold tailWord_3073807
  simp only [CollatzResearch.WordTrace]
  refine ⟨112110951575129678286155675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74740634383419785524103783 112110951575129678286155675)
  ·
    refine ⟨168166427362694517429233513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112110951575129678286155675 168166427362694517429233513)
    ·
      refine ⟨126124820522020888071925135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168166427362694517429233513 126124820522020888071925135)
      ·
        refine ⟨189187230783031332107887703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126124820522020888071925135 189187230783031332107887703)
        ·
          refine ⟨283780846174546998161831555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189187230783031332107887703 283780846174546998161831555)
          ·
            refine ⟨425671269261820497242747333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283780846174546998161831555 425671269261820497242747333)
            ·
              refine ⟨79813362986591343233015125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 425671269261820497242747333 79813362986591343233015125)
              ·
                refine ⟨116914105937389662938987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 79813362986591343233015125 116914105937389662938987)
                ·
                  rfl

theorem cell22_3073807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 11].length) (baseStart_3073807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073807 prefixEnd_3073807 := by exact prefixLift 3073807
  have htrace : WordTrace (prefixWord ++ tailWord_3073807) baseStart_3073807 baseEnd_3073807 := by
    simpa [prefixWord, tailWord_3073807, baseEnd_3073807] using wordTrace_append hprefix tailTrace_3073807
  have hstable : (prefixWord ++ tailWord_3073807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073807).length < 2 ^ (prefixWord ++ tailWord_3073807).sum := by decide
  have hdescent : baseEnd_3073807 < baseStart_3073807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073845 : List Nat := [1, 3, 3, 1, 4, 2, 1, 2, 2, 3]
def baseStart_3073845 : Nat := 118140960795 + 3073845 * 2 ^ 59
def prefixEnd_3073845 : Nat := 4983230072969 + 3 ^ 40 * 3073845 * 2
def baseEnd_3073845 : Nat := 1052239961613087534000767

theorem tailTrace_3073845 : CollatzResearch.WordTrace tailWord_3073845 prefixEnd_3073845 1052239961613087534000767 := by
  unfold tailWord_3073845
  simp only [CollatzResearch.WordTrace]
  refine ⟨112112337548992010776038989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74741558365994673850692659 112112337548992010776038989)
  ·
    refine ⟨42042126580872004041014621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112112337548992010776038989 42042126580872004041014621)
    ·
      refine ⟨15765797467827001515380483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42042126580872004041014621 15765797467827001515380483)
      ·
        refine ⟨23648696201740502273070725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15765797467827001515380483 23648696201740502273070725)
        ·
          refine ⟨4434130537826344176200761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23648696201740502273070725 4434130537826344176200761)
          ·
            refine ⟨3325597903369758132150571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4434130537826344176200761 3325597903369758132150571)
            ·
              refine ⟨4988396855054637198225857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3325597903369758132150571 4988396855054637198225857)
              ·
                refine ⟨3741297641290977898669393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4988396855054637198225857 3741297641290977898669393)
                ·
                  refine ⟨2805973230968233424002045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3741297641290977898669393 2805973230968233424002045)
                  ·
                    refine ⟨1052239961613087534000767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2805973230968233424002045 1052239961613087534000767)
                    ·
                      rfl

theorem cell22_3073845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_3073845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073845 prefixEnd_3073845 := by exact prefixLift 3073845
  have htrace : WordTrace (prefixWord ++ tailWord_3073845) baseStart_3073845 baseEnd_3073845 := by
    simpa [prefixWord, tailWord_3073845, baseEnd_3073845] using wordTrace_append hprefix tailTrace_3073845
  have hstable : (prefixWord ++ tailWord_3073845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073845).length < 2 ^ (prefixWord ++ tailWord_3073845).sum := by decide
  have hdescent : baseEnd_3073845 < baseStart_3073845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073899 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 5, 4]
def baseStart_3073899 : Nat := 118140960795 + 3073899 * 2 ^ 59
def prefixEnd_3073899 : Nat := 4983230072969 + 3 ^ 40 * 3073899 * 2
def baseEnd_3073899 : Nat := 1052258446916649393150601

theorem tailTrace_3073899 : CollatzResearch.WordTrace tailWord_3073899 prefixEnd_3073899 1052258446916649393150601 := by
  unfold tailWord_3073899
  simp only [CollatzResearch.WordTrace]
  refine ⟨112114307090796377998504751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74742871393864251999003167 112114307090796377998504751)
  ·
    refine ⟨168171460636194566997757127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112114307090796377998504751 168171460636194566997757127)
    ·
      refine ⟨252257190954291850496635691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168171460636194566997757127 252257190954291850496635691)
      ·
        refine ⟨378385786431437775744953537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252257190954291850496635691 378385786431437775744953537)
        ·
          refine ⟨283789339823578331808715153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378385786431437775744953537 283789339823578331808715153)
          ·
            refine ⟨212842004867683748856536365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283789339823578331808715153 212842004867683748856536365)
            ·
              refine ⟨79815751825381405821201137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212842004867683748856536365 79815751825381405821201137)
              ·
                refine ⟨59861813869036054365900853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79815751825381405821201137 59861813869036054365900853)
                ·
                  refine ⟨5612045050222130096803205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59861813869036054365900853 5612045050222130096803205)
                  ·
                    refine ⟨1052258446916649393150601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5612045050222130096803205 1052258446916649393150601)
                    ·
                      rfl

theorem cell22_3073899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 4].length) (baseStart_3073899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073899 prefixEnd_3073899 := by exact prefixLift 3073899
  have htrace : WordTrace (prefixWord ++ tailWord_3073899) baseStart_3073899 baseEnd_3073899 := by
    simpa [prefixWord, tailWord_3073899, baseEnd_3073899] using wordTrace_append hprefix tailTrace_3073899
  have hstable : (prefixWord ++ tailWord_3073899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073899).length < 2 ^ (prefixWord ++ tailWord_3073899).sum := by decide
  have hdescent : baseEnd_3073899 < baseStart_3073899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073946 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_3073946 : Nat := 118140960795 + 3073946 * 2 ^ 59
def prefixEnd_3073946 : Nat := 4983230072969 + 3 ^ 40 * 3073946 * 2
def baseEnd_3073946 : Nat := 1052274535977156937225457

theorem tailTrace_3073946 : CollatzResearch.WordTrace tailWord_3073946 prefixEnd_3073946 1052274535977156937225457 := by
  unfold tailWord_3073946
  simp only [CollatzResearch.WordTrace]
  refine ⟨28029005330406526256366423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74744014214417403350310461 28029005330406526256366423)
  ·
    refine ⟨42043507995609789384549635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28029005330406526256366423 42043507995609789384549635)
    ·
      refine ⟨63065261993414684076824453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42043507995609789384549635 63065261993414684076824453)
      ·
        refine ⟨11824736623765253264404585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63065261993414684076824453 11824736623765253264404585)
        ·
          refine ⟨8868552467823939948303439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11824736623765253264404585 8868552467823939948303439)
          ·
            refine ⟨13302828701735909922455159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8868552467823939948303439 13302828701735909922455159)
            ·
              refine ⟨19954243052603864883682739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13302828701735909922455159 19954243052603864883682739)
              ·
                refine ⟨29931364578905797325524109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19954243052603864883682739 29931364578905797325524109)
                ·
                  refine ⟨11224261717089673997071541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29931364578905797325524109 11224261717089673997071541)
                  ·
                    refine ⟨1052274535977156937225457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11224261717089673997071541 1052274535977156937225457)
                    ·
                      rfl

theorem cell22_3073946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_3073946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073946 prefixEnd_3073946 := by exact prefixLift 3073946
  have htrace : WordTrace (prefixWord ++ tailWord_3073946) baseStart_3073946 baseEnd_3073946 := by
    simpa [prefixWord, tailWord_3073946, baseEnd_3073946] using wordTrace_append hprefix tailTrace_3073946
  have hstable : (prefixWord ++ tailWord_3073946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073946).length < 2 ^ (prefixWord ++ tailWord_3073946).sum := by decide
  have hdescent : baseEnd_3073946 < baseStart_3073946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073980 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 1, 5]
def baseStart_3073980 : Nat := 118140960795 + 3073980 * 2 ^ 59
def prefixEnd_3073980 : Nat := 4983230072969 + 3 ^ 40 * 3073980 * 2
def baseEnd_3073980 : Nat := 1052286174871992181875353

theorem tailTrace_3073980 : CollatzResearch.WordTrace tailWord_3073980 prefixEnd_3073980 1052286174871992181875353 := by
  unfold tailWord_3073980
  simp only [CollatzResearch.WordTrace]
  refine ⟨56058630701751464416101697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74744840935668619221468929 56058630701751464416101697)
  ·
    refine ⟨42043973026313598312076273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56058630701751464416101697 42043973026313598312076273)
    ·
      refine ⟨31532979769735198734057205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42043973026313598312076273 31532979769735198734057205)
      ·
        refine ⟨2956216853412674881317863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31532979769735198734057205 2956216853412674881317863)
        ·
          refine ⟨4434325280119012321976795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956216853412674881317863 4434325280119012321976795)
          ·
            refine ⟨6651487920178518482965193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4434325280119012321976795 6651487920178518482965193)
            ·
              refine ⟨4988615940133888862223895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6651487920178518482965193 4988615940133888862223895)
              ·
                refine ⟨7482923910200833293335843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4988615940133888862223895 7482923910200833293335843)
                ·
                  refine ⟨11224385865301249940003765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7482923910200833293335843 11224385865301249940003765)
                  ·
                    refine ⟨1052286174871992181875353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11224385865301249940003765 1052286174871992181875353)
                    ·
                      rfl

theorem cell22_3073980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_3073980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3073980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3073980 prefixEnd_3073980 := by exact prefixLift 3073980
  have htrace : WordTrace (prefixWord ++ tailWord_3073980) baseStart_3073980 baseEnd_3073980 := by
    simpa [prefixWord, tailWord_3073980, baseEnd_3073980] using wordTrace_append hprefix tailTrace_3073980
  have hstable : (prefixWord ++ tailWord_3073980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073980).length < 2 ^ (prefixWord ++ tailWord_3073980).sum := by decide
  have hdescent : baseEnd_3073980 < baseStart_3073980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074051 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 3, 4]
def baseStart_3074051 : Nat := 118140960795 + 3074051 * 2 ^ 59
def prefixEnd_3074051 : Nat := 4983230072969 + 3 ^ 40 * 3074051 * 2
def baseEnd_3074051 : Nat := 1052310479622971663350135

theorem tailTrace_3074051 : CollatzResearch.WordTrace tailWord_3074051 prefixEnd_3074051 1052310479622971663350135 := by
  unfold tailWord_3074051
  simp only [CollatzResearch.WordTrace]
  refine ⟨112119850986245707958038007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74746567324163805305358671 112119850986245707958038007)
  ·
    refine ⟨168179776479368561937057011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112119850986245707958038007 168179776479368561937057011)
    ·
      refine ⟨252269664719052842905585517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168179776479368561937057011 252269664719052842905585517)
      ·
        refine ⟨94601124269644816089594569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252269664719052842905585517 94601124269644816089594569)
        ·
          refine ⟨70950843202233612067195927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94601124269644816089594569 70950843202233612067195927)
          ·
            refine ⟨106426264803350418100793891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70950843202233612067195927 106426264803350418100793891)
            ·
              refine ⟨159639397205025627151190837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106426264803350418100793891 159639397205025627151190837)
              ·
                refine ⟨14966193487971152545424141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159639397205025627151190837 14966193487971152545424141)
                ·
                  refine ⟨5612322557989182204534053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14966193487971152545424141 5612322557989182204534053)
                  ·
                    refine ⟨1052310479622971663350135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5612322557989182204534053 1052310479622971663350135)
                    ·
                      rfl

theorem cell22_3074051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 4].length) (baseStart_3074051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074051 prefixEnd_3074051 := by exact prefixLift 3074051
  have htrace : WordTrace (prefixWord ++ tailWord_3074051) baseStart_3074051 baseEnd_3074051 := by
    simpa [prefixWord, tailWord_3074051, baseEnd_3074051] using wordTrace_append hprefix tailTrace_3074051
  have hstable : (prefixWord ++ tailWord_3074051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074051).length < 2 ^ (prefixWord ++ tailWord_3074051).sum := by decide
  have hdescent : baseEnd_3074051 < baseStart_3074051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074111 : List Nat := [1, 1, 2, 2, 3, 1, 4, 8]
def baseStart_3074111 : Nat := 118140960795 + 3074111 * 2 ^ 59
def prefixEnd_3074111 : Nat := 4983230072969 + 3 ^ 40 * 3074111 * 2
def baseEnd_3074111 : Nat := 116925668761016834094439

theorem tailTrace_3074111 : CollatzResearch.WordTrace tailWord_3074111 prefixEnd_3074111 116925668761016834094439 := by
  unfold tailWord_3074111
  simp only [CollatzResearch.WordTrace]
  refine ⟨112122039366028338205222187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74748026244018892136814791 112122039366028338205222187)
  ·
    refine ⟨168183059049042507307833281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112122039366028338205222187 168183059049042507307833281)
    ·
      refine ⟨126137294286781880480874961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168183059049042507307833281 126137294286781880480874961)
      ·
        refine ⟨94602970715086410360656221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126137294286781880480874961 94602970715086410360656221)
        ·
          refine ⟨35476114018157403885246083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94602970715086410360656221 35476114018157403885246083)
          ·
            refine ⟨53214171027236105827869125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35476114018157403885246083 53214171027236105827869125)
            ·
              refine ⟨9977657067606769842725461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53214171027236105827869125 9977657067606769842725461)
              ·
                refine ⟨116925668761016834094439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9977657067606769842725461 116925668761016834094439)
                ·
                  rfl

theorem cell22_3074111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 8].length) (baseStart_3074111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074111 prefixEnd_3074111 := by exact prefixLift 3074111
  have htrace : WordTrace (prefixWord ++ tailWord_3074111) baseStart_3074111 baseEnd_3074111 := by
    simpa [prefixWord, tailWord_3074111, baseEnd_3074111] using wordTrace_append hprefix tailTrace_3074111
  have hstable : (prefixWord ++ tailWord_3074111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074111).length < 2 ^ (prefixWord ++ tailWord_3074111).sum := by decide
  have hdescent : baseEnd_3074111 < baseStart_3074111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074134 : List Nat := [5, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_3074134 : Nat := 118140960795 + 3074134 * 2 ^ 59
def prefixEnd_3074134 : Nat := 4983230072969 + 3 ^ 40 * 3074134 * 2
def baseEnd_3074134 : Nat := 350779630739729037841627

theorem tailTrace_3074134 : CollatzResearch.WordTrace tailWord_3074134 prefixEnd_3074134 350779630739729037841627 := by
  unfold tailWord_3074134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7007679890309063320831841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74748585496630008755539637 7007679890309063320831841)
  ·
    refine ⟨5255759917731797490623881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7007679890309063320831841 5255759917731797490623881)
    ·
      refine ⟨3941819938298848117967911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5255759917731797490623881 3941819938298848117967911)
      ·
        refine ⟨5912729907448272176951867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3941819938298848117967911 5912729907448272176951867)
        ·
          refine ⟨8869094861172408265427801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5912729907448272176951867 8869094861172408265427801)
          ·
            refine ⟨6651821145879306199070851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8869094861172408265427801 6651821145879306199070851)
            ·
              refine ⟨9977731718818959298606277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6651821145879306199070851 9977731718818959298606277)
              ·
                refine ⟨1870824697278554868488677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9977731718818959298606277 1870824697278554868488677)
                ·
                  refine ⟨350779630739729037841627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1870824697278554868488677 350779630739729037841627)
                  ·
                    rfl

theorem cell22_3074134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_3074134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074134 prefixEnd_3074134 := by exact prefixLift 3074134
  have htrace : WordTrace (prefixWord ++ tailWord_3074134) baseStart_3074134 baseEnd_3074134 := by
    simpa [prefixWord, tailWord_3074134, baseEnd_3074134] using wordTrace_append hprefix tailTrace_3074134
  have hstable : (prefixWord ++ tailWord_3074134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074134).length < 2 ^ (prefixWord ++ tailWord_3074134).sum := by decide
  have hdescent : baseEnd_3074134 < baseStart_3074134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074158 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3074158 : Nat := 118140960795 + 3074158 * 2 ^ 59
def prefixEnd_3074158 : Nat := 4983230072969 + 3 ^ 40 * 3074158 * 2
def baseEnd_3074158 : Nat := 1052347107909659050924807

theorem tailTrace_3074158 : CollatzResearch.WordTrace tailWord_3074158 prefixEnd_3074158 1052347107909659050924807 := by
  unfold tailWord_3074158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14015469199607258154022891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74749169064572043488122085 14015469199607258154022891)
  ·
    refine ⟨21023203799410887231034337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14015469199607258154022891 21023203799410887231034337)
    ·
      refine ⟨15767402849558165423275753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21023203799410887231034337 15767402849558165423275753)
      ·
        refine ⟨11825552137168624067456815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15767402849558165423275753 11825552137168624067456815)
        ·
          refine ⟨17738328205752936101185223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11825552137168624067456815 17738328205752936101185223)
          ·
            refine ⟨26607492308629404151777835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17738328205752936101185223 26607492308629404151777835)
            ·
              refine ⟨39911238462944106227666753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26607492308629404151777835 39911238462944106227666753)
              ·
                refine ⟨29933428847208079670750065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39911238462944106227666753 29933428847208079670750065)
                ·
                  refine ⟨22450071635406059753062549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29933428847208079670750065 22450071635406059753062549)
                  ·
                    refine ⟨1052347107909659050924807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22450071635406059753062549 1052347107909659050924807)
                    ·
                      rfl

theorem cell22_3074158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3074158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074158 prefixEnd_3074158 := by exact prefixLift 3074158
  have htrace : WordTrace (prefixWord ++ tailWord_3074158) baseStart_3074158 baseEnd_3074158 := by
    simpa [prefixWord, tailWord_3074158, baseEnd_3074158] using wordTrace_append hprefix tailTrace_3074158
  have hstable : (prefixWord ++ tailWord_3074158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074158).length < 2 ^ (prefixWord ++ tailWord_3074158).sum := by decide
  have hdescent : baseEnd_3074158 < baseStart_3074158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074160 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 3, 3]
def baseStart_3074160 : Nat := 118140960795 + 3074160 * 2 ^ 59
def prefixEnd_3074160 : Nat := 4983230072969 + 3 ^ 40 * 3074160 * 2
def baseEnd_3074160 : Nat := 1052347792550531712374801

theorem tailTrace_3074160 : CollatzResearch.WordTrace tailWord_3074160 prefixEnd_3074160 1052347792550531712374801 := by
  unfold tailWord_3074160
  simp only [CollatzResearch.WordTrace]
  refine ⟨56061913271425409786877967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74749217695233879715837289 56061913271425409786877967)
  ·
    refine ⟨84092869907138114680316951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56061913271425409786877967 84092869907138114680316951)
    ·
      refine ⟨126139304860707172020475427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84092869907138114680316951 126139304860707172020475427)
      ·
        refine ⟨189208957291060758030713141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126139304860707172020475427 189208957291060758030713141)
        ·
          refine ⟨17738339746036946065379357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189208957291060758030713141 17738339746036946065379357)
          ·
            refine ⟨6651877404763854774517259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17738339746036946065379357 6651877404763854774517259)
            ·
              refine ⟨9977816107145782161775889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6651877404763854774517259 9977816107145782161775889)
              ·
                refine ⟨7483362080359336621331917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9977816107145782161775889 7483362080359336621331917)
                ·
                  refine ⟨2806260780134751232999469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7483362080359336621331917 2806260780134751232999469)
                  ·
                    refine ⟨1052347792550531712374801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2806260780134751232999469 1052347792550531712374801)
                    ·
                      rfl

theorem cell22_3074160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 3, 3].length) (baseStart_3074160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074160 prefixEnd_3074160 := by exact prefixLift 3074160
  have htrace : WordTrace (prefixWord ++ tailWord_3074160) baseStart_3074160 baseEnd_3074160 := by
    simpa [prefixWord, tailWord_3074160, baseEnd_3074160] using wordTrace_append hprefix tailTrace_3074160
  have hstable : (prefixWord ++ tailWord_3074160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074160).length < 2 ^ (prefixWord ++ tailWord_3074160).sum := by decide
  have hdescent : baseEnd_3074160 < baseStart_3074160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074190 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_3074190 : Nat := 118140960795 + 3074190 * 2 ^ 59
def prefixEnd_3074190 : Nat := 4983230072969 + 3 ^ 40 * 3074190 * 2
def baseEnd_3074190 : Nat := 350786020721207211374903

theorem tailTrace_3074190 : CollatzResearch.WordTrace tailWord_3074190 prefixEnd_3074190 350786020721207211374903 := by
  unfold tailWord_3074190
  simp only [CollatzResearch.WordTrace]
  refine ⟨14015615091592766837168503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74749947155161423131565349 14015615091592766837168503)
  ·
    refine ⟨21023422637389150255752755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14015615091592766837168503 21023422637389150255752755)
    ·
      refine ⟨31535133956083725383629133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21023422637389150255752755 31535133956083725383629133)
      ·
        refine ⟨11825675233531397018860925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31535133956083725383629133 11825675233531397018860925)
        ·
          refine ⟨4434628212574273882072847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11825675233531397018860925 4434628212574273882072847)
          ·
            refine ⟨6651942318861410823109271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4434628212574273882072847 6651942318861410823109271)
            ·
              refine ⟨9977913478292116234663907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6651942318861410823109271 9977913478292116234663907)
              ·
                refine ⟨14966870217438174351995861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9977913478292116234663907 14966870217438174351995861)
                ·
                  refine ⟨350786020721207211374903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14966870217438174351995861 350786020721207211374903)
                  ·
                    rfl

theorem cell22_3074190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_3074190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074190 prefixEnd_3074190 := by exact prefixLift 3074190
  have htrace : WordTrace (prefixWord ++ tailWord_3074190) baseStart_3074190 baseEnd_3074190 := by
    simpa [prefixWord, tailWord_3074190, baseEnd_3074190] using wordTrace_append hprefix tailTrace_3074190
  have hstable : (prefixWord ++ tailWord_3074190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074190).length < 2 ^ (prefixWord ++ tailWord_3074190).sum := by decide
  have hdescent : baseEnd_3074190 < baseStart_3074190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074207 : List Nat := [1, 1, 2, 6, 1, 2, 3, 1, 5]
def baseStart_3074207 : Nat := 118140960795 + 3074207 * 2 ^ 59
def prefixEnd_3074207 : Nat := 4983230072969 + 3 ^ 40 * 3074207 * 2
def baseEnd_3074207 : Nat := 350787960537013085483219

theorem tailTrace_3074207 : CollatzResearch.WordTrace tailWord_3074207 prefixEnd_3074207 350787960537013085483219 := by
  unfold tailWord_3074207
  simp only [CollatzResearch.WordTrace]
  refine ⟨112125540773680546600716875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74750360515787031067144583 112125540773680546600716875)
  ·
    refine ⟨168188311160520819901075313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112125540773680546600716875 168188311160520819901075313)
    ·
      refine ⟨126141233370390614925806485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168188311160520819901075313 126141233370390614925806485)
      ·
        refine ⟨5912870314237060074647179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126141233370390614925806485 5912870314237060074647179)
        ·
          refine ⟨8869305471355590111970769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5912870314237060074647179 8869305471355590111970769)
          ·
            refine ⟨6651979103516692583978077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8869305471355590111970769 6651979103516692583978077)
            ·
              refine ⟨2494492163818759718991779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6651979103516692583978077 2494492163818759718991779)
              ·
                refine ⟨3741738245728139578487669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2494492163818759718991779 3741738245728139578487669)
                ·
                  refine ⟨350787960537013085483219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3741738245728139578487669 350787960537013085483219)
                  ·
                    rfl

theorem cell22_3074207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 5].length) (baseStart_3074207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074207 prefixEnd_3074207 := by exact prefixLift 3074207
  have htrace : WordTrace (prefixWord ++ tailWord_3074207) baseStart_3074207 baseEnd_3074207 := by
    simpa [prefixWord, tailWord_3074207, baseEnd_3074207] using wordTrace_append hprefix tailTrace_3074207
  have hstable : (prefixWord ++ tailWord_3074207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074207).length < 2 ^ (prefixWord ++ tailWord_3074207).sum := by decide
  have hdescent : baseEnd_3074207 < baseStart_3074207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074233 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 3, 5]
def baseStart_3074233 : Nat := 118140960795 + 3074233 * 2 ^ 59
def prefixEnd_3074233 : Nat := 4983230072969 + 3 ^ 40 * 3074233 * 2
def baseEnd_3074233 : Nat := 1052372781942383855299577

theorem tailTrace_3074233 : CollatzResearch.WordTrace tailWord_3074233 prefixEnd_3074233 1052372781942383855299577 := by
  unfold tailWord_3074233
  simp only [CollatzResearch.WordTrace]
  refine ⟨112126489071586353041163353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74750992714390902027442235 112126489071586353041163353)
  ·
    refine ⟨84094866803689764780872515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112126489071586353041163353 84094866803689764780872515)
    ·
      refine ⟨126142300205534647171308773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84094866803689764780872515 126142300205534647171308773)
      ·
        refine ⟨23651681288537746344620395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126142300205534647171308773 23651681288537746344620395)
        ·
          refine ⟨35477521932806619516930593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23651681288537746344620395 35477521932806619516930593)
          ·
            refine ⟨26608141449604964637697945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35477521932806619516930593 26608141449604964637697945)
            ·
              refine ⟨19956106087203723478273459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26608141449604964637697945 19956106087203723478273459)
              ·
                refine ⟨29934159130805585217410189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19956106087203723478273459 29934159130805585217410189)
                ·
                  refine ⟨11225309674052094456528821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29934159130805585217410189 11225309674052094456528821)
                  ·
                    refine ⟨1052372781942383855299577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11225309674052094456528821 1052372781942383855299577)
                    ·
                      rfl

theorem cell22_3074233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_3074233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074233 prefixEnd_3074233 := by exact prefixLift 3074233
  have htrace : WordTrace (prefixWord ++ tailWord_3074233) baseStart_3074233 baseEnd_3074233 := by
    simpa [prefixWord, tailWord_3074233, baseEnd_3074233] using wordTrace_append hprefix tailTrace_3074233
  have hstable : (prefixWord ++ tailWord_3074233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074233).length < 2 ^ (prefixWord ++ tailWord_3074233).sum := by decide
  have hdescent : baseEnd_3074233 < baseStart_3074233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074250 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 4, 3]
def baseStart_3074250 : Nat := 118140960795 + 3074250 * 2 ^ 59
def prefixEnd_3074250 : Nat := 4983230072969 + 3 ^ 40 * 3074250 * 2
def baseEnd_3074250 : Nat := 1052378601389801477624525

theorem tailTrace_3074250 : CollatzResearch.WordTrace tailWord_3074250 prefixEnd_3074250 1052378601389801477624525 := by
  unfold tailWord_3074250
  simp only [CollatzResearch.WordTrace]
  refine ⟨28031777278131191236133051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74751406075016509963021469 28031777278131191236133051)
  ·
    refine ⟨42047665917196786854199577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28031777278131191236133051 42047665917196786854199577)
    ·
      refine ⟨31535749437897590140649683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42047665917196786854199577 31535749437897590140649683)
      ·
        refine ⟨47303624156846385210974525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31535749437897590140649683 47303624156846385210974525)
        ·
          refine ⟨17738859058817394454115447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47303624156846385210974525 17738859058817394454115447)
          ·
            refine ⟨26608288588226091681173171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17738859058817394454115447 26608288588226091681173171)
            ·
              refine ⟨39912432882339137521759757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26608288588226091681173171 39912432882339137521759757)
              ·
                refine ⟨14967162330877176570659909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39912432882339137521759757 14967162330877176570659909)
                ·
                  refine ⟨2806342937039470606998733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14967162330877176570659909 2806342937039470606998733)
                  ·
                    refine ⟨1052378601389801477624525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2806342937039470606998733 1052378601389801477624525)
                    ·
                      rfl

theorem cell22_3074250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_3074250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074250 prefixEnd_3074250 := by exact prefixLift 3074250
  have htrace : WordTrace (prefixWord ++ tailWord_3074250) baseStart_3074250 baseEnd_3074250 := by
    simpa [prefixWord, tailWord_3074250, baseEnd_3074250] using wordTrace_append hprefix tailTrace_3074250
  have hstable : (prefixWord ++ tailWord_3074250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074250).length < 2 ^ (prefixWord ++ tailWord_3074250).sum := by decide
  have hdescent : baseEnd_3074250 < baseStart_3074250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074325 : List Nat := [1, 3, 2, 1, 2, 1, 4, 3, 5]
def baseStart_3074325 : Nat := 118140960795 + 3074325 * 2 ^ 59
def prefixEnd_3074325 : Nat := 4983230072969 + 3 ^ 40 * 3074325 * 2
def baseEnd_3074325 : Nat := 350801425140842093999765

theorem tailTrace_3074325 : CollatzResearch.WordTrace tailWord_3074325 prefixEnd_3074325 350801425140842093999765 := by
  unfold tailWord_3074325
  simp only [CollatzResearch.WordTrace]
  refine ⟨112129844587253052753512429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74753229724835368502341619 112129844587253052753512429)
  ·
    refine ⟨42048691720219894782567161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112129844587253052753512429 42048691720219894782567161)
    ·
      refine ⟨31536518790164921086925371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42048691720219894782567161 31536518790164921086925371)
      ·
        refine ⟨47304778185247381630388057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31536518790164921086925371 47304778185247381630388057)
        ·
          refine ⟨35478583638935536222791043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47304778185247381630388057 35478583638935536222791043)
          ·
            refine ⟨53217875458403304334186565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35478583638935536222791043 53217875458403304334186565)
            ·
              refine ⟨9978351648450619562659981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53217875458403304334186565 9978351648450619562659981)
              ·
                refine ⟨3741881868168982335997493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9978351648450619562659981 3741881868168982335997493)
                ·
                  refine ⟨350801425140842093999765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3741881868168982335997493 350801425140842093999765)
                  ·
                    rfl

theorem cell22_3074325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_3074325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074325 prefixEnd_3074325 := by exact prefixLift 3074325
  have htrace : WordTrace (prefixWord ++ tailWord_3074325) baseStart_3074325 baseEnd_3074325 := by
    simpa [prefixWord, tailWord_3074325, baseEnd_3074325] using wordTrace_append hprefix tailTrace_3074325
  have hstable : (prefixWord ++ tailWord_3074325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074325).length < 2 ^ (prefixWord ++ tailWord_3074325).sum := by decide
  have hdescent : baseEnd_3074325 < baseStart_3074325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074389 : List Nat := [1, 3, 2, 2, 4, 1, 2, 2, 1, 4]
def baseStart_3074389 : Nat := 118140960795 + 3074389 * 2 ^ 59
def prefixEnd_3074389 : Nat := 4983230072969 + 3 ^ 40 * 3074389 * 2
def baseEnd_3074389 : Nat := 1052426183930451448399099

theorem tailTrace_3074389 : CollatzResearch.WordTrace tailWord_3074389 prefixEnd_3074389 1052426183930451448399099 := by
  unfold tailWord_3074389
  simp only [CollatzResearch.WordTrace]
  refine ⟨112132178859021191683842221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74754785906014127789228147 112132178859021191683842221)
  ·
    refine ⟨42049567072132946881440833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112132178859021191683842221 42049567072132946881440833)
    ·
      refine ⟨31537175304099710161080625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42049567072132946881440833 31537175304099710161080625)
      ·
        refine ⟨23652881478074782620810469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31537175304099710161080625 23652881478074782620810469)
        ·
          refine ⟨4434915277139021741401963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23652881478074782620810469 4434915277139021741401963)
          ·
            refine ⟨6652372915708532612102945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4434915277139021741401963 6652372915708532612102945)
            ·
              refine ⟨4989279686781399459077209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6652372915708532612102945 4989279686781399459077209)
              ·
                refine ⟨3741959765086049594307907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4989279686781399459077209 3741959765086049594307907)
                ·
                  refine ⟨5612939647629074391461861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3741959765086049594307907 5612939647629074391461861)
                  ·
                    refine ⟨1052426183930451448399099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5612939647629074391461861 1052426183930451448399099)
                    ·
                      rfl

theorem cell22_3074389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_3074389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074389 prefixEnd_3074389 := by exact prefixLift 3074389
  have htrace : WordTrace (prefixWord ++ tailWord_3074389) baseStart_3074389 baseEnd_3074389 := by
    simpa [prefixWord, tailWord_3074389, baseEnd_3074389] using wordTrace_append hprefix tailTrace_3074389
  have hstable : (prefixWord ++ tailWord_3074389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074389).length < 2 ^ (prefixWord ++ tailWord_3074389).sum := by decide
  have hdescent : baseEnd_3074389 < baseStart_3074389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074421 : List Nat := [1, 3, 4, 1, 2, 2, 3, 2, 4]
def baseStart_3074421 : Nat := 118140960795 + 3074421 * 2 ^ 59
def prefixEnd_3074421 : Nat := 4983230072969 + 3 ^ 40 * 3074421 * 2
def baseEnd_3074421 : Nat := 350812379394804677199667

theorem tailTrace_3074421 : CollatzResearch.WordTrace tailWord_3074421 prefixEnd_3074421 350812379394804677199667 := by
  unfold tailWord_3074421
  simp only [CollatzResearch.WordTrace]
  refine ⟨112133345994905261149007117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74755563996603507432671411 112133345994905261149007117)
  ·
    refine ⟨42050004748089472930877669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112133345994905261149007117 42050004748089472930877669)
    ·
      refine ⟨7884375890266776174539563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42050004748089472930877669 7884375890266776174539563)
      ·
        refine ⟨11826563835400164261809345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7884375890266776174539563 11826563835400164261809345)
        ·
          refine ⟨8869922876550123196357009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11826563835400164261809345 8869922876550123196357009)
          ·
            refine ⟨6652442157412592397267757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8869922876550123196357009 6652442157412592397267757)
            ·
              refine ⟨2494665809029722148975409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6652442157412592397267757 2494665809029722148975409)
              ·
                refine ⟨1870999356772291611731557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2494665809029722148975409 1870999356772291611731557)
                ·
                  refine ⟨350812379394804677199667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1870999356772291611731557 350812379394804677199667)
                  ·
                    rfl

theorem cell22_3074421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_3074421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074421 prefixEnd_3074421 := by exact prefixLift 3074421
  have htrace : WordTrace (prefixWord ++ tailWord_3074421) baseStart_3074421 baseEnd_3074421 := by
    simpa [prefixWord, tailWord_3074421, baseEnd_3074421] using wordTrace_append hprefix tailTrace_3074421
  have hstable : (prefixWord ++ tailWord_3074421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074421).length < 2 ^ (prefixWord ++ tailWord_3074421).sum := by decide
  have hdescent : baseEnd_3074421 < baseStart_3074421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074481 : List Nat := [1, 2, 2, 4, 1, 3, 1, 4, 1, 3]
def baseStart_3074481 : Nat := 118140960795 + 3074481 * 2 ^ 59
def prefixEnd_3074481 : Nat := 4983230072969 + 3 ^ 40 * 3074481 * 2
def baseEnd_3074481 : Nat := 1052457677410593875098817

theorem tailTrace_3074481 : CollatzResearch.WordTrace tailWord_3074481 prefixEnd_3074481 1052457677410593875098817 := by
  unfold tailWord_3074481
  simp only [CollatzResearch.WordTrace]
  refine ⟨112135534374687891396191297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74757022916458594264127531 112135534374687891396191297)
  ·
    refine ⟨84101650781015918547143473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112135534374687891396191297 84101650781015918547143473)
    ·
      refine ⟨63076238085761938910357605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84101650781015918547143473 63076238085761938910357605)
      ·
        refine ⟨11826794641080363545692051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63076238085761938910357605 11826794641080363545692051)
        ·
          refine ⟨17740191961620545318538077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11826794641080363545692051 17740191961620545318538077)
          ·
            refine ⟨6652571985607704494451779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17740191961620545318538077 6652571985607704494451779)
            ·
              refine ⟨9978857978411556741677669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6652571985607704494451779 9978857978411556741677669)
              ·
                refine ⟨1871035870952166889064563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9978857978411556741677669 1871035870952166889064563)
                ·
                  refine ⟨2806553806428250333596845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1871035870952166889064563 2806553806428250333596845)
                  ·
                    refine ⟨1052457677410593875098817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2806553806428250333596845 1052457677410593875098817)
                    ·
                      rfl

theorem cell22_3074481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_3074481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074481 prefixEnd_3074481 := by exact prefixLift 3074481
  have htrace : WordTrace (prefixWord ++ tailWord_3074481) baseStart_3074481 baseEnd_3074481 := by
    simpa [prefixWord, tailWord_3074481, baseEnd_3074481] using wordTrace_append hprefix tailTrace_3074481
  have hstable : (prefixWord ++ tailWord_3074481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074481).length < 2 ^ (prefixWord ++ tailWord_3074481).sum := by decide
  have hdescent : baseEnd_3074481 < baseStart_3074481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074492 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_3074492 : Nat := 118140960795 + 3074492 * 2 ^ 59
def prefixEnd_3074492 : Nat := 4983230072969 + 3 ^ 40 * 3074492 * 2
def baseEnd_3074492 : Nat := 1052461442935393513073783

theorem tailTrace_3074492 : CollatzResearch.WordTrace tailWord_3074492 prefixEnd_3074492 1052461442935393513073783 := by
  unfold tailWord_3074492
  simp only [CollatzResearch.WordTrace]
  refine ⟨56067967788824020137420865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74757290385098693516561153 56067967788824020137420865)
  ·
    refine ⟨42050975841618015103065649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56067967788824020137420865 42050975841618015103065649)
    ·
      refine ⟨31538231881213511327299237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42050975841618015103065649 31538231881213511327299237)
      ·
        refine ⟨5913418477727533373868607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31538231881213511327299237 5913418477727533373868607)
        ·
          refine ⟨8870127716591300060802911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5913418477727533373868607 8870127716591300060802911)
          ·
            refine ⟨13305191574886950091204367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8870127716591300060802911 13305191574886950091204367)
            ·
              refine ⟨19957787362330425136806551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13305191574886950091204367 19957787362330425136806551)
              ·
                refine ⟨29936681043495637705209827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19957787362330425136806551 29936681043495637705209827)
                ·
                  refine ⟨44905021565243456557814741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29936681043495637705209827 44905021565243456557814741)
                  ·
                    refine ⟨1052461442935393513073783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44905021565243456557814741 1052461442935393513073783)
                    ·
                      rfl

theorem cell22_3074492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_3074492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074492 prefixEnd_3074492 := by exact prefixLift 3074492
  have htrace : WordTrace (prefixWord ++ tailWord_3074492) baseStart_3074492 baseEnd_3074492 := by
    simpa [prefixWord, tailWord_3074492, baseEnd_3074492] using wordTrace_append hprefix tailTrace_3074492
  have hstable : (prefixWord ++ tailWord_3074492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074492).length < 2 ^ (prefixWord ++ tailWord_3074492).sum := by decide
  have hdescent : baseEnd_3074492 < baseStart_3074492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074505 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 8]
def baseStart_3074505 : Nat := 118140960795 + 3074505 * 2 ^ 59
def prefixEnd_3074505 : Nat := 4983230072969 + 3 ^ 40 * 3074505 * 2
def baseEnd_3074505 : Nat := 350821964367021937499581

theorem tailTrace_3074505 : CollatzResearch.WordTrace tailWord_3074505 prefixEnd_3074505 350821964367021937499581 := by
  unfold tailWord_3074505
  simp only [CollatzResearch.WordTrace]
  refine ⟨112136409726600943495064969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74757606484400628996709979 112136409726600943495064969)
  ·
    refine ⟨84102307294950707621298727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112136409726600943495064969 84102307294950707621298727)
    ·
      refine ⟨126153460942426061431948091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84102307294950707621298727 126153460942426061431948091)
      ·
        refine ⟨189230191413639092147922137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126153460942426061431948091 189230191413639092147922137)
        ·
          refine ⟨141922643560229319110941603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189230191413639092147922137 141922643560229319110941603)
          ·
            refine ⟨212883965340343978666412405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141922643560229319110941603 212883965340343978666412405)
            ·
              refine ⟨19957871750657247999976163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212883965340343978666412405 19957871750657247999976163)
              ·
                refine ⟨29936807625985871999964245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19957871750657247999976163 29936807625985871999964245)
                ·
                  refine ⟨350821964367021937499581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29936807625985871999964245 350821964367021937499581)
                  ·
                    rfl

theorem cell22_3074505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_3074505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074505 prefixEnd_3074505 := by exact prefixLift 3074505
  have htrace : WordTrace (prefixWord ++ tailWord_3074505) baseStart_3074505 baseEnd_3074505 := by
    simpa [prefixWord, tailWord_3074505, baseEnd_3074505] using wordTrace_append hprefix tailTrace_3074505
  have hstable : (prefixWord ++ tailWord_3074505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074505).length < 2 ^ (prefixWord ++ tailWord_3074505).sum := by decide
  have hdescent : baseEnd_3074505 < baseStart_3074505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074507 : List Nat := [1, 1, 1, 1, 3, 3, 1, 6, 1, 4]
def baseStart_3074507 : Nat := 118140960795 + 3074507 * 2 ^ 59
def prefixEnd_3074507 : Nat := 4983230072969 + 3 ^ 40 * 3074507 * 2
def baseEnd_3074507 : Nat := 1052466577741938473948737

theorem tailTrace_3074507 : CollatzResearch.WordTrace tailWord_3074507 prefixEnd_3074507 1052466577741938473948737 := by
  unfold tailWord_3074507
  simp only [CollatzResearch.WordTrace]
  refine ⟨112136482672593697836637775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74757655115062465224425183 112136482672593697836637775)
  ·
    refine ⟨168204724008890546754956663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112136482672593697836637775 168204724008890546754956663)
    ·
      refine ⟨252307086013335820132434995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168204724008890546754956663 252307086013335820132434995)
      ·
        refine ⟨378460629020003730198652493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252307086013335820132434995 378460629020003730198652493)
        ·
          refine ⟨141922735882501398824494685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 378460629020003730198652493 141922735882501398824494685)
          ·
            refine ⟨53221025955938024559185507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141922735882501398824494685 53221025955938024559185507)
            ·
              refine ⟨79831538933907036838778261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53221025955938024559185507 79831538933907036838778261)
              ·
                refine ⟨3742103387526892351817731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79831538933907036838778261 3742103387526892351817731)
                ·
                  refine ⟨5613155081290338527726597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742103387526892351817731 5613155081290338527726597)
                  ·
                    refine ⟨1052466577741938473948737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5613155081290338527726597 1052466577741938473948737)
                    ·
                      rfl

theorem cell22_3074507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 4].length) (baseStart_3074507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074507 prefixEnd_3074507 := by exact prefixLift 3074507
  have htrace : WordTrace (prefixWord ++ tailWord_3074507) baseStart_3074507 baseEnd_3074507 := by
    simpa [prefixWord, tailWord_3074507, baseEnd_3074507] using wordTrace_append hprefix tailTrace_3074507
  have hstable : (prefixWord ++ tailWord_3074507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074507).length < 2 ^ (prefixWord ++ tailWord_3074507).sum := by decide
  have hdescent : baseEnd_3074507 < baseStart_3074507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074689 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 1, 5]
def baseStart_3074689 : Nat := 118140960795 + 3074689 * 2 ^ 59
def prefixEnd_3074689 : Nat := 4983230072969 + 3 ^ 40 * 3074689 * 2
def baseEnd_3074689 : Nat := 1052528880061350665898179

theorem tailTrace_3074689 : CollatzResearch.WordTrace tailWord_3074689 prefixEnd_3074689 1052528880061350665898179 := by
  unfold tailWord_3074689
  simp only [CollatzResearch.WordTrace]
  refine ⟨112143120757934342919763121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74762080505289561946508747 112143120757934342919763121)
  ·
    refine ⟨84107340568450757189822341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112143120757934342919763121 84107340568450757189822341)
    ·
      refine ⟨15770126356584516973091689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84107340568450757189822341 15770126356584516973091689)
      ·
        refine ⟨11827594767438387729818767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15770126356584516973091689 11827594767438387729818767)
        ·
          refine ⟨17741392151157581594728151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11827594767438387729818767 17741392151157581594728151)
          ·
            refine ⟨26612088226736372392092227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17741392151157581594728151 26612088226736372392092227)
            ·
              refine ⟨39918132340104558588138341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26612088226736372392092227 39918132340104558588138341)
              ·
                refine ⟨7484649813769604735275939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39918132340104558588138341 7484649813769604735275939)
                ·
                  refine ⟨11226974720654407102913909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7484649813769604735275939 11226974720654407102913909)
                  ·
                    refine ⟨1052528880061350665898179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11226974720654407102913909 1052528880061350665898179)
                    ·
                      rfl

theorem cell22_3074689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_3074689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074689 prefixEnd_3074689 := by exact prefixLift 3074689
  have htrace : WordTrace (prefixWord ++ tailWord_3074689) baseStart_3074689 baseEnd_3074689 := by
    simpa [prefixWord, tailWord_3074689, baseEnd_3074689] using wordTrace_append hprefix tailTrace_3074689
  have hstable : (prefixWord ++ tailWord_3074689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074689).length < 2 ^ (prefixWord ++ tailWord_3074689).sum := by decide
  have hdescent : baseEnd_3074689 < baseStart_3074689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074693 : List Nat := [1, 3, 1, 1, 4, 4, 2, 1, 1, 4]
def baseStart_3074693 : Nat := 118140960795 + 3074693 * 2 ^ 59
def prefixEnd_3074693 : Nat := 4983230072969 + 3 ^ 40 * 3074693 * 2
def baseEnd_3074693 : Nat := 1052530249343095988798167

theorem tailTrace_3074693 : CollatzResearch.WordTrace tailWord_3074693 prefixEnd_3074693 1052530249343095988798167 := by
  unfold tailWord_3074693
  simp only [CollatzResearch.WordTrace]
  refine ⟨112143266649919851602908733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74762177766613234401939155 112143266649919851602908733)
  ·
    refine ⟨42053724993719944351090775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112143266649919851602908733 42053724993719944351090775)
    ·
      refine ⟨63080587490579916526636163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42053724993719944351090775 63080587490579916526636163)
      ·
        refine ⟨94620881235869874789954245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63080587490579916526636163 94620881235869874789954245)
        ·
          refine ⟨17741415231725601523116421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94620881235869874789954245 17741415231725601523116421)
          ·
            refine ⟨3326515355948550285584329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17741415231725601523116421 3326515355948550285584329)
            ·
              refine ⟨2494886516961412714188247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3326515355948550285584329 2494886516961412714188247)
              ·
                refine ⟨3742329775442119071282371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2494886516961412714188247 3742329775442119071282371)
                ·
                  refine ⟨5613494663163178606923557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742329775442119071282371 5613494663163178606923557)
                  ·
                    refine ⟨1052530249343095988798167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5613494663163178606923557 1052530249343095988798167)
                    ·
                      rfl

theorem cell22_3074693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_3074693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074693 prefixEnd_3074693 := by exact prefixLift 3074693
  have htrace : WordTrace (prefixWord ++ tailWord_3074693) baseStart_3074693 baseEnd_3074693 := by
    simpa [prefixWord, tailWord_3074693, baseEnd_3074693] using wordTrace_append hprefix tailTrace_3074693
  have hstable : (prefixWord ++ tailWord_3074693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074693).length < 2 ^ (prefixWord ++ tailWord_3074693).sum := by decide
  have hdescent : baseEnd_3074693 < baseStart_3074693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074708 : List Nat := [2, 4, 2, 2, 1, 1, 2, 4, 4]
def baseStart_3074708 : Nat := 118140960795 + 3074708 * 2 ^ 59
def prefixEnd_3074708 : Nat := 4983230072969 + 3 ^ 40 * 3074708 * 2
def baseEnd_3074708 : Nat := 350845128049880316557707

theorem tailTrace_3074708 : CollatzResearch.WordTrace tailWord_3074708 prefixEnd_3074708 350845128049880316557707 := by
  unfold tailWord_3074708
  simp only [CollatzResearch.WordTrace]
  refine ⟨56071906872432754582352389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74762542496577006109803185 56071906872432754582352389)
  ·
    refine ⟨10513482538581141484191073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56071906872432754582352389 10513482538581141484191073)
    ·
      refine ⟨7885111903935856113143305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10513482538581141484191073 7885111903935856113143305)
      ·
        refine ⟨5913833927951892084857479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7885111903935856113143305 5913833927951892084857479)
        ·
          refine ⟨8870750891927838127286219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5913833927951892084857479 8870750891927838127286219)
          ·
            refine ⟨13306126337891757190929329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8870750891927838127286219 13306126337891757190929329)
            ·
              refine ⟨9979594753418817893196997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13306126337891757190929329 9979594753418817893196997)
              ·
                refine ⟨1871174016266028354974437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9979594753418817893196997 1871174016266028354974437)
                ·
                  refine ⟨350845128049880316557707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1871174016266028354974437 350845128049880316557707)
                  ·
                    rfl

theorem cell22_3074708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_3074708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074708 prefixEnd_3074708 := by exact prefixLift 3074708
  have htrace : WordTrace (prefixWord ++ tailWord_3074708) baseStart_3074708 baseEnd_3074708 := by
    simpa [prefixWord, tailWord_3074708, baseEnd_3074708] using wordTrace_append hprefix tailTrace_3074708
  have hstable : (prefixWord ++ tailWord_3074708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074708).length < 2 ^ (prefixWord ++ tailWord_3074708).sum := by decide
  have hdescent : baseEnd_3074708 < baseStart_3074708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074742 : List Nat := [5, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_3074742 : Nat := 118140960795 + 3074742 * 2 ^ 59
def prefixEnd_3074742 : Nat := 4983230072969 + 3 ^ 40 * 3074742 * 2
def baseEnd_3074742 : Nat := 350849007681492064774339

theorem tailTrace_3074742 : CollatzResearch.WordTrace tailWord_3074742 prefixEnd_3074742 350849007681492064774339 := by
  unfold tailWord_3074742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7009065864171395810715155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74763369217828221980961653 7009065864171395810715155)
  ·
    refine ⟨10513598796257093716072733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7009065864171395810715155 10513598796257093716072733)
    ·
      refine ⟨3942599548596410143527275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10513598796257093716072733 3942599548596410143527275)
      ·
        refine ⟨5913899322894615215290913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3942599548596410143527275 5913899322894615215290913)
        ·
          refine ⟨4435424492170961411468185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5913899322894615215290913 4435424492170961411468185)
          ·
            refine ⟨3326568369128221058601139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4435424492170961411468185 3326568369128221058601139)
            ·
              refine ⟨4989852553692331587901709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3326568369128221058601139 4989852553692331587901709)
              ·
                refine ⟨1871194707634624345463141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4989852553692331587901709 1871194707634624345463141)
                ·
                  refine ⟨350849007681492064774339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1871194707634624345463141 350849007681492064774339)
                  ·
                    rfl

theorem cell22_3074742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_3074742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074742 prefixEnd_3074742 := by exact prefixLift 3074742
  have htrace : WordTrace (prefixWord ++ tailWord_3074742) baseStart_3074742 baseEnd_3074742 := by
    simpa [prefixWord, tailWord_3074742, baseEnd_3074742] using wordTrace_append hprefix tailTrace_3074742
  have hstable : (prefixWord ++ tailWord_3074742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074742).length < 2 ^ (prefixWord ++ tailWord_3074742).sum := by decide
  have hdescent : baseEnd_3074742 < baseStart_3074742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074753 : List Nat := [1, 2, 6, 2, 1, 2, 8]
def baseStart_3074753 : Nat := 118140960795 + 3074753 * 2 ^ 59
def prefixEnd_3074753 : Nat := 4983230072969 + 3 ^ 40 * 3074753 * 2
def baseEnd_3074753 : Nat := 38983362539602808603629

theorem tailTrace_3074753 : CollatzResearch.WordTrace tailWord_3074753 prefixEnd_3074753 38983362539602808603629 := by
  unfold tailWord_3074753
  simp only [CollatzResearch.WordTrace]
  refine ⟨112145455029702481850092913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74763636686468321233395275 112145455029702481850092913)
  ·
    refine ⟨84109091272276861387569685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112145455029702481850092913 84109091272276861387569685)
    ·
      refine ⟨3942613653387977877542329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84109091272276861387569685 3942613653387977877542329)
      ·
        refine ⟨2956960240040983408156747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3942613653387977877542329 2956960240040983408156747)
        ·
          refine ⟨4435440360061475112235121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956960240040983408156747 4435440360061475112235121)
          ·
            refine ⟨3326580270046106334176341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4435440360061475112235121 3326580270046106334176341)
            ·
              refine ⟨38983362539602808603629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3326580270046106334176341 38983362539602808603629)
              ·
                rfl

theorem cell22_3074753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 8].length) (baseStart_3074753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074753 prefixEnd_3074753 := by exact prefixLift 3074753
  have htrace : WordTrace (prefixWord ++ tailWord_3074753) baseStart_3074753 baseEnd_3074753 := by
    simpa [prefixWord, tailWord_3074753, baseEnd_3074753] using wordTrace_append hprefix tailTrace_3074753
  have hstable : (prefixWord ++ tailWord_3074753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074753).length < 2 ^ (prefixWord ++ tailWord_3074753).sum := by decide
  have hdescent : baseEnd_3074753 < baseStart_3074753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074856 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 1, 6]
def baseStart_3074856 : Nat := 118140960795 + 3074856 * 2 ^ 59
def prefixEnd_3074856 : Nat := 4983230072969 + 3 ^ 40 * 3074856 * 2
def baseEnd_3074856 : Nat := 1052586047574217896972667

theorem tailTrace_3074856 : CollatzResearch.WordTrace tailWord_3074856 prefixEnd_3074856 1052586047574217896972667 := by
  unfold tailWord_3074856
  simp only [CollatzResearch.WordTrace]
  refine ⟨56074605874164665220546211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74766141165552886960728281 56074605874164665220546211)
  ·
    refine ⟨84111908811246997830819317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56074605874164665220546211 84111908811246997830819317)
    ·
      refine ⟨7885491451054406046639311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84111908811246997830819317 7885491451054406046639311)
      ·
        refine ⟨11828237176581609069958967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7885491451054406046639311 11828237176581609069958967)
        ·
          refine ⟨17742355764872413604938451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11828237176581609069958967 17742355764872413604938451)
          ·
            refine ⟨26613533647308620407407677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17742355764872413604938451 26613533647308620407407677)
            ·
              refine ⟨9980075117740732652777879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26613533647308620407407677 9980075117740732652777879)
              ·
                refine ⟨14970112676611098979166819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9980075117740732652777879 14970112676611098979166819)
                ·
                  refine ⟨22455169014916648468750229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14970112676611098979166819 22455169014916648468750229)
                  ·
                    refine ⟨1052586047574217896972667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22455169014916648468750229 1052586047574217896972667)
                    ·
                      rfl

theorem cell22_3074856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_3074856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074856 prefixEnd_3074856 := by exact prefixLift 3074856
  have htrace : WordTrace (prefixWord ++ tailWord_3074856) baseStart_3074856 baseEnd_3074856 := by
    simpa [prefixWord, tailWord_3074856, baseEnd_3074856] using wordTrace_append hprefix tailTrace_3074856
  have hstable : (prefixWord ++ tailWord_3074856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074856).length < 2 ^ (prefixWord ++ tailWord_3074856).sum := by decide
  have hdescent : baseEnd_3074856 < baseStart_3074856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074862 : List Nat := [4, 1, 3, 2, 1, 3, 2, 1, 1, 4]
def baseStart_3074862 : Nat := 118140960795 + 3074862 * 2 ^ 59
def prefixEnd_3074862 : Nat := 4983230072969 + 3 ^ 40 * 3074862 * 2
def baseEnd_3074862 : Nat := 1052588101496835881322649

theorem tailTrace_3074862 : CollatzResearch.WordTrace tailWord_3074862 prefixEnd_3074862 1052588101496835881322649 := by
  unfold tailWord_3074862
  simp only [CollatzResearch.WordTrace]
  refine ⟨14018678823288449183226355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74766287057538395643873893 14018678823288449183226355)
  ·
    refine ⟨21028018234932673774839533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14018678823288449183226355 21028018234932673774839533)
    ·
      refine ⟨7885506838099752665564825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21028018234932673774839533 7885506838099752665564825)
      ·
        refine ⟨5914130128574814499173619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7885506838099752665564825 5914130128574814499173619)
        ·
          refine ⟨8871195192862221748760429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5914130128574814499173619 8871195192862221748760429)
          ·
            refine ⟨3326698197323333155785161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8871195192862221748760429 3326698197323333155785161)
            ·
              refine ⟨2495023647992499866838871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3326698197323333155785161 2495023647992499866838871)
              ·
                refine ⟨3742535471988749800258307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495023647992499866838871 3742535471988749800258307)
                ·
                  refine ⟨5613803207983124700387461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742535471988749800258307 5613803207983124700387461)
                  ·
                    refine ⟨1052588101496835881322649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5613803207983124700387461 1052588101496835881322649)
                    ·
                      rfl

theorem cell22_3074862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_3074862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074862 prefixEnd_3074862 := by exact prefixLift 3074862
  have htrace : WordTrace (prefixWord ++ tailWord_3074862) baseStart_3074862 baseEnd_3074862 := by
    simpa [prefixWord, tailWord_3074862, baseEnd_3074862] using wordTrace_append hprefix tailTrace_3074862
  have hstable : (prefixWord ++ tailWord_3074862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074862).length < 2 ^ (prefixWord ++ tailWord_3074862).sum := by decide
  have hdescent : baseEnd_3074862 < baseStart_3074862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074903 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 3, 3]
def baseStart_3074903 : Nat := 118140960795 + 3074903 * 2 ^ 59
def prefixEnd_3074903 : Nat := 4983230072969 + 3 ^ 40 * 3074903 * 2
def baseEnd_3074903 : Nat := 1052602136634725441047523

theorem tailTrace_3074903 : CollatzResearch.WordTrace tailWord_3074903 prefixEnd_3074903 1052602136634725441047523 := by
  unfold tailWord_3074903
  simp only [CollatzResearch.WordTrace]
  refine ⟨112150925979159057468053363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74767283986106038312035575 112150925979159057468053363)
  ·
    refine ⟨168226388968738586202080045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112150925979159057468053363 168226388968738586202080045)
    ·
      refine ⟨63084895863276969825780017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168226388968738586202080045 63084895863276969825780017)
      ·
        refine ⟨47313671897457727369335013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63084895863276969825780017 47313671897457727369335013)
        ·
          refine ⟨8871313480773323881750315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47313671897457727369335013 8871313480773323881750315)
          ·
            refine ⟨13306970221159985822625473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8871313480773323881750315 13306970221159985822625473)
            ·
              refine ⟨9980227665869989366969105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13306970221159985822625473 9980227665869989366969105)
              ·
                refine ⟨7485170749402492025226829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9980227665869989366969105 7485170749402492025226829)
                ·
                  refine ⟨2806939031025934509460061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7485170749402492025226829 2806939031025934509460061)
                  ·
                    refine ⟨1052602136634725441047523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2806939031025934509460061 1052602136634725441047523)
                    ·
                      rfl

theorem cell22_3074903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_3074903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074903 prefixEnd_3074903 := by exact prefixLift 3074903
  have htrace : WordTrace (prefixWord ++ tailWord_3074903) baseStart_3074903 baseEnd_3074903 := by
    simpa [prefixWord, tailWord_3074903, baseEnd_3074903] using wordTrace_append hprefix tailTrace_3074903
  have hstable : (prefixWord ++ tailWord_3074903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074903).length < 2 ^ (prefixWord ++ tailWord_3074903).sum := by decide
  have hdescent : baseEnd_3074903 < baseStart_3074903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074916 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 7]
def baseStart_3074916 : Nat := 118140960795 + 3074916 * 2 ^ 59
def prefixEnd_3074916 : Nat := 4983230072969 + 3 ^ 40 * 3074916 * 2
def baseEnd_3074916 : Nat := 350868862266799246824161

theorem tailTrace_3074916 : CollatzResearch.WordTrace tailWord_3074916 prefixEnd_3074916 350868862266799246824161 := by
  unfold tailWord_3074916
  simp only [CollatzResearch.WordTrace]
  refine ⟨56075700064055980344138301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74767600085407973792184401 56075700064055980344138301)
  ·
    refine ⟨21028387524020992629051863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56075700064055980344138301 21028387524020992629051863)
    ·
      refine ⟨31542581286031488943577795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21028387524020992629051863 31542581286031488943577795)
      ·
        refine ⟨47313871929047233415366693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31542581286031488943577795 47313871929047233415366693)
        ·
          refine ⟨8871350986696356265381255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47313871929047233415366693 8871350986696356265381255)
          ·
            refine ⟨13307026480044534398071883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8871350986696356265381255 13307026480044534398071883)
            ·
              refine ⟨19960539720066801597107825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13307026480044534398071883 19960539720066801597107825)
              ·
                refine ⟨14970404790050101197830869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19960539720066801597107825 14970404790050101197830869)
                ·
                  refine ⟨350868862266799246824161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14970404790050101197830869 350868862266799246824161)
                  ·
                    rfl

theorem cell22_3074916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_3074916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074916 prefixEnd_3074916 := by exact prefixLift 3074916
  have htrace : WordTrace (prefixWord ++ tailWord_3074916) baseStart_3074916 baseEnd_3074916 := by
    simpa [prefixWord, tailWord_3074916, baseEnd_3074916] using wordTrace_append hprefix tailTrace_3074916
  have hstable : (prefixWord ++ tailWord_3074916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074916).length < 2 ^ (prefixWord ++ tailWord_3074916).sum := by decide
  have hdescent : baseEnd_3074916 < baseStart_3074916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074937 : List Nat := [1, 2, 1, 3, 2, 4, 3, 2, 1, 3]
def baseStart_3074937 : Nat := 118140960795 + 3074937 * 2 ^ 59
def prefixEnd_3074937 : Nat := 4983230072969 + 3 ^ 40 * 3074937 * 2
def baseEnd_3074937 : Nat := 1052613775529560685697419

theorem tailTrace_3074937 : CollatzResearch.WordTrace tailWord_3074937 prefixEnd_3074937 1052613775529560685697419 := by
  unfold tailWord_3074937
  simp only [CollatzResearch.WordTrace]
  refine ⟨112152166061035881274791065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74768110707357254183194043 112152166061035881274791065)
  ·
    refine ⟨84114124545776910956093299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112152166061035881274791065 84114124545776910956093299)
    ·
      refine ⟨126171186818665366434139949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84114124545776910956093299 126171186818665366434139949)
      ·
        refine ⟨47314195056999512412802481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126171186818665366434139949 47314195056999512412802481)
        ·
          refine ⟨35485646292749634309601861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47314195056999512412802481 35485646292749634309601861)
          ·
            refine ⟨6653558679890556433050349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35485646292749634309601861 6653558679890556433050349)
            ·
              refine ⟨2495084504958958662393881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6653558679890556433050349 2495084504958958662393881)
              ·
                refine ⟨1871313378719218996795411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2495084504958958662393881 1871313378719218996795411)
                ·
                  refine ⟨2806970068078828495193117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1871313378719218996795411 2806970068078828495193117)
                  ·
                    refine ⟨1052613775529560685697419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2806970068078828495193117 1052613775529560685697419)
                    ·
                      rfl

theorem cell22_3074937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 1, 3].length) (baseStart_3074937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074937 prefixEnd_3074937 := by exact prefixLift 3074937
  have htrace : WordTrace (prefixWord ++ tailWord_3074937) baseStart_3074937 baseEnd_3074937 := by
    simpa [prefixWord, tailWord_3074937, baseEnd_3074937] using wordTrace_append hprefix tailTrace_3074937
  have hstable : (prefixWord ++ tailWord_3074937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074937).length < 2 ^ (prefixWord ++ tailWord_3074937).sum := by decide
  have hdescent : baseEnd_3074937 < baseStart_3074937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074976 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 3, 5]
def baseStart_3074976 : Nat := 118140960795 + 3074976 * 2 ^ 59
def prefixEnd_3074976 : Nat := 4983230072969 + 3 ^ 40 * 3074976 * 2
def baseEnd_3074976 : Nat := 1052627126026577583972299

theorem tailTrace_3074976 : CollatzResearch.WordTrace tailWord_3074976 prefixEnd_3074976 1052627126026577583972299 := by
  unfold tailWord_3074976
  simp only [CollatzResearch.WordTrace]
  refine ⟨56076794253947295467730391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74769059005263060623640521 56076794253947295467730391)
  ·
    refine ⟨84115191380920943201595587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56076794253947295467730391 84115191380920943201595587)
    ·
      refine ⟨126172787071381414802393381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84115191380920943201595587 126172787071381414802393381)
      ·
        refine ⟨23657397575884015275448759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126172787071381414802393381 23657397575884015275448759)
        ·
          refine ⟨35486096363826022913173139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23657397575884015275448759 35486096363826022913173139)
          ·
            refine ⟨53229144545739034369759709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35486096363826022913173139 53229144545739034369759709)
            ·
              refine ⟨19960929204652137888659891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53229144545739034369759709 19960929204652137888659891)
              ·
                refine ⟨29941393806978206832989837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19960929204652137888659891 29941393806978206832989837)
                ·
                  refine ⟨11228022677616827562371189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29941393806978206832989837 11228022677616827562371189)
                  ·
                    refine ⟨1052627126026577583972299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11228022677616827562371189 1052627126026577583972299)
                    ·
                      rfl

theorem cell22_3074976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_3074976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074976 prefixEnd_3074976 := by exact prefixLift 3074976
  have htrace : WordTrace (prefixWord ++ tailWord_3074976) baseStart_3074976 baseEnd_3074976 := by
    simpa [prefixWord, tailWord_3074976, baseEnd_3074976] using wordTrace_append hprefix tailTrace_3074976
  have hstable : (prefixWord ++ tailWord_3074976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074976).length < 2 ^ (prefixWord ++ tailWord_3074976).sum := by decide
  have hdescent : baseEnd_3074976 < baseStart_3074976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074980 : List Nat := [2, 3, 1, 2, 1, 2, 5, 1, 1, 4]
def baseStart_3074980 : Nat := 118140960795 + 3074980 * 2 ^ 59
def prefixEnd_3074980 : Nat := 4983230072969 + 3 ^ 40 * 3074980 * 2
def baseEnd_3074980 : Nat := 1052628495308322906872287

theorem tailTrace_3074980 : CollatzResearch.WordTrace tailWord_3074980 prefixEnd_3074980 1052628495308322906872287 := by
  unfold tailWord_3074980
  simp only [CollatzResearch.WordTrace]
  refine ⟨56076867199940049809303197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74769156266586733079070929 56076867199940049809303197)
  ·
    refine ⟨21028825199977518678488699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56076867199940049809303197 21028825199977518678488699)
    ·
      refine ⟨31543237799966278017733049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21028825199977518678488699 31543237799966278017733049)
      ·
        refine ⟨23657428349974708513299787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31543237799966278017733049 23657428349974708513299787)
        ·
          refine ⟨35486142524962062769949681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23657428349974708513299787 35486142524962062769949681)
          ·
            refine ⟨26614606893721547077462261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35486142524962062769949681 26614606893721547077462261)
            ·
              refine ⟨2495119396286395038512087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26614606893721547077462261 2495119396286395038512087)
              ·
                refine ⟨3742679094429592557768131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495119396286395038512087 3742679094429592557768131)
                ·
                  refine ⟨5614018641644388836652197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742679094429592557768131 5614018641644388836652197)
                  ·
                    refine ⟨1052628495308322906872287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5614018641644388836652197 1052628495308322906872287)
                    ·
                      rfl

theorem cell22_3074980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_3074980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074980 prefixEnd_3074980 := by exact prefixLift 3074980
  have htrace : WordTrace (prefixWord ++ tailWord_3074980) baseStart_3074980 baseEnd_3074980 := by
    simpa [prefixWord, tailWord_3074980, baseEnd_3074980] using wordTrace_append hprefix tailTrace_3074980
  have hstable : (prefixWord ++ tailWord_3074980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074980).length < 2 ^ (prefixWord ++ tailWord_3074980).sum := by decide
  have hdescent : baseEnd_3074980 < baseStart_3074980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074991 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 4, 4]
def baseStart_3074991 : Nat := 118140960795 + 3074991 * 2 ^ 59
def prefixEnd_3074991 : Nat := 4983230072969 + 3 ^ 40 * 3074991 * 2
def baseEnd_3074991 : Nat := 1052632260833122544847253

theorem tailTrace_3074991 : CollatzResearch.WordTrace tailWord_3074991 prefixEnd_3074991 1052632260833122544847253 := by
  unfold tailWord_3074991
  simp only [CollatzResearch.WordTrace]
  refine ⟨112154135602840248497256827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74769423735226832331504551 112154135602840248497256827)
  ·
    refine ⟨168231203404260372745885241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112154135602840248497256827 168231203404260372745885241)
    ·
      refine ⟨126173402553195279559413931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168231203404260372745885241 126173402553195279559413931)
      ·
        refine ⟨189260103829792919339120897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126173402553195279559413931 189260103829792919339120897)
        ·
          refine ⟨141945077872344689504340673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189260103829792919339120897 141945077872344689504340673)
          ·
            refine ⟨106458808404258517128255505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141945077872344689504340673 106458808404258517128255505)
            ·
              refine ⟨79844106303193887846191629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106458808404258517128255505 79844106303193887846191629)
              ·
                refine ⟨29941539863697707942321861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79844106303193887846191629 29941539863697707942321861)
                ·
                  refine ⟨5614038724443320239185349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29941539863697707942321861 5614038724443320239185349)
                  ·
                    refine ⟨1052632260833122544847253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5614038724443320239185349 1052632260833122544847253)
                    ·
                      rfl

theorem cell22_3074991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_3074991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3074991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3074991 prefixEnd_3074991 := by exact prefixLift 3074991
  have htrace : WordTrace (prefixWord ++ tailWord_3074991) baseStart_3074991 baseEnd_3074991 := by
    simpa [prefixWord, tailWord_3074991, baseEnd_3074991] using wordTrace_append hprefix tailTrace_3074991
  have hstable : (prefixWord ++ tailWord_3074991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074991).length < 2 ^ (prefixWord ++ tailWord_3074991).sum := by decide
  have hdescent : baseEnd_3074991 < baseStart_3074991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075023 : List Nat := [1, 1, 2, 1, 1, 7, 3, 6]
def baseStart_3075023 : Nat := 118140960795 + 3075023 * 2 ^ 59
def prefixEnd_3075023 : Nat := 4983230072969 + 3 ^ 40 * 3075023 * 2
def baseEnd_3075023 : Nat := 116960357231898347560795

theorem tailTrace_3075023 : CollatzResearch.WordTrace tailWord_3075023 prefixEnd_3075023 116960357231898347560795 := by
  unfold tailWord_3075023
  simp only [CollatzResearch.WordTrace]
  refine ⟨112155302738724317962421723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74770201825816211974947815 112155302738724317962421723)
  ·
    refine ⟨168232954108086476943632585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112155302738724317962421723 168232954108086476943632585)
    ·
      refine ⟨126174715581064857707724439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168232954108086476943632585 126174715581064857707724439)
      ·
        refine ⟨189262073371597286561586659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126174715581064857707724439 189262073371597286561586659)
        ·
          refine ⟨283893110057395929842379989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189262073371597286561586659 283893110057395929842379989)
          ·
            refine ⟨6653744766970217105680781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 283893110057395929842379989 6653744766970217105680781)
            ·
              refine ⟨2495154287613831414630293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6653744766970217105680781 2495154287613831414630293)
              ·
                refine ⟨116960357231898347560795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2495154287613831414630293 116960357231898347560795)
                ·
                  rfl

theorem cell22_3075023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 6].length) (baseStart_3075023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075023 prefixEnd_3075023 := by exact prefixLift 3075023
  have htrace : WordTrace (prefixWord ++ tailWord_3075023) baseStart_3075023 baseEnd_3075023 := by
    simpa [prefixWord, tailWord_3075023, baseEnd_3075023] using wordTrace_append hprefix tailTrace_3075023
  have hstable : (prefixWord ++ tailWord_3075023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075023).length < 2 ^ (prefixWord ++ tailWord_3075023).sum := by decide
  have hdescent : baseEnd_3075023 < baseStart_3075023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075055 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 3, 3]
def baseStart_3075055 : Nat := 118140960795 + 3075055 * 2 ^ 59
def prefixEnd_3075055 : Nat := 4983230072969 + 3 ^ 40 * 3075055 * 2
def baseEnd_3075055 : Nat := 1052654169341047711247057

theorem tailTrace_3075055 : CollatzResearch.WordTrace tailWord_3075055 prefixEnd_3075055 1052654169341047711247057 := by
  unfold tailWord_3075055
  simp only [CollatzResearch.WordTrace]
  refine ⟨112156469874608387427586619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74770979916405591618391079 112156469874608387427586619)
  ·
    refine ⟨168234704811912581141379929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112156469874608387427586619 168234704811912581141379929)
    ·
      refine ⟨126176028608934435856034947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168234704811912581141379929 126176028608934435856034947)
      ·
        refine ⟨189264042913401653784052421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126176028608934435856034947 189264042913401653784052421)
        ·
          refine ⟨35487008046262810084509829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189264042913401653784052421 35487008046262810084509829)
          ·
            refine ⟨6653814008674276890845593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35487008046262810084509829 6653814008674276890845593)
            ·
              refine ⟨4990360506505707668134195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6653814008674276890845593 4990360506505707668134195)
              ·
                refine ⟨7485540759758561502201293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4990360506505707668134195 7485540759758561502201293)
                ·
                  refine ⟨2807077784909460563325485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7485540759758561502201293 2807077784909460563325485)
                  ·
                    refine ⟨1052654169341047711247057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2807077784909460563325485 1052654169341047711247057)
                    ·
                      rfl

theorem cell22_3075055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 3].length) (baseStart_3075055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075055 prefixEnd_3075055 := by exact prefixLift 3075055
  have htrace : WordTrace (prefixWord ++ tailWord_3075055) baseStart_3075055 baseEnd_3075055 := by
    simpa [prefixWord, tailWord_3075055, baseEnd_3075055] using wordTrace_append hprefix tailTrace_3075055
  have hstable : (prefixWord ++ tailWord_3075055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075055).length < 2 ^ (prefixWord ++ tailWord_3075055).sum := by decide
  have hdescent : baseEnd_3075055 < baseStart_3075055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075061 : List Nat := [1, 3, 5, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3075061 : Nat := 118140960795 + 3075061 * 2 ^ 59
def prefixEnd_3075061 : Nat := 4983230072969 + 3 ^ 40 * 3075061 * 2
def baseEnd_3075061 : Nat := 1052656223263665695597039

theorem tailTrace_3075061 : CollatzResearch.WordTrace tailWord_3075061 prefixEnd_3075061 1052656223263665695597039 := by
  unfold tailWord_3075061
  simp only [CollatzResearch.WordTrace]
  refine ⟨112156688712586650452305037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74771125808391100301536691 112156688712586650452305037)
  ·
    refine ⟨42058758267219993919614389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112156688712586650452305037 42058758267219993919614389)
    ·
      refine ⟨3943008587551874429963849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42058758267219993919614389 3943008587551874429963849)
      ·
        refine ⟨2957256440663905822472887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3943008587551874429963849 2957256440663905822472887)
        ·
          refine ⟨4435884660995858733709331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2957256440663905822472887 4435884660995858733709331)
          ·
            refine ⟨6653826991493788100563997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4435884660995858733709331 6653826991493788100563997)
            ·
              refine ⟨2495185121810170537711499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6653826991493788100563997 2495185121810170537711499)
              ·
                refine ⟨3742777682715255806567249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495185121810170537711499 3742777682715255806567249)
                ·
                  refine ⟨2807083262036441854925437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3742777682715255806567249 2807083262036441854925437)
                  ·
                    refine ⟨1052656223263665695597039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2807083262036441854925437 1052656223263665695597039)
                    ·
                      rfl

theorem cell22_3075061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3075061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075061 prefixEnd_3075061 := by exact prefixLift 3075061
  have htrace : WordTrace (prefixWord ++ tailWord_3075061) baseStart_3075061 baseEnd_3075061 := by
    simpa [prefixWord, tailWord_3075061, baseEnd_3075061] using wordTrace_append hprefix tailTrace_3075061
  have hstable : (prefixWord ++ tailWord_3075061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075061).length < 2 ^ (prefixWord ++ tailWord_3075061).sum := by decide
  have hdescent : baseEnd_3075061 < baseStart_3075061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075074 : List Nat := [3, 4, 1, 3, 1, 2, 2, 6]
def baseStart_3075074 : Nat := 118140960795 + 3075074 * 2 ^ 59
def prefixEnd_3075074 : Nat := 4983230072969 + 3 ^ 40 * 3075074 * 2
def baseEnd_3075074 : Nat := 116962297047704221669111

theorem tailTrace_3075074 : CollatzResearch.WordTrace tailWord_3075074 prefixEnd_3075074 116962297047704221669111 := by
  unfold tailWord_3075074
  simp only [CollatzResearch.WordTrace]
  refine ⟨28039290715384888418132069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74771441907693035781685517 28039290715384888418132069)
  ·
    refine ⟨5257367009134666578399763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28039290715384888418132069 5257367009134666578399763)
    ·
      refine ⟨7886050513701999867599645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5257367009134666578399763 7886050513701999867599645)
      ·
        refine ⟨2957268942638249950349867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7886050513701999867599645 2957268942638249950349867)
        ·
          refine ⟨4435903413957374925524801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2957268942638249950349867 4435903413957374925524801)
          ·
            refine ⟨3326927560468031194143601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4435903413957374925524801 3326927560468031194143601)
            ·
              refine ⟨2495195670351023395607701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3326927560468031194143601 2495195670351023395607701)
              ·
                refine ⟨116962297047704221669111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2495195670351023395607701 116962297047704221669111)
                ·
                  rfl

theorem cell22_3075074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 6].length) (baseStart_3075074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075074 prefixEnd_3075074 := by exact prefixLift 3075074
  have htrace : WordTrace (prefixWord ++ tailWord_3075074) baseStart_3075074 baseEnd_3075074 := by
    simpa [prefixWord, tailWord_3075074, baseEnd_3075074] using wordTrace_append hprefix tailTrace_3075074
  have hstable : (prefixWord ++ tailWord_3075074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075074).length < 2 ^ (prefixWord ++ tailWord_3075074).sum := by decide
  have hdescent : baseEnd_3075074 < baseStart_3075074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075081 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 2, 8]
def baseStart_3075081 : Nat := 118140960795 + 3075081 * 2 ^ 59
def prefixEnd_3075081 : Nat := 4983230072969 + 3 ^ 40 * 3075081 * 2
def baseEnd_3075081 : Nat := 1052663069672392310096977

theorem tailTrace_3075081 : CollatzResearch.WordTrace tailWord_3075081 prefixEnd_3075081 1052663069672392310096977 := by
  unfold tailWord_3075081
  simp only [CollatzResearch.WordTrace]
  refine ⟨112157418172514193868033097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74771612115009462578688731 112157418172514193868033097)
  ·
    refine ⟨84118063629385645401024823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112157418172514193868033097 84118063629385645401024823)
    ·
      refine ⟨126177095444078468101537235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84118063629385645401024823 126177095444078468101537235)
      ·
        refine ⟨189265643166117702152305853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126177095444078468101537235 189265643166117702152305853)
        ·
          refine ⟨70974616187294138307114695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189265643166117702152305853 70974616187294138307114695)
          ·
            refine ⟨106461924280941207460672043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70974616187294138307114695 106461924280941207460672043)
            ·
              refine ⟨159692886421411811191008065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106461924280941207460672043 159692886421411811191008065)
              ·
                refine ⟨119769664816058858393256049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159692886421411811191008065 119769664816058858393256049)
                ·
                  refine ⟨89827248612044143794942037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119769664816058858393256049 89827248612044143794942037)
                  ·
                    refine ⟨1052663069672392310096977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89827248612044143794942037 1052663069672392310096977)
                    ·
                      rfl

theorem cell22_3075081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_3075081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075081 prefixEnd_3075081 := by exact prefixLift 3075081
  have htrace : WordTrace (prefixWord ++ tailWord_3075081) baseStart_3075081 baseEnd_3075081 := by
    simpa [prefixWord, tailWord_3075081, baseEnd_3075081] using wordTrace_append hprefix tailTrace_3075081
  have hstable : (prefixWord ++ tailWord_3075081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075081).length < 2 ^ (prefixWord ++ tailWord_3075081).sum := by decide
  have hdescent : baseEnd_3075081 < baseStart_3075081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075132 : List Nat := [2, 2, 2, 2, 2, 4, 1, 2, 1, 4]
def baseStart_3075132 : Nat := 118140960795 + 3075132 * 2 ^ 59
def prefixEnd_3075132 : Nat := 4983230072969 + 3 ^ 40 * 3075132 * 2
def baseEnd_3075132 : Nat := 1052680528014645177071821

theorem tailTrace_3075132 : CollatzResearch.WordTrace tailWord_3075132 prefixEnd_3075132 1052680528014645177071821 := by
  unfold tailWord_3075132
  simp only [CollatzResearch.WordTrace]
  refine ⟨56079639147664714789069825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74772852196886286385426433 56079639147664714789069825)
  ·
    refine ⟨42059729360748536091802369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56079639147664714789069825 42059729360748536091802369)
    ·
      refine ⟨31544797020561402068851777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42059729360748536091802369 31544797020561402068851777)
      ·
        refine ⟨23658597765421051551638833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31544797020561402068851777 23658597765421051551638833)
        ·
          refine ⟨17743948324065788663729125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23658597765421051551638833 17743948324065788663729125)
          ·
            refine ⟨3326990310762335374449211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17743948324065788663729125 3326990310762335374449211)
            ·
              refine ⟨4990485466143503061673817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3326990310762335374449211 4990485466143503061673817)
              ·
                refine ⟨3742864099607627296255363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4990485466143503061673817 3742864099607627296255363)
                ·
                  refine ⟨5614296149411440944383045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742864099607627296255363 5614296149411440944383045)
                  ·
                    refine ⟨1052680528014645177071821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5614296149411440944383045 1052680528014645177071821)
                    ·
                      rfl

theorem cell22_3075132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_3075132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075132 prefixEnd_3075132 := by exact prefixLift 3075132
  have htrace : WordTrace (prefixWord ++ tailWord_3075132) baseStart_3075132 baseEnd_3075132 := by
    simpa [prefixWord, tailWord_3075132, baseEnd_3075132] using wordTrace_append hprefix tailTrace_3075132
  have hstable : (prefixWord ++ tailWord_3075132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075132).length < 2 ^ (prefixWord ++ tailWord_3075132).sum := by decide
  have hdescent : baseEnd_3075132 < baseStart_3075132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075149 : List Nat := [1, 6, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3075149 : Nat := 118140960795 + 3075149 * 2 ^ 59
def prefixEnd_3075149 : Nat := 4983230072969 + 3 ^ 40 * 3075149 * 2
def baseEnd_3075149 : Nat := 1052686347462062799396769

theorem tailTrace_3075149 : CollatzResearch.WordTrace tailWord_3075149 prefixEnd_3075149 1052686347462062799396769 := by
  unfold tailWord_3075149
  simp only [CollatzResearch.WordTrace]
  refine ⟨112159898336267841481508501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74773265557511894321005667 112159898336267841481508501)
  ·
    refine ⟨5257495234512555069445711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 112159898336267841481508501 5257495234512555069445711)
    ·
      refine ⟨7886242851768832604168567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5257495234512555069445711 7886242851768832604168567)
      ·
        refine ⟨11829364277653248906252851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7886242851768832604168567 11829364277653248906252851)
        ·
          refine ⟨17744046416479873359379277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11829364277653248906252851 17744046416479873359379277)
          ·
            refine ⟨6654017406179952509767229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17744046416479873359379277 6654017406179952509767229)
            ·
              refine ⟨2495256527317482191162711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6654017406179952509767229 2495256527317482191162711)
              ·
                refine ⟨3742884790976223286744067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495256527317482191162711 3742884790976223286744067)
                ·
                  refine ⟨5614327186464334930116101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742884790976223286744067 5614327186464334930116101)
                  ·
                    refine ⟨1052686347462062799396769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5614327186464334930116101 1052686347462062799396769)
                    ·
                      rfl

theorem cell22_3075149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3075149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075149 prefixEnd_3075149 := by exact prefixLift 3075149
  have htrace : WordTrace (prefixWord ++ tailWord_3075149) baseStart_3075149 baseEnd_3075149 := by
    simpa [prefixWord, tailWord_3075149, baseEnd_3075149] using wordTrace_append hprefix tailTrace_3075149
  have hstable : (prefixWord ++ tailWord_3075149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075149).length < 2 ^ (prefixWord ++ tailWord_3075149).sum := by decide
  have hdescent : baseEnd_3075149 < baseStart_3075149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075175 : List Nat := [1, 1, 5, 1, 1, 5, 1, 7]
def baseStart_3075175 : Nat := 118140960795 + 3075175 * 2 ^ 59
def prefixEnd_3075175 : Nat := 4983230072969 + 3 ^ 40 * 3075175 * 2
def baseEnd_3075175 : Nat := 116966138643711933138521

theorem tailTrace_3075175 : CollatzResearch.WordTrace tailWord_3075175 prefixEnd_3075175 116966138643711933138521 := by
  unfold tailWord_3075175
  simp only [CollatzResearch.WordTrace]
  refine ⟨112160846634173647921954979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74773897756115765281303319 112160846634173647921954979)
  ·
    refine ⟨168241269951260471882932469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112160846634173647921954979 168241269951260471882932469)
    ·
      refine ⟨15772619057930669239024919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168241269951260471882932469 15772619057930669239024919)
      ·
        refine ⟨23658928586896003858537379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15772619057930669239024919 23658928586896003858537379)
        ·
          refine ⟨35488392880344005787806069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23658928586896003858537379 35488392880344005787806069)
          ·
            refine ⟨3327036832532250542606819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35488392880344005787806069 3327036832532250542606819)
            ·
              refine ⟨4990555248798375813910229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327036832532250542606819 4990555248798375813910229)
              ·
                refine ⟨116966138643711933138521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4990555248798375813910229 116966138643711933138521)
                ·
                  rfl

theorem cell22_3075175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 7].length) (baseStart_3075175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075175 prefixEnd_3075175 := by exact prefixLift 3075175
  have htrace : WordTrace (prefixWord ++ tailWord_3075175) baseStart_3075175 baseEnd_3075175 := by
    simpa [prefixWord, tailWord_3075175, baseEnd_3075175] using wordTrace_append hprefix tailTrace_3075175
  have hstable : (prefixWord ++ tailWord_3075175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075175).length < 2 ^ (prefixWord ++ tailWord_3075175).sum := by decide
  have hdescent : baseEnd_3075175 < baseStart_3075175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075198 : List Nat := [4, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_3075198 : Nat := 118140960795 + 3075198 * 2 ^ 59
def prefixEnd_3075198 : Nat := 4983230072969 + 3 ^ 40 * 3075198 * 2
def baseEnd_3075198 : Nat := 350901040387814334973873

theorem tailTrace_3075198 : CollatzResearch.WordTrace tailWord_3075198 prefixEnd_3075198 350901040387814334973873 := by
  unfold tailWord_3075198
  simp only [CollatzResearch.WordTrace]
  refine ⟨14020210689136290356255281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74774457008726881900028165 14020210689136290356255281)
  ·
    refine ⟨10515158016852217767191461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14020210689136290356255281 10515158016852217767191461)
    ·
      refine ⟨1971592128159790831348399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10515158016852217767191461 1971592128159790831348399)
      ·
        refine ⟨2957388192239686247022599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1971592128159790831348399 2957388192239686247022599)
        ·
          refine ⟨4436082288359529370533899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2957388192239686247022599 4436082288359529370533899)
          ·
            refine ⟨6654123432539294055800849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4436082288359529370533899 6654123432539294055800849)
            ·
              refine ⟨4990592574404470541850637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6654123432539294055800849 4990592574404470541850637)
              ·
                refine ⟨1871472215401676453193989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4990592574404470541850637 1871472215401676453193989)
                ·
                  refine ⟨350901040387814334973873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1871472215401676453193989 350901040387814334973873)
                  ·
                    rfl

theorem cell22_3075198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_3075198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075198 prefixEnd_3075198 := by exact prefixLift 3075198
  have htrace : WordTrace (prefixWord ++ tailWord_3075198) baseStart_3075198 baseEnd_3075198 := by
    simpa [prefixWord, tailWord_3075198, baseEnd_3075198] using wordTrace_append hprefix tailTrace_3075198
  have hstable : (prefixWord ++ tailWord_3075198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075198).length < 2 ^ (prefixWord ++ tailWord_3075198).sum := by decide
  have hdescent : baseEnd_3075198 < baseStart_3075198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075203 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 7]
def baseStart_3075203 : Nat := 118140960795 + 3075203 * 2 ^ 59
def prefixEnd_3075203 : Nat := 4983230072969 + 3 ^ 40 * 3075203 * 2
def baseEnd_3075203 : Nat := 350901610921874886182201

theorem tailTrace_3075203 : CollatzResearch.WordTrace tailWord_3075203 prefixEnd_3075203 350901610921874886182201 := by
  unfold tailWord_3075203
  simp only [CollatzResearch.WordTrace]
  refine ⟨112161867878072208703974263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74774578585381472469316175 112161867878072208703974263)
  ·
    refine ⟨168242801817108313055961395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112161867878072208703974263 168242801817108313055961395)
    ·
      refine ⟨252364202725662469583942093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168242801817108313055961395 252364202725662469583942093)
      ·
        refine ⟨94636576022123426093978285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252364202725662469583942093 94636576022123426093978285)
        ·
          refine ⟨35488716008296284785241857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94636576022123426093978285 35488716008296284785241857)
          ·
            refine ⟨26616537006222213588931393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35488716008296284785241857 26616537006222213588931393)
            ·
              refine ⟨19962402754666660191698545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26616537006222213588931393 19962402754666660191698545)
              ·
                refine ⟨14971802065999995143773909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19962402754666660191698545 14971802065999995143773909)
                ·
                  refine ⟨350901610921874886182201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14971802065999995143773909 350901610921874886182201)
                  ·
                    rfl

theorem cell22_3075203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 7].length) (baseStart_3075203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075203 prefixEnd_3075203 := by exact prefixLift 3075203
  have htrace : WordTrace (prefixWord ++ tailWord_3075203) baseStart_3075203 baseEnd_3075203 := by
    simpa [prefixWord, tailWord_3075203, baseEnd_3075203] using wordTrace_append hprefix tailTrace_3075203
  have hstable : (prefixWord ++ tailWord_3075203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075203).length < 2 ^ (prefixWord ++ tailWord_3075203).sum := by decide
  have hdescent : baseEnd_3075203 < baseStart_3075203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075224 : List Nat := [2, 1, 2, 4, 2, 1, 2, 4, 1, 3]
def baseStart_3075224 : Nat := 118140960795 + 3075224 * 2 ^ 59
def prefixEnd_3075224 : Nat := 4983230072969 + 3 ^ 40 * 3075224 * 2
def baseEnd_3075224 : Nat := 1052712021494787603771539

theorem tailTrace_3075224 : CollatzResearch.WordTrace tailWord_3075224 prefixEnd_3075224 1052712021494787603771539 := by
  unfold tailWord_3075224
  simp only [CollatzResearch.WordTrace]
  refine ⟨56081316905498064645244363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74775089207330752860325817 56081316905498064645244363)
  ·
    refine ⟨84121975358247096967866545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56081316905498064645244363 84121975358247096967866545)
    ·
      refine ⟨63091481518685322725899909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84121975358247096967866545 63091481518685322725899909)
      ·
        refine ⟨11829652784753498011106233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63091481518685322725899909 11829652784753498011106233)
        ·
          refine ⟨8872239588565123508329675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11829652784753498011106233 8872239588565123508329675)
          ·
            refine ⟨13308359382847685262494513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8872239588565123508329675 13308359382847685262494513)
            ·
              refine ⟨9981269537135763946870885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13308359382847685262494513 9981269537135763946870885)
              ·
                refine ⟨1871488038212955740038291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9981269537135763946870885 1871488038212955740038291)
                ·
                  refine ⟨2807232057319433610057437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1871488038212955740038291 2807232057319433610057437)
                  ·
                    refine ⟨1052712021494787603771539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2807232057319433610057437 1052712021494787603771539)
                    ·
                      rfl

theorem cell22_3075224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_3075224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075224 prefixEnd_3075224 := by exact prefixLift 3075224
  have htrace : WordTrace (prefixWord ++ tailWord_3075224) baseStart_3075224 baseEnd_3075224 := by
    simpa [prefixWord, tailWord_3075224, baseEnd_3075224] using wordTrace_append hprefix tailTrace_3075224
  have hstable : (prefixWord ++ tailWord_3075224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075224).length < 2 ^ (prefixWord ++ tailWord_3075224).sum := by decide
  have hdescent : baseEnd_3075224 < baseStart_3075224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075237 : List Nat := [1, 3, 1, 2, 1, 5, 3, 1, 5]
def baseStart_3075237 : Nat := 118140960795 + 3075237 * 2 ^ 59
def prefixEnd_3075237 : Nat := 4983230072969 + 3 ^ 40 * 3075237 * 2
def baseEnd_3075237 : Nat := 350905490553486634398833

theorem tailTrace_3075237 : CollatzResearch.WordTrace tailWord_3075237 prefixEnd_3075237 350905490553486634398833 := by
  unfold tailWord_3075237
  simp only [CollatzResearch.WordTrace]
  refine ⟨112163107959949032510711965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74775405306632688340474643 112163107959949032510711965)
  ·
    refine ⟨42061165484980887191516987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112163107959949032510711965 42061165484980887191516987)
    ·
      refine ⟨63091748227471330787275481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42061165484980887191516987 63091748227471330787275481)
      ·
        refine ⟨47318811170603498090456611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63091748227471330787275481 47318811170603498090456611)
        ·
          refine ⟨70978216755905247135684917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47318811170603498090456611 70978216755905247135684917)
          ·
            refine ⟨6654207820866116918970461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70978216755905247135684917 6654207820866116918970461)
            ·
              refine ⟨2495327932824793844613923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6654207820866116918970461 2495327932824793844613923)
              ·
                refine ⟨3742991899237190766920885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495327932824793844613923 3742991899237190766920885)
                ·
                  refine ⟨350905490553486634398833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3742991899237190766920885 350905490553486634398833)
                  ·
                    rfl

theorem cell22_3075237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_3075237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075237 prefixEnd_3075237 := by exact prefixLift 3075237
  have htrace : WordTrace (prefixWord ++ tailWord_3075237) baseStart_3075237 baseEnd_3075237 := by
    simpa [prefixWord, tailWord_3075237, baseEnd_3075237] using wordTrace_append hprefix tailTrace_3075237
  have hstable : (prefixWord ++ tailWord_3075237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075237).length < 2 ^ (prefixWord ++ tailWord_3075237).sum := by decide
  have hdescent : baseEnd_3075237 < baseStart_3075237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075301 : List Nat := [1, 3, 1, 4, 4, 1, 1, 2, 1, 4]
def baseStart_3075301 : Nat := 118140960795 + 3075301 * 2 ^ 59
def prefixEnd_3075301 : Nat := 4983230072969 + 3 ^ 40 * 3075301 * 2
def baseEnd_3075301 : Nat := 1052738380168385069596303

theorem tailTrace_3075301 : CollatzResearch.WordTrace tailWord_3075301 prefixEnd_3075301 1052738380168385069596303 := by
  unfold tailWord_3075301
  simp only [CollatzResearch.WordTrace]
  refine ⟨112165442231717171441041757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74776961487811447627361171 112165442231717171441041757)
  ·
    refine ⟨42062040836893939290390659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112165442231717171441041757 42062040836893939290390659)
    ·
      refine ⟨63093061255340908935585989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42062040836893939290390659 63093061255340908935585989)
      ·
        refine ⟨11829948985376420425422373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63093061255340908935585989 11829948985376420425422373)
        ·
          refine ⟨2218115434758078829766695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11829948985376420425422373 2218115434758078829766695)
          ·
            refine ⟨3327173152137118244650043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218115434758078829766695 3327173152137118244650043)
            ·
              refine ⟨4990759728205677366975065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327173152137118244650043 4990759728205677366975065)
              ·
                refine ⟨3743069796154258025231299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4990759728205677366975065 3743069796154258025231299)
                ·
                  refine ⟨5614604694231387037846949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743069796154258025231299 5614604694231387037846949)
                  ·
                    refine ⟨1052738380168385069596303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5614604694231387037846949 1052738380168385069596303)
                    ·
                      rfl

theorem cell22_3075301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_3075301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075301 prefixEnd_3075301 := by exact prefixLift 3075301
  have htrace : WordTrace (prefixWord ++ tailWord_3075301) baseStart_3075301 baseEnd_3075301 := by
    simpa [prefixWord, tailWord_3075301, baseEnd_3075301] using wordTrace_append hprefix tailTrace_3075301
  have hstable : (prefixWord ++ tailWord_3075301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075301).length < 2 ^ (prefixWord ++ tailWord_3075301).sum := by decide
  have hdescent : baseEnd_3075301 < baseStart_3075301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075310 : List Nat := [4, 1, 2, 1, 1, 1, 4, 8]
def baseStart_3075310 : Nat := 118140960795 + 3075310 * 2 ^ 59
def prefixEnd_3075310 : Nat := 4983230072969 + 3 ^ 40 * 3075310 * 2
def baseEnd_3075310 : Nat := 116971273450256894013475

theorem tailTrace_3075310 : CollatzResearch.WordTrace tailWord_3075310 prefixEnd_3075310 116971273450256894013475 := by
  unfold tailWord_3075310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14020721311085570747264923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74777180325789710652079589 14020721311085570747264923)
  ·
    refine ⟨21031081966628356120897385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14020721311085570747264923 21031081966628356120897385)
    ·
      refine ⟨15773311474971267090673039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21031081966628356120897385 15773311474971267090673039)
      ·
        refine ⟨23659967212456900636009559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15773311474971267090673039 23659967212456900636009559)
        ·
          refine ⟨35489950818685350954014339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23659967212456900636009559 35489950818685350954014339)
          ·
            refine ⟨53234926228028026431021509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35489950818685350954014339 53234926228028026431021509)
            ·
              refine ⟨9981548667755254955816533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53234926228028026431021509 9981548667755254955816533)
              ·
                refine ⟨116971273450256894013475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9981548667755254955816533 116971273450256894013475)
                ·
                  rfl

theorem cell22_3075310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_3075310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075310 prefixEnd_3075310 := by exact prefixLift 3075310
  have htrace : WordTrace (prefixWord ++ tailWord_3075310) baseStart_3075310 baseEnd_3075310 := by
    simpa [prefixWord, tailWord_3075310, baseEnd_3075310] using wordTrace_append hprefix tailTrace_3075310
  have hstable : (prefixWord ++ tailWord_3075310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075310).length < 2 ^ (prefixWord ++ tailWord_3075310).sum := by decide
  have hdescent : baseEnd_3075310 < baseStart_3075310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075340 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_3075340 : Nat := 118140960795 + 3075340 * 2 ^ 59
def prefixEnd_3075340 : Nat := 4983230072969 + 3 ^ 40 * 3075340 * 2
def baseEnd_3075340 : Nat := 1052751730665401967871183

theorem tailTrace_3075340 : CollatzResearch.WordTrace tailWord_3075340 prefixEnd_3075340 1052751730665401967871183 := by
  unfold tailWord_3075340
  simp only [CollatzResearch.WordTrace]
  refine ⟨56083432339287940550855737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74777909785717254067807649 56083432339287940550855737)
  ·
    refine ⟨42062574254465955413141803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56083432339287940550855737 42062574254465955413141803)
    ·
      refine ⟨63093861381698933119712705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42062574254465955413141803 63093861381698933119712705)
      ·
        refine ⟨47320396036274199839784529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63093861381698933119712705 47320396036274199839784529)
        ·
          refine ⟨35490297027205649879838397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47320396036274199839784529 35490297027205649879838397)
          ·
            refine ⟨13308861385202118704939399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35490297027205649879838397 13308861385202118704939399)
            ·
              refine ⟨19963292077803178057409099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13308861385202118704939399 19963292077803178057409099)
              ·
                refine ⟨29944938116704767086113649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19963292077803178057409099 29944938116704767086113649)
                ·
                  refine ⟨22458703587528575314585237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29944938116704767086113649 22458703587528575314585237)
                  ·
                    refine ⟨1052751730665401967871183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22458703587528575314585237 1052751730665401967871183)
                    ·
                      rfl

theorem cell22_3075340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_3075340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075340 prefixEnd_3075340 := by exact prefixLift 3075340
  have htrace : WordTrace (prefixWord ++ tailWord_3075340) baseStart_3075340 baseEnd_3075340 := by
    simpa [prefixWord, tailWord_3075340, baseEnd_3075340] using wordTrace_append hprefix tailTrace_3075340
  have hstable : (prefixWord ++ tailWord_3075340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075340).length < 2 ^ (prefixWord ++ tailWord_3075340).sum := by decide
  have hdescent : baseEnd_3075340 < baseStart_3075340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075359 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 3, 3]
def baseStart_3075359 : Nat := 118140960795 + 3075359 * 2 ^ 59
def prefixEnd_3075359 : Nat := 4983230072969 + 3 ^ 40 * 3075359 * 2
def baseEnd_3075359 : Nat := 1052758234753692251646125

theorem tailTrace_3075359 : CollatzResearch.WordTrace tailWord_3075359 prefixEnd_3075359 1052758234753692251646125 := by
  unfold tailWord_3075359
  simp only [CollatzResearch.WordTrace]
  refine ⟨112167557665507047346653131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74778371777004698231102087 112167557665507047346653131)
  ·
    refine ⟨168251336498260571019979697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112167557665507047346653131 168251336498260571019979697)
    ·
      refine ⟨126188502373695428264984773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168251336498260571019979697 126188502373695428264984773)
      ·
        refine ⟨23660344195067892799684645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126188502373695428264984773 23660344195067892799684645)
        ·
          refine ⟨4436314536575229899940871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23660344195067892799684645 4436314536575229899940871)
          ·
            refine ⟨6654471804862844849911307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4436314536575229899940871 6654471804862844849911307)
            ·
              refine ⟨9981707707294267274866961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6654471804862844849911307 9981707707294267274866961)
              ·
                refine ⟨7486280780470700456150221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9981707707294267274866961 7486280780470700456150221)
                ·
                  refine ⟨2807355292676512671056333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7486280780470700456150221 2807355292676512671056333)
                  ·
                    refine ⟨1052758234753692251646125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2807355292676512671056333 1052758234753692251646125)
                    ·
                      rfl

theorem cell22_3075359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 3].length) (baseStart_3075359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075359 prefixEnd_3075359 := by exact prefixLift 3075359
  have htrace : WordTrace (prefixWord ++ tailWord_3075359) baseStart_3075359 baseEnd_3075359 := by
    simpa [prefixWord, tailWord_3075359, baseEnd_3075359] using wordTrace_append hprefix tailTrace_3075359
  have hstable : (prefixWord ++ tailWord_3075359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075359).length < 2 ^ (prefixWord ++ tailWord_3075359).sum := by decide
  have hdescent : baseEnd_3075359 < baseStart_3075359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075389 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 7]
def baseStart_3075389 : Nat := 118140960795 + 3075389 * 2 ^ 59
def prefixEnd_3075389 : Nat := 4983230072969 + 3 ^ 40 * 3075389 * 2
def baseEnd_3075389 : Nat := 350922834788927391132011

theorem tailTrace_3075389 : CollatzResearch.WordTrace tailWord_3075389 prefixEnd_3075389 350922834788927391132011 := by
  unfold tailWord_3075389
  simp only [CollatzResearch.WordTrace]
  refine ⟨112168651855398362470245221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74779101236932241646830147 112168651855398362470245221)
  ·
    refine ⟨21031622222887192963170979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112168651855398362470245221 21031622222887192963170979)
    ·
      refine ⟨31547433334330789444756469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21031622222887192963170979 31547433334330789444756469)
      ·
        refine ⟨2957571875093511510445919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31547433334330789444756469 2957571875093511510445919)
        ·
          refine ⟨4436357812640267265668879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2957571875093511510445919 4436357812640267265668879)
          ·
            refine ⟨6654536718960400898503319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4436357812640267265668879 6654536718960400898503319)
            ·
              refine ⟨9981805078440601347754979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6654536718960400898503319 9981805078440601347754979)
              ·
                refine ⟨14972707617660902021632469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9981805078440601347754979 14972707617660902021632469)
                ·
                  refine ⟨350922834788927391132011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14972707617660902021632469 350922834788927391132011)
                  ·
                    rfl

theorem cell22_3075389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_3075389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075389 prefixEnd_3075389 := by exact prefixLift 3075389
  have htrace : WordTrace (prefixWord ++ tailWord_3075389) baseStart_3075389 baseEnd_3075389 := by
    simpa [prefixWord, tailWord_3075389, baseEnd_3075389] using wordTrace_append hprefix tailTrace_3075389
  have hstable : (prefixWord ++ tailWord_3075389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075389).length < 2 ^ (prefixWord ++ tailWord_3075389).sum := by decide
  have hdescent : baseEnd_3075389 < baseStart_3075389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075447 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 2, 4]
def baseStart_3075447 : Nat := 118140960795 + 3075447 * 2 ^ 59
def prefixEnd_3075447 : Nat := 4983230072969 + 3 ^ 40 * 3075447 * 2
def baseEnd_3075447 : Nat := 1052788358952089355445855

theorem tailTrace_3075447 : CollatzResearch.WordTrace tailWord_3075447 prefixEnd_3075447 1052788358952089355445855 := by
  unfold tailWord_3075447
  simp only [CollatzResearch.WordTrace]
  refine ⟨112170767289188238375856595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74780511526125492250571063 112170767289188238375856595)
  ·
    refine ⟨168256150933782357563784893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112170767289188238375856595 168256150933782357563784893)
    ·
      refine ⟨63096056600168384086419335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168256150933782357563784893 63096056600168384086419335)
      ·
        refine ⟨94644084900252576129629003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63096056600168384086419335 94644084900252576129629003)
        ·
          refine ⟨141966127350378864194443505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94644084900252576129629003 141966127350378864194443505)
          ·
            refine ⟨106474595512784148145832629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141966127350378864194443505 106474595512784148145832629)
            ·
              refine ⟨9981993329323513888671809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106474595512784148145832629 9981993329323513888671809)
              ·
                refine ⟨7486494996992635416503857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9981993329323513888671809 7486494996992635416503857)
                ·
                  refine ⟨5614871247744476562377893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7486494996992635416503857 5614871247744476562377893)
                  ·
                    refine ⟨1052788358952089355445855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5614871247744476562377893 1052788358952089355445855)
                    ·
                      rfl

theorem cell22_3075447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_3075447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075447 prefixEnd_3075447 := by exact prefixLift 3075447
  have htrace : WordTrace (prefixWord ++ tailWord_3075447) baseStart_3075447 baseEnd_3075447 := by
    simpa [prefixWord, tailWord_3075447, baseEnd_3075447] using wordTrace_append hprefix tailTrace_3075447
  have hstable : (prefixWord ++ tailWord_3075447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075447).length < 2 ^ (prefixWord ++ tailWord_3075447).sum := by decide
  have hdescent : baseEnd_3075447 < baseStart_3075447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075511 : List Nat := [1, 1, 3, 1, 3, 2, 3, 4, 1, 3]
def baseStart_3075511 : Nat := 118140960795 + 3075511 * 2 ^ 59
def prefixEnd_3075511 : Nat := 4983230072969 + 3 ^ 40 * 3075511 * 2
def baseEnd_3075511 : Nat := 1052810267460014521845659

theorem tailTrace_3075511 : CollatzResearch.WordTrace tailWord_3075511 prefixEnd_3075511 1052810267460014521845659 := by
  unfold tailWord_3075511
  simp only [CollatzResearch.WordTrace]
  refine ⟨112173101560956377306186387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74782067707304251537457591 112173101560956377306186387)
  ·
    refine ⟨168259652341434565959279581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112173101560956377306186387 168259652341434565959279581)
    ·
      refine ⟨63097369628037962234729843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168259652341434565959279581 63097369628037962234729843)
      ·
        refine ⟨94646054442056943352094765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63097369628037962234729843 94646054442056943352094765)
        ·
          refine ⟨35492270415771353757035537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94646054442056943352094765 35492270415771353757035537)
          ·
            refine ⟨26619202811828515317776653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35492270415771353757035537 26619202811828515317776653)
            ·
              refine ⟨9982201054435693244166245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26619202811828515317776653 9982201054435693244166245)
              ·
                refine ⟨1871662697706692483281171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9982201054435693244166245 1871662697706692483281171)
                ·
                  refine ⟨2807494046560038724921757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1871662697706692483281171 2807494046560038724921757)
                  ·
                    refine ⟨1052810267460014521845659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2807494046560038724921757 1052810267460014521845659)
                    ·
                      rfl

theorem cell22_3075511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_3075511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075511 prefixEnd_3075511 := by exact prefixLift 3075511
  have htrace : WordTrace (prefixWord ++ tailWord_3075511) baseStart_3075511 baseEnd_3075511 := by
    simpa [prefixWord, tailWord_3075511, baseEnd_3075511] using wordTrace_append hprefix tailTrace_3075511
  have hstable : (prefixWord ++ tailWord_3075511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075511).length < 2 ^ (prefixWord ++ tailWord_3075511).sum := by decide
  have hdescent : baseEnd_3075511 < baseStart_3075511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075567 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 3, 5]
def baseStart_3075567 : Nat := 118140960795 + 3075567 * 2 ^ 59
def prefixEnd_3075567 : Nat := 4983230072969 + 3 ^ 40 * 3075567 * 2
def baseEnd_3075567 : Nat := 1052829437404449042445487

theorem tailTrace_3075567 : CollatzResearch.WordTrace tailWord_3075567 prefixEnd_3075567 1052829437404449042445487 := by
  unfold tailWord_3075567
  simp only [CollatzResearch.WordTrace]
  refine ⟨112175144048753498870224955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74783429365835665913483303 112175144048753498870224955)
  ·
    refine ⟨168262716073130248305337433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112175144048753498870224955 168262716073130248305337433)
    ·
      refine ⟨126197037054847686229003075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168262716073130248305337433 126197037054847686229003075)
      ·
        refine ⟨189295555582271529343504613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126197037054847686229003075 189295555582271529343504613)
        ·
          refine ⟨35492916671675911751907115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189295555582271529343504613 35492916671675911751907115)
          ·
            refine ⟨53239375007513867627860673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35492916671675911751907115 53239375007513867627860673)
            ·
              refine ⟨39929531255635400720895505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53239375007513867627860673 39929531255635400720895505)
              ·
                refine ⟨29947148441726550540671629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39929531255635400720895505 29947148441726550540671629)
                ·
                  refine ⟨11230180665647456452751861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29947148441726550540671629 11230180665647456452751861)
                  ·
                    refine ⟨1052829437404449042445487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11230180665647456452751861 1052829437404449042445487)
                    ·
                      rfl

theorem cell22_3075567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_3075567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075567 prefixEnd_3075567 := by exact prefixLift 3075567
  have htrace : WordTrace (prefixWord ++ tailWord_3075567) baseStart_3075567 baseEnd_3075567 := by
    simpa [prefixWord, tailWord_3075567, baseEnd_3075567] using wordTrace_append hprefix tailTrace_3075567
  have hstable : (prefixWord ++ tailWord_3075567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075567).length < 2 ^ (prefixWord ++ tailWord_3075567).sum := by decide
  have hdescent : baseEnd_3075567 < baseStart_3075567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075569 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 6]
def baseStart_3075569 : Nat := 118140960795 + 3075569 * 2 ^ 59
def prefixEnd_3075569 : Nat := 4983230072969 + 3 ^ 40 * 3075569 * 2
def baseEnd_3075569 : Nat := 350943374015107234631827

theorem tailTrace_3075569 : CollatzResearch.WordTrace tailWord_3075569 prefixEnd_3075569 350943374015107234631827 := by
  unfold tailWord_3075569
  simp only [CollatzResearch.WordTrace]
  refine ⟨112175216994746253211797761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74783477996497502141198507 112175216994746253211797761)
  ·
    refine ⟨84131412746059689908848321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112175216994746253211797761 84131412746059689908848321)
    ·
      refine ⟨63098559559544767431636241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84131412746059689908848321 63098559559544767431636241)
      ·
        refine ⟨47323919669658575573727181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63098559559544767431636241 47323919669658575573727181)
        ·
          refine ⟨17746469876121965840147693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47323919669658575573727181 17746469876121965840147693)
          ·
            refine ⟨6654926203545737190055385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17746469876121965840147693 6654926203545737190055385)
            ·
              refine ⟨4991194652659302892541539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6654926203545737190055385 4991194652659302892541539)
              ·
                refine ⟨7486791978988954338812309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991194652659302892541539 7486791978988954338812309)
                ·
                  refine ⟨350943374015107234631827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7486791978988954338812309 350943374015107234631827)
                  ·
                    rfl

theorem cell22_3075569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 6].length) (baseStart_3075569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075569 prefixEnd_3075569 := by exact prefixLift 3075569
  have htrace : WordTrace (prefixWord ++ tailWord_3075569) baseStart_3075569 baseEnd_3075569 := by
    simpa [prefixWord, tailWord_3075569, baseEnd_3075569] using wordTrace_append hprefix tailTrace_3075569
  have hstable : (prefixWord ++ tailWord_3075569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075569).length < 2 ^ (prefixWord ++ tailWord_3075569).sum := by decide
  have hdescent : baseEnd_3075569 < baseStart_3075569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075586 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3075586 : Nat := 118140960795 + 3075586 * 2 ^ 59
def prefixEnd_3075586 : Nat := 4983230072969 + 3 ^ 40 * 3075586 * 2
def baseEnd_3075586 : Nat := 350945313830913108740143

theorem tailTrace_3075586 : CollatzResearch.WordTrace tailWord_3075586 prefixEnd_3075586 350945313830913108740143 := by
  unfold tailWord_3075586
  simp only [CollatzResearch.WordTrace]
  refine ⟨28043959258921166278791653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74783891357123110076777741 28043959258921166278791653)
  ·
    refine ⟨5258242361047718677273435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28043959258921166278791653 5258242361047718677273435)
    ·
      refine ⟨7887363541571578015910153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5258242361047718677273435 7887363541571578015910153)
      ·
        refine ⟨5915522656178683511932615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7887363541571578015910153 5915522656178683511932615)
        ·
          refine ⟨8873283984268025267898923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5915522656178683511932615 8873283984268025267898923)
          ·
            refine ⟨13309925976402037901848385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8873283984268025267898923 13309925976402037901848385)
            ·
              refine ⟨9982444482301528426386289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13309925976402037901848385 9982444482301528426386289)
              ·
                refine ⟨7486833361726146319789717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9982444482301528426386289 7486833361726146319789717)
                ·
                  refine ⟨350945313830913108740143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7486833361726146319789717 350945313830913108740143)
                  ·
                    rfl

theorem cell22_3075586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3075586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075586 prefixEnd_3075586 := by exact prefixLift 3075586
  have htrace : WordTrace (prefixWord ++ tailWord_3075586) baseStart_3075586 baseEnd_3075586 := by
    simpa [prefixWord, tailWord_3075586, baseEnd_3075586] using wordTrace_append hprefix tailTrace_3075586
  have hstable : (prefixWord ++ tailWord_3075586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075586).length < 2 ^ (prefixWord ++ tailWord_3075586).sum := by decide
  have hdescent : baseEnd_3075586 < baseStart_3075586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075588 : List Nat := [2, 3, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_3075588 : Nat := 118140960795 + 3075588 * 2 ^ 59
def prefixEnd_3075588 : Nat := 4983230072969 + 3 ^ 40 * 3075588 * 2
def baseEnd_3075588 : Nat := 1052836626133611987670423

theorem tailTrace_3075588 : CollatzResearch.WordTrace tailWord_3075588 prefixEnd_3075588 1052836626133611987670423 := by
  unfold tailWord_3075588
  simp only [CollatzResearch.WordTrace]
  refine ⟨56087954990838709728369709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74783939987784946304492945 56087954990838709728369709)
  ·
    refine ⟨21032983121564516148138641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56087954990838709728369709 21032983121564516148138641)
    ·
      refine ⟨15774737341173387111103981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21032983121564516148138641 15774737341173387111103981)
      ·
        refine ⟨5915526502940020166663993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15774737341173387111103981 5915526502940020166663993)
        ·
          refine ⟨4436644877205015124997995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5915526502940020166663993 4436644877205015124997995)
          ·
            refine ⟨6654967315807522687496993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4436644877205015124997995 6654967315807522687496993)
            ·
              refine ⟨4991225486855642015622745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6654967315807522687496993 4991225486855642015622745)
              ·
                refine ⟨3743419115141731511717059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4991225486855642015622745 3743419115141731511717059)
                ·
                  refine ⟨5615128672712597267575589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743419115141731511717059 5615128672712597267575589)
                  ·
                    refine ⟨1052836626133611987670423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5615128672712597267575589 1052836626133611987670423)
                    ·
                      rfl

theorem cell22_3075588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_3075588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075588 prefixEnd_3075588 := by exact prefixLift 3075588
  have htrace : WordTrace (prefixWord ++ tailWord_3075588) baseStart_3075588 baseEnd_3075588 := by
    simpa [prefixWord, tailWord_3075588, baseEnd_3075588] using wordTrace_append hprefix tailTrace_3075588
  have hstable : (prefixWord ++ tailWord_3075588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075588).length < 2 ^ (prefixWord ++ tailWord_3075588).sum := by decide
  have hdescent : baseEnd_3075588 < baseStart_3075588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075616 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 2, 4]
def baseStart_3075616 : Nat := 118140960795 + 3075616 * 2 ^ 59
def prefixEnd_3075616 : Nat := 4983230072969 + 3 ^ 40 * 3075616 * 2
def baseEnd_3075616 : Nat := 1052846211105829247970337

theorem tailTrace_3075616 : CollatzResearch.WordTrace tailWord_3075616 prefixEnd_3075616 1052846211105829247970337 := by
  unfold tailWord_3075616
  simp only [CollatzResearch.WordTrace]
  refine ⟨56088465612787990119379351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74784620817050653492505801 56088465612787990119379351)
  ·
    refine ⟨84132698419181985179069027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56088465612787990119379351 84132698419181985179069027)
    ·
      refine ⟨126199047628772977768603541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84132698419181985179069027 126199047628772977768603541)
      ·
        refine ⟨5915580357598733332903291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126199047628772977768603541 5915580357598733332903291)
        ·
          refine ⟨8873370536398099999354937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5915580357598733332903291 8873370536398099999354937)
          ·
            refine ⟨6655027902298574999516203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8873370536398099999354937 6655027902298574999516203)
            ·
              refine ⟨9982541853447862499274305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6655027902298574999516203 9982541853447862499274305)
              ·
                refine ⟨7486906390085896874455729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9982541853447862499274305 7486906390085896874455729)
                ·
                  refine ⟨5615179792564422655841797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7486906390085896874455729 5615179792564422655841797)
                  ·
                    refine ⟨1052846211105829247970337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5615179792564422655841797 1052846211105829247970337)
                    ·
                      rfl

theorem cell22_3075616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_3075616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075616 prefixEnd_3075616 := by exact prefixLift 3075616
  have htrace : WordTrace (prefixWord ++ tailWord_3075616) baseStart_3075616 baseEnd_3075616 := by
    simpa [prefixWord, tailWord_3075616, baseEnd_3075616] using wordTrace_append hprefix tailTrace_3075616
  have hstable : (prefixWord ++ tailWord_3075616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075616).length < 2 ^ (prefixWord ++ tailWord_3075616).sum := by decide
  have hdescent : baseEnd_3075616 < baseStart_3075616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075676 : List Nat := [2, 2, 4, 1, 2, 1, 1, 4, 5]
def baseStart_3075676 : Nat := 118140960795 + 3075676 * 2 ^ 59
def prefixEnd_3075676 : Nat := 4983230072969 + 3 ^ 40 * 3075676 * 2
def baseEnd_3075676 : Nat := 350955583444003030490051

theorem tailTrace_3075676 : CollatzResearch.WordTrace tailWord_3075676 prefixEnd_3075676 350955583444003030490051 := by
  unfold tailWord_3075676
  simp only [CollatzResearch.WordTrace]
  refine ⟨56089559802679305242971441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74786079736905740323961921 56089559802679305242971441)
  ·
    refine ⟨42067169852009478932228581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56089559802679305242971441 42067169852009478932228581)
    ·
      refine ⟨7887594347251777299792859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42067169852009478932228581 7887594347251777299792859)
      ·
        refine ⟨11831391520877665949689289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7887594347251777299792859 11831391520877665949689289)
        ·
          refine ⟨8873543640658249462266967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11831391520877665949689289 8873543640658249462266967)
          ·
            refine ⟨13310315460987374193400451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8873543640658249462266967 13310315460987374193400451)
            ·
              refine ⟨19965473191481061290100677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13310315460987374193400451 19965473191481061290100677)
              ·
                refine ⟨3743526223402698991893877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19965473191481061290100677 3743526223402698991893877)
                ·
                  refine ⟨350955583444003030490051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3743526223402698991893877 350955583444003030490051)
                  ·
                    rfl

theorem cell22_3075676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_3075676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075676 prefixEnd_3075676 := by exact prefixLift 3075676
  have htrace : WordTrace (prefixWord ++ tailWord_3075676) baseStart_3075676 baseEnd_3075676 := by
    simpa [prefixWord, tailWord_3075676, baseEnd_3075676] using wordTrace_append hprefix tailTrace_3075676
  have hstable : (prefixWord ++ tailWord_3075676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075676).length < 2 ^ (prefixWord ++ tailWord_3075676).sum := by decide
  have hdescent : baseEnd_3075676 < baseStart_3075676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075689 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 3, 4]
def baseStart_3075689 : Nat := 118140960795 + 3075689 * 2 ^ 59
def prefixEnd_3075689 : Nat := 4983230072969 + 3 ^ 40 * 3075689 * 2
def baseEnd_3075689 : Nat := 1052871200497681390895113

theorem tailTrace_3075689 : CollatzResearch.WordTrace tailWord_3075689 prefixEnd_3075689 1052871200497681390895113 := by
  unfold tailWord_3075689
  simp only [CollatzResearch.WordTrace]
  refine ⟨112179593754311513706166121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74786395836207675804110747 112179593754311513706166121)
  ·
    refine ⟨84134695315733635279624591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112179593754311513706166121 84134695315733635279624591)
    ·
      refine ⟨126202042973600452919436887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84134695315733635279624591 126202042973600452919436887)
      ·
        refine ⟨189303064460400679379155331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126202042973600452919436887 189303064460400679379155331)
        ·
          refine ⟨283954596690601019068732997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189303064460400679379155331 283954596690601019068732997)
          ·
            refine ⟨53241486879487691075387437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283954596690601019068732997 53241486879487691075387437)
            ·
              refine ⟨19965557579807884153270289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53241486879487691075387437 19965557579807884153270289)
              ·
                refine ⟨14974168184855913114952717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19965557579807884153270289 14974168184855913114952717)
                ·
                  refine ⟨5615313069320967418107269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14974168184855913114952717 5615313069320967418107269)
                  ·
                    refine ⟨1052871200497681390895113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5615313069320967418107269 1052871200497681390895113)
                    ·
                      rfl

theorem cell22_3075689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_3075689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075689 prefixEnd_3075689 := by exact prefixLift 3075689
  have htrace : WordTrace (prefixWord ++ tailWord_3075689) baseStart_3075689 baseEnd_3075689 := by
    simpa [prefixWord, tailWord_3075689, baseEnd_3075689] using wordTrace_append hprefix tailTrace_3075689
  have hstable : (prefixWord ++ tailWord_3075689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075689).length < 2 ^ (prefixWord ++ tailWord_3075689).sum := by decide
  have hdescent : baseEnd_3075689 < baseStart_3075689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075721 : List Nat := [1, 2, 1, 1, 4, 1, 3, 5, 4]
def baseStart_3075721 : Nat := 118140960795 + 3075721 * 2 ^ 59
def prefixEnd_3075721 : Nat := 4983230072969 + 3 ^ 40 * 3075721 * 2
def baseEnd_3075721 : Nat := 350960718250547991365005

theorem tailTrace_3075721 : CollatzResearch.WordTrace tailWord_3075721 prefixEnd_3075721 350960718250547991365005 := by
  unfold tailWord_3075721
  simp only [CollatzResearch.WordTrace]
  refine ⟨112180760890195583171331017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74787173926797055447554011 112180760890195583171331017)
  ·
    refine ⟨84135570667646687378498263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112180760890195583171331017 84135570667646687378498263)
    ·
      refine ⟨126203356001470031067747395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84135570667646687378498263 126203356001470031067747395)
      ·
        refine ⟨189305034002205046601621093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126203356001470031067747395 189305034002205046601621093)
        ·
          refine ⟨35494693875413446237803955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189305034002205046601621093 35494693875413446237803955)
          ·
            refine ⟨53242040813120169356705933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35494693875413446237803955 53242040813120169356705933)
            ·
              refine ⟨19965765304920063508764725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53242040813120169356705933 19965765304920063508764725)
              ·
                refine ⟨1871790497336255953946693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19965765304920063508764725 1871790497336255953946693)
                ·
                  refine ⟨350960718250547991365005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1871790497336255953946693 350960718250547991365005)
                  ·
                    rfl

theorem cell22_3075721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 4].length) (baseStart_3075721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075721 prefixEnd_3075721 := by exact prefixLift 3075721
  have htrace : WordTrace (prefixWord ++ tailWord_3075721) baseStart_3075721 baseEnd_3075721 := by
    simpa [prefixWord, tailWord_3075721, baseEnd_3075721] using wordTrace_append hprefix tailTrace_3075721
  have hstable : (prefixWord ++ tailWord_3075721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075721).length < 2 ^ (prefixWord ++ tailWord_3075721).sum := by decide
  have hdescent : baseEnd_3075721 < baseStart_3075721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075804 : List Nat := [2, 2, 5, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3075804 : Nat := 118140960795 + 3075804 * 2 ^ 59
def prefixEnd_3075804 : Nat := 4983230072969 + 3 ^ 40 * 3075804 * 2
def baseEnd_3075804 : Nat := 1052910567347859424269761

theorem tailTrace_3075804 : CollatzResearch.WordTrace tailWord_3075804 prefixEnd_3075804 1052910567347859424269761 := by
  unfold tailWord_3075804
  simp only [CollatzResearch.WordTrace]
  refine ⟨56091894074447444173301233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74789192099263258897734977 56091894074447444173301233)
  ·
    refine ⟨42068920555835583129975925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56091894074447444173301233 42068920555835583129975925)
    ·
      refine ⟨3943961302109585918435243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42068920555835583129975925 3943961302109585918435243)
      ·
        refine ⟨5915941953164378877652865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3943961302109585918435243 5915941953164378877652865)
        ·
          refine ⟨4436956464873284158239649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5915941953164378877652865 4436956464873284158239649)
          ·
            refine ⟨3327717348654963118679737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4436956464873284158239649 3327717348654963118679737)
            ·
              refine ⟨2495788011491222339009803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3327717348654963118679737 2495788011491222339009803)
              ·
                refine ⟨3743682017236833508514705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495788011491222339009803 3743682017236833508514705)
                ·
                  refine ⟨2807761512927625131386029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3743682017236833508514705 2807761512927625131386029)
                  ·
                    refine ⟨1052910567347859424269761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2807761512927625131386029 1052910567347859424269761)
                    ·
                      rfl

theorem cell22_3075804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3075804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075804 prefixEnd_3075804 := by exact prefixLift 3075804
  have htrace : WordTrace (prefixWord ++ tailWord_3075804) baseStart_3075804 baseEnd_3075804 := by
    simpa [prefixWord, tailWord_3075804, baseEnd_3075804] using wordTrace_append hprefix tailTrace_3075804
  have hstable : (prefixWord ++ tailWord_3075804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075804).length < 2 ^ (prefixWord ++ tailWord_3075804).sum := by decide
  have hdescent : baseEnd_3075804 < baseStart_3075804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075890 : List Nat := [3, 2, 1, 1, 3, 3, 2, 3, 4]
def baseStart_3075890 : Nat := 118140960795 + 3075890 * 2 ^ 59
def prefixEnd_3075890 : Nat := 4983230072969 + 3 ^ 40 * 3075890 * 2
def baseEnd_3075890 : Nat := 350980002301794622206499

theorem tailTrace_3075890 : CollatzResearch.WordTrace tailWord_3075890 prefixEnd_3075890 350980002301794622206499 := by
  unfold tailWord_3075890
  simp only [CollatzResearch.WordTrace]
  refine ⟨28046731206645831258558281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74791283217722216689488749 28046731206645831258558281)
  ·
    refine ⟨21035048404984373443918711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28046731206645831258558281 21035048404984373443918711)
    ·
      refine ⟨31552572607476560165878067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21035048404984373443918711 31552572607476560165878067)
      ·
        refine ⟨47328858911214840248817101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31552572607476560165878067 47328858911214840248817101)
        ·
          refine ⟨17748322091705565093306413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47328858911214840248817101 17748322091705565093306413)
          ·
            refine ⟨6655620784389586909989905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17748322091705565093306413 6655620784389586909989905)
            ·
              refine ⟨4991715588292190182492429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6655620784389586909989905 4991715588292190182492429)
              ·
                refine ⟨1871893345609571318434661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4991715588292190182492429 1871893345609571318434661)
                ·
                  refine ⟨350980002301794622206499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1871893345609571318434661 350980002301794622206499)
                  ·
                    rfl

theorem cell22_3075890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_3075890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075890 prefixEnd_3075890 := by exact prefixLift 3075890
  have htrace : WordTrace (prefixWord ++ tailWord_3075890) baseStart_3075890 baseEnd_3075890 := by
    simpa [prefixWord, tailWord_3075890, baseEnd_3075890] using wordTrace_append hprefix tailTrace_3075890
  have hstable : (prefixWord ++ tailWord_3075890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075890).length < 2 ^ (prefixWord ++ tailWord_3075890).sum := by decide
  have hdescent : baseEnd_3075890 < baseStart_3075890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075892 : List Nat := [2, 5, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_3075892 : Nat := 118140960795 + 3075892 * 2 ^ 59
def prefixEnd_3075892 : Nat := 4983230072969 + 3 ^ 40 * 3075892 * 2
def baseEnd_3075892 : Nat := 1052940691546256528069491

theorem tailTrace_3075892 : CollatzResearch.WordTrace tailWord_3075892 prefixEnd_3075892 1052940691546256528069491 := by
  unfold tailWord_3075892
  simp only [CollatzResearch.WordTrace]
  refine ⟨56093498886288039687902965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74791331848384052917203953 56093498886288039687902965)
  ·
    refine ⟨5258765520589503720740903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56093498886288039687902965 5258765520589503720740903)
    ·
      refine ⟨7888148280884255581111355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5258765520589503720740903 7888148280884255581111355)
      ·
        refine ⟨11832222421326383371667033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7888148280884255581111355 11832222421326383371667033)
        ·
          refine ⟨8874166815994787528750275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11832222421326383371667033 8874166815994787528750275)
          ·
            refine ⟨13311250223992181293125413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8874166815994787528750275 13311250223992181293125413)
            ·
              refine ⟨2495859416998533992461015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13311250223992181293125413 2495859416998533992461015)
              ·
                refine ⟨3743789125497800988691523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495859416998533992461015 3743789125497800988691523)
                ·
                  refine ⟨5615683688246701483037285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743789125497800988691523 5615683688246701483037285)
                  ·
                    refine ⟨1052940691546256528069491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5615683688246701483037285 1052940691546256528069491)
                    ·
                      rfl

theorem cell22_3075892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_3075892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075892 prefixEnd_3075892 := by exact prefixLift 3075892
  have htrace : WordTrace (prefixWord ++ tailWord_3075892) baseStart_3075892 baseEnd_3075892 := by
    simpa [prefixWord, tailWord_3075892, baseEnd_3075892] using wordTrace_append hprefix tailTrace_3075892
  have hstable : (prefixWord ++ tailWord_3075892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075892).length < 2 ^ (prefixWord ++ tailWord_3075892).sum := by decide
  have hdescent : baseEnd_3075892 < baseStart_3075892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075922 : List Nat := [3, 2, 2, 1, 1, 4, 3, 1, 2, 3]
def baseStart_3075922 : Nat := 118140960795 + 3075922 * 2 ^ 59
def prefixEnd_3075922 : Nat := 4983230072969 + 3 ^ 40 * 3075922 * 2
def baseEnd_3075922 : Nat := 1052950961159346449819399

theorem tailTrace_3075922 : CollatzResearch.WordTrace tailWord_3075922 prefixEnd_3075922 1052950961159346449819399 := by
  unfold tailWord_3075922
  simp only [CollatzResearch.WordTrace]
  refine ⟨28047022990616848624849505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74792061308311596332932013 28047022990616848624849505)
  ·
    refine ⟨21035267242962636468637129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28047022990616848624849505 21035267242962636468637129)
    ·
      refine ⟨15776450432221977351477847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21035267242962636468637129 15776450432221977351477847)
      ·
        refine ⟨23664675648332966027216771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15776450432221977351477847 23664675648332966027216771)
        ·
          refine ⟨35497013472499449040825157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23664675648332966027216771 35497013472499449040825157)
          ·
            refine ⟨6655690026093646695154717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35497013472499449040825157 6655690026093646695154717)
            ·
              refine ⟨2495883759785117510683019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6655690026093646695154717 2495883759785117510683019)
              ·
                refine ⟨3743825639677676266024529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495883759785117510683019 3743825639677676266024529)
                ·
                  refine ⟨2807869229758257199518397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3743825639677676266024529 2807869229758257199518397)
                  ·
                    refine ⟨1052950961159346449819399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2807869229758257199518397 1052950961159346449819399)
                    ·
                      rfl

theorem cell22_3075922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_3075922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3075922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3075922 prefixEnd_3075922 := by exact prefixLift 3075922
  have htrace : WordTrace (prefixWord ++ tailWord_3075922) baseStart_3075922 baseEnd_3075922 := by
    simpa [prefixWord, tailWord_3075922, baseEnd_3075922] using wordTrace_append hprefix tailTrace_3075922
  have hstable : (prefixWord ++ tailWord_3075922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075922).length < 2 ^ (prefixWord ++ tailWord_3075922).sum := by decide
  have hdescent : baseEnd_3075922 < baseStart_3075922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076025 : List Nat := [1, 2, 1, 4, 2, 1, 3, 4, 4]
def baseStart_3076025 : Nat := 118140960795 + 3076025 * 2 ^ 59
def prefixEnd_3076025 : Nat := 4983230072969 + 3 ^ 40 * 3076025 * 2
def baseEnd_3076025 : Nat := 350995406721429504831361

theorem tailTrace_3076025 : CollatzResearch.WordTrace tailWord_3076025 prefixEnd_3076025 350995406721429504831361 := by
  unfold tailWord_3076025
  simp only [CollatzResearch.WordTrace]
  refine ⟨112191848681094243090397529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74794565787396162060265019 112191848681094243090397529)
  ·
    refine ⟨84143886510820682317798147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112191848681094243090397529 84143886510820682317798147)
    ·
      refine ⟨126215829766231023476697221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84143886510820682317798147 126215829766231023476697221)
      ·
        refine ⟨23665468081168316901880729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126215829766231023476697221 23665468081168316901880729)
        ·
          refine ⟨17749101060876237676410547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23665468081168316901880729 17749101060876237676410547)
          ·
            refine ⟨26623651591314356514615821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17749101060876237676410547 26623651591314356514615821)
            ·
              refine ⟨9983869346742883692980933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26623651591314356514615821 9983869346742883692980933)
              ·
                refine ⟨1871975502514290692433925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9983869346742883692980933 1871975502514290692433925)
                ·
                  refine ⟨350995406721429504831361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1871975502514290692433925 350995406721429504831361)
                  ·
                    rfl

theorem cell22_3076025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 4].length) (baseStart_3076025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076025 prefixEnd_3076025 := by exact prefixLift 3076025
  have htrace : WordTrace (prefixWord ++ tailWord_3076025) baseStart_3076025 baseEnd_3076025 := by
    simpa [prefixWord, tailWord_3076025, baseEnd_3076025] using wordTrace_append hprefix tailTrace_3076025
  have hstable : (prefixWord ++ tailWord_3076025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076025).length < 2 ^ (prefixWord ++ tailWord_3076025).sum := by decide
  have hdescent : baseEnd_3076025 < baseStart_3076025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076040 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 1, 5]
def baseStart_3076040 : Nat := 118140960795 + 3076040 * 2 ^ 59
def prefixEnd_3076040 : Nat := 4983230072969 + 3 ^ 40 * 3076040 * 2
def baseEnd_3076040 : Nat := 1052991354970833475369037

theorem tailTrace_3076040 : CollatzResearch.WordTrace tailWord_3076040 prefixEnd_3076040 1052991354970833475369037 := by
  unfold tailWord_3076040
  simp only [CollatzResearch.WordTrace]
  refine ⟨56096197888019950326096787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74794930517359933768129049 56096197888019950326096787)
  ·
    refine ⟨84144296832029925489145181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56096197888019950326096787 84144296832029925489145181)
    ·
      refine ⟨31554111312011222058429443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84144296832029925489145181 31554111312011222058429443)
      ·
        refine ⟨47331166968016833087644165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31554111312011222058429443 47331166968016833087644165)
        ·
          refine ⟨8874593806503156203933281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47331166968016833087644165 8874593806503156203933281)
          ·
            refine ⟨6655945354877367152949961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8874593806503156203933281 6655945354877367152949961)
            ·
              refine ⟨4991959016158025364712471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6655945354877367152949961 4991959016158025364712471)
              ·
                refine ⟨7487938524237038047068707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991959016158025364712471 7487938524237038047068707)
                ·
                  refine ⟨11231907786355557070603061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7487938524237038047068707 11231907786355557070603061)
                  ·
                    refine ⟨1052991354970833475369037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11231907786355557070603061 1052991354970833475369037)
                    ·
                      rfl

theorem cell22_3076040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_3076040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076040 prefixEnd_3076040 := by exact prefixLift 3076040
  have htrace : WordTrace (prefixWord ++ tailWord_3076040) baseStart_3076040 baseEnd_3076040 := by
    simpa [prefixWord, tailWord_3076040, baseEnd_3076040] using wordTrace_append hprefix tailTrace_3076040
  have hstable : (prefixWord ++ tailWord_3076040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076040).length < 2 ^ (prefixWord ++ tailWord_3076040).sum := by decide
  have hdescent : baseEnd_3076040 < baseStart_3076040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076061 : List Nat := [1, 4, 3, 1, 4, 1, 2, 1, 1, 4]
def baseStart_3076061 : Nat := 118140960795 + 3076061 * 2 ^ 59
def prefixEnd_3076061 : Nat := 4983230072969 + 3 ^ 40 * 3076061 * 2
def baseEnd_3076061 : Nat := 1052998543699996420593973

theorem tailTrace_3076061 : CollatzResearch.WordTrace tailWord_3076061 prefixEnd_3076061 1052998543699996420593973 := by
  unfold tailWord_3076061
  simp only [CollatzResearch.WordTrace]
  refine ⟨112193161708963821238708037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74795441139309214159138691 112193161708963821238708037)
  ·
    refine ⟨21036217820430716482257757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112193161708963821238708037 21036217820430716482257757)
    ·
      refine ⟨7888581682661518680846659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21036217820430716482257757 7888581682661518680846659)
      ·
        refine ⟨11832872523992278021269989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7888581682661518680846659 11832872523992278021269989)
        ·
          refine ⟨2218663598248552128988123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11832872523992278021269989 2218663598248552128988123)
          ·
            refine ⟨3327995397372828193482185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218663598248552128988123 3327995397372828193482185)
            ·
              refine ⟨2495996548029621145111639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3327995397372828193482185 2495996548029621145111639)
              ·
                refine ⟨3743994822044431717667459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495996548029621145111639 3743994822044431717667459)
                ·
                  refine ⟨5615992233066647576501189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743994822044431717667459 5615992233066647576501189)
                  ·
                    refine ⟨1052998543699996420593973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5615992233066647576501189 1052998543699996420593973)
                    ·
                      rfl

theorem cell22_3076061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_3076061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076061 prefixEnd_3076061 := by exact prefixLift 3076061
  have htrace : WordTrace (prefixWord ++ tailWord_3076061) baseStart_3076061 baseEnd_3076061 := by
    simpa [prefixWord, tailWord_3076061, baseEnd_3076061] using wordTrace_append hprefix tailTrace_3076061
  have hstable : (prefixWord ++ tailWord_3076061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076061).length < 2 ^ (prefixWord ++ tailWord_3076061).sum := by decide
  have hdescent : baseEnd_3076061 < baseStart_3076061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076136 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 3, 3]
def baseStart_3076136 : Nat := 118140960795 + 3076136 * 2 ^ 59
def prefixEnd_3076136 : Nat := 4983230072969 + 3 ^ 40 * 3076136 * 2
def baseEnd_3076136 : Nat := 1053024217732721224968743

theorem tailTrace_3076136 : CollatzResearch.WordTrace tailWord_3076136 prefixEnd_3076136 1053024217732721224968743 := by
  unfold tailWord_3076136
  simp only [CollatzResearch.WordTrace]
  refine ⟨56097948591846054523844131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74797264789128072698458841 56097948591846054523844131)
  ·
    refine ⟨84146922887769081785766197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56097948591846054523844131 84146922887769081785766197)
    ·
      refine ⟨7888774020728351417415581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84146922887769081785766197 7888774020728351417415581)
      ·
        refine ⟨2958290257773131781530843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7888774020728351417415581 2958290257773131781530843)
        ·
          refine ⟨4437435386659697672296265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2958290257773131781530843 4437435386659697672296265)
          ·
            refine ⟨3328076539994773254222199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4437435386659697672296265 3328076539994773254222199)
            ·
              refine ⟨4992114809992159881333299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328076539994773254222199 4992114809992159881333299)
              ·
                refine ⟨7488172214988239821999949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4992114809992159881333299 7488172214988239821999949)
                ·
                  refine ⟨2808064580620589933249981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7488172214988239821999949 2808064580620589933249981)
                  ·
                    refine ⟨1053024217732721224968743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2808064580620589933249981 1053024217732721224968743)
                    ·
                      rfl

theorem cell22_3076136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_3076136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076136 prefixEnd_3076136 := by exact prefixLift 3076136
  have htrace : WordTrace (prefixWord ++ tailWord_3076136) baseStart_3076136 baseEnd_3076136 := by
    simpa [prefixWord, tailWord_3076136, baseEnd_3076136] using wordTrace_append hprefix tailTrace_3076136
  have hstable : (prefixWord ++ tailWord_3076136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076136).length < 2 ^ (prefixWord ++ tailWord_3076136).sum := by decide
  have hdescent : baseEnd_3076136 < baseStart_3076136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076143 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 6]
def baseStart_3076143 : Nat := 118140960795 + 3076143 * 2 ^ 59
def prefixEnd_3076143 : Nat := 4983230072969 + 3 ^ 40 * 3076143 * 2
def baseEnd_3076143 : Nat := 351008871325258513347907

theorem tailTrace_3076143 : CollatzResearch.WordTrace tailWord_3076143 prefixEnd_3076143 351008871325258513347907 := by
  unfold tailWord_3076143
  simp only [CollatzResearch.WordTrace]
  refine ⟨112196152494666749243193083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74797434996444499495462055 112196152494666749243193083)
  ·
    refine ⟨168294228742000123864789625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112196152494666749243193083 168294228742000123864789625)
    ·
      refine ⟨126220671556500092898592219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168294228742000123864789625 126220671556500092898592219)
      ·
        refine ⟨189331007334750139347888329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126220671556500092898592219 189331007334750139347888329)
        ·
          refine ⟨141998255501062604510916247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189331007334750139347888329 141998255501062604510916247)
          ·
            refine ⟨212997383251593906766374371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141998255501062604510916247 212997383251593906766374371)
            ·
              refine ⟨319496074877390860149561557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212997383251593906766374371 319496074877390860149561557)
              ·
                refine ⟨7488189254938848284755349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 319496074877390860149561557 7488189254938848284755349)
                ·
                  refine ⟨351008871325258513347907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7488189254938848284755349 351008871325258513347907)
                  ·
                    rfl

theorem cell22_3076143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 6].length) (baseStart_3076143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076143 prefixEnd_3076143 := by exact prefixLift 3076143
  have htrace : WordTrace (prefixWord ++ tailWord_3076143) baseStart_3076143 baseEnd_3076143 := by
    simpa [prefixWord, tailWord_3076143, baseEnd_3076143] using wordTrace_append hprefix tailTrace_3076143
  have hstable : (prefixWord ++ tailWord_3076143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076143).length < 2 ^ (prefixWord ++ tailWord_3076143).sum := by decide
  have hdescent : baseEnd_3076143 < baseStart_3076143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076192 : List Nat := [2, 1, 1, 3, 2, 3, 1, 4, 2, 3]
def baseStart_3076192 : Nat := 118140960795 + 3076192 * 2 ^ 59
def prefixEnd_3076192 : Nat := 4983230072969 + 3 ^ 40 * 3076192 * 2
def baseEnd_3076192 : Nat := 1053043387677155745568571

theorem tailTrace_3076192 : CollatzResearch.WordTrace tailWord_3076192 prefixEnd_3076192 1053043387677155745568571 := by
  unfold tailWord_3076192
  simp only [CollatzResearch.WordTrace]
  refine ⟨56098969835744615305863415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74798626447659487074484553 56098969835744615305863415)
  ·
    refine ⟨84148454753616922958795123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56098969835744615305863415 84148454753616922958795123)
    ·
      refine ⟨126222682130425384438192685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84148454753616922958795123 126222682130425384438192685)
      ·
        refine ⟨47333505798909519164322257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126222682130425384438192685 47333505798909519164322257)
        ·
          refine ⟨35500129349182139373241693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47333505798909519164322257 35500129349182139373241693)
          ·
            refine ⟨13312548505943302264965635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35500129349182139373241693 13312548505943302264965635)
            ·
              refine ⟨19968822758914953397448453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13312548505943302264965635 19968822758914953397448453)
              ·
                refine ⟨3744154267296553762021585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19968822758914953397448453 3744154267296553762021585)
                ·
                  refine ⟨2808115700472415321516189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3744154267296553762021585 2808115700472415321516189)
                  ·
                    refine ⟨1053043387677155745568571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2808115700472415321516189 1053043387677155745568571)
                    ·
                      rfl

theorem cell22_3076192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 2, 3].length) (baseStart_3076192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076192 prefixEnd_3076192 := by exact prefixLift 3076192
  have htrace : WordTrace (prefixWord ++ tailWord_3076192) baseStart_3076192 baseEnd_3076192 := by
    simpa [prefixWord, tailWord_3076192, baseEnd_3076192] using wordTrace_append hprefix tailTrace_3076192
  have hstable : (prefixWord ++ tailWord_3076192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076192).length < 2 ^ (prefixWord ++ tailWord_3076192).sum := by decide
  have hdescent : baseEnd_3076192 < baseStart_3076192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076312 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 6]
def baseStart_3076312 : Nat := 118140960795 + 3076312 * 2 ^ 59
def prefixEnd_3076312 : Nat := 4983230072969 + 3 ^ 40 * 3076312 * 2
def baseEnd_3076312 : Nat := 351028155376505144189401

theorem tailTrace_3076312 : CollatzResearch.WordTrace tailWord_3076312 prefixEnd_3076312 351028155376505144189401 := by
  unfold tailWord_3076312
  simp only [CollatzResearch.WordTrace]
  refine ⟨56101158215527245553047595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74801544287369660737396793 56101158215527245553047595)
  ·
    refine ⟨84151737323290868329571393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56101158215527245553047595 84151737323290868329571393)
    ·
      refine ⟨63113802992468151247178545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84151737323290868329571393 63113802992468151247178545)
      ·
        refine ⟨47335352244351113435383909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63113802992468151247178545 47335352244351113435383909)
        ·
          refine ⟨8875378545815833769134483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47335352244351113435383909 8875378545815833769134483)
          ·
            refine ⟨13313067818723750653701725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8875378545815833769134483 13313067818723750653701725)
            ·
              refine ⟨4992400432021406495138147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13313067818723750653701725 4992400432021406495138147)
              ·
                refine ⟨7488600648032109742707221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4992400432021406495138147 7488600648032109742707221)
                ·
                  refine ⟨351028155376505144189401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7488600648032109742707221 351028155376505144189401)
                  ·
                    rfl

theorem cell22_3076312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 6].length) (baseStart_3076312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076312 prefixEnd_3076312 := by exact prefixLift 3076312
  have htrace : WordTrace (prefixWord ++ tailWord_3076312) baseStart_3076312 baseEnd_3076312 := by
    simpa [prefixWord, tailWord_3076312, baseEnd_3076312] using wordTrace_append hprefix tailTrace_3076312
  have hstable : (prefixWord ++ tailWord_3076312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076312).length < 2 ^ (prefixWord ++ tailWord_3076312).sum := by decide
  have hdescent : baseEnd_3076312 < baseStart_3076312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076342 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_3076342 : Nat := 118140960795 + 3076342 * 2 ^ 59
def prefixEnd_3076342 : Nat := 4983230072969 + 3 ^ 40 * 3076342 * 2
def baseEnd_3076342 : Nat := 1053094735742605354318111

theorem tailTrace_3076342 : CollatzResearch.WordTrace tailWord_3076342 prefixEnd_3076342 1053094735742605354318111 := by
  unfold tailWord_3076342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012713163809112889355455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74802273747297204153124853 7012713163809112889355455)
  ·
    refine ⟨10519069745713669334033183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7012713163809112889355455 10519069745713669334033183)
    ·
      refine ⟨15778604618570504001049775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10519069745713669334033183 15778604618570504001049775)
      ·
        refine ⟨23667906927855756001574663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15778604618570504001049775 23667906927855756001574663)
        ·
          refine ⟨35501860391783634002361995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23667906927855756001574663 35501860391783634002361995)
          ·
            refine ⟨53252790587675451003542993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35501860391783634002361995 53252790587675451003542993)
            ·
              refine ⟨39939592940756588252657245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53252790587675451003542993 39939592940756588252657245)
              ·
                refine ⟨14977347352783720594746467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39939592940756588252657245 14977347352783720594746467)
                ·
                  refine ⟨22466021029175580892119701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14977347352783720594746467 22466021029175580892119701)
                  ·
                    refine ⟨1053094735742605354318111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22466021029175580892119701 1053094735742605354318111)
                    ·
                      rfl

theorem cell22_3076342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_3076342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076342 prefixEnd_3076342 := by exact prefixLift 3076342
  have htrace : WordTrace (prefixWord ++ tailWord_3076342) baseStart_3076342 baseEnd_3076342 := by
    simpa [prefixWord, tailWord_3076342, baseEnd_3076342] using wordTrace_append hprefix tailTrace_3076342
  have hstable : (prefixWord ++ tailWord_3076342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076342).length < 2 ^ (prefixWord ++ tailWord_3076342).sum := by decide
  have hdescent : baseEnd_3076342 < baseStart_3076342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076436 : List Nat := [2, 4, 1, 1, 2, 3, 3, 1, 5]
def baseStart_3076436 : Nat := 118140960795 + 3076436 * 2 ^ 59
def prefixEnd_3076436 : Nat := 4983230072969 + 3 ^ 40 * 3076436 * 2
def baseEnd_3076436 : Nat := 351042304621206814155941

theorem tailTrace_3076436 : CollatzResearch.WordTrace tailWord_3076436 prefixEnd_3076436 351042304621206814155941 := by
  unfold tailWord_3076436
  simp only [CollatzResearch.WordTrace]
  refine ⟨56103419541302630141804581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74804559388403506855739441 56103419541302630141804581)
  ·
    refine ⟨10519391163994243151588359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56103419541302630141804581 10519391163994243151588359)
    ·
      refine ⟨15779086745991364727382539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10519391163994243151588359 15779086745991364727382539)
      ·
        refine ⟨23668630118987047091073809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15779086745991364727382539 23668630118987047091073809)
        ·
          refine ⟨17751472589240285318305357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23668630118987047091073809 17751472589240285318305357)
          ·
            refine ⟨6656802220965106994364509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17751472589240285318305357 6656802220965106994364509)
            ·
              refine ⟨2496300832861915122886691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6656802220965106994364509 2496300832861915122886691)
              ·
                refine ⟨3744451249292872684330037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2496300832861915122886691 3744451249292872684330037)
                ·
                  refine ⟨351042304621206814155941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3744451249292872684330037 351042304621206814155941)
                  ·
                    rfl

theorem cell22_3076436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_3076436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076436 prefixEnd_3076436 := by exact prefixLift 3076436
  have htrace : WordTrace (prefixWord ++ tailWord_3076436) baseStart_3076436 baseEnd_3076436 := by
    simpa [prefixWord, tailWord_3076436, baseEnd_3076436] using wordTrace_append hprefix tailTrace_3076436
  have hstable : (prefixWord ++ tailWord_3076436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076436).length < 2 ^ (prefixWord ++ tailWord_3076436).sum := by decide
  have hdescent : baseEnd_3076436 < baseStart_3076436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076447 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 6]
def baseStart_3076447 : Nat := 118140960795 + 3076447 * 2 ^ 59
def prefixEnd_3076447 : Nat := 4983230072969 + 3 ^ 40 * 3076447 * 2
def baseEnd_3076447 : Nat := 351043559796140026814263

theorem tailTrace_3076447 : CollatzResearch.WordTrace tailWord_3076447 prefixEnd_3076447 351043559796140026814263 := by
  unfold tailWord_3076447
  simp only [CollatzResearch.WordTrace]
  refine ⟨112207240285565409162259595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74804826857043606108173063 112207240285565409162259595)
  ·
    refine ⟨168310860428348113743389393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112207240285565409162259595 168310860428348113743389393)
    ·
      refine ⟨126233145321261085307542045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168310860428348113743389393 126233145321261085307542045)
      ·
        refine ⟨47337429495472906990328267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126233145321261085307542045 47337429495472906990328267)
        ·
          refine ⟨71006144243209360485492401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47337429495472906990328267 71006144243209360485492401)
          ·
            refine ⟨53254608182407020364119301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71006144243209360485492401 53254608182407020364119301)
            ·
              refine ⟨9985239034201316318272369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53254608182407020364119301 9985239034201316318272369)
              ·
                refine ⟨7488929275650987238704277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9985239034201316318272369 7488929275650987238704277)
                ·
                  refine ⟨351043559796140026814263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7488929275650987238704277 351043559796140026814263)
                  ·
                    rfl

theorem cell22_3076447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 6].length) (baseStart_3076447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076447 prefixEnd_3076447 := by exact prefixLift 3076447
  have htrace : WordTrace (prefixWord ++ tailWord_3076447) baseStart_3076447 baseEnd_3076447 := by
    simpa [prefixWord, tailWord_3076447, baseEnd_3076447] using wordTrace_append hprefix tailTrace_3076447
  have hstable : (prefixWord ++ tailWord_3076447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076447).length < 2 ^ (prefixWord ++ tailWord_3076447).sum := by decide
  have hdescent : baseEnd_3076447 < baseStart_3076447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076481 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 6]
def baseStart_3076481 : Nat := 118140960795 + 3076481 * 2 ^ 59
def prefixEnd_3076481 : Nat := 4983230072969 + 3 ^ 40 * 3076481 * 2
def baseEnd_3076481 : Nat := 351047439427751775030895

theorem tailTrace_3076481 : CollatzResearch.WordTrace tailWord_3076481 prefixEnd_3076481 351047439427751775030895 := by
  unfold tailWord_3076481
  simp only [CollatzResearch.WordTrace]
  refine ⟨112208480367442232968997297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74805653578294821979331531 112208480367442232968997297)
  ·
    refine ⟨84156360275581674726747973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112208480367442232968997297 84156360275581674726747973)
    ·
      refine ⟨15779317551671564011265245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84156360275581674726747973 15779317551671564011265245)
      ·
        refine ⟨5917244081876836504224467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15779317551671564011265245 5917244081876836504224467)
        ·
          refine ⟨8875866122815254756336701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5917244081876836504224467 8875866122815254756336701)
          ·
            refine ⟨3328449796055720533626263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8875866122815254756336701 3328449796055720533626263)
            ·
              refine ⟨4992674694083580800439395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328449796055720533626263 4992674694083580800439395)
              ·
                refine ⟨7489012041125371200659093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4992674694083580800439395 7489012041125371200659093)
                ·
                  refine ⟨351047439427751775030895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7489012041125371200659093 351047439427751775030895)
                  ·
                    rfl

theorem cell22_3076481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 6].length) (baseStart_3076481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076481 prefixEnd_3076481 := by exact prefixLift 3076481
  have htrace : WordTrace (prefixWord ++ tailWord_3076481) baseStart_3076481 baseEnd_3076481 := by
    simpa [prefixWord, tailWord_3076481, baseEnd_3076481] using wordTrace_append hprefix tailTrace_3076481
  have hstable : (prefixWord ++ tailWord_3076481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076481).length < 2 ^ (prefixWord ++ tailWord_3076481).sum := by decide
  have hdescent : baseEnd_3076481 < baseStart_3076481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076492 : List Nat := [2, 2, 1, 2, 1, 4, 1, 9]
def baseStart_3076492 : Nat := 118140960795 + 3076492 * 2 ^ 59
def prefixEnd_3076492 : Nat := 4983230072969 + 3 ^ 40 * 3076492 * 2
def baseEnd_3076492 : Nat := 117016231534228329229739

theorem tailTrace_3076492 : CollatzResearch.WordTrace tailWord_3076492 prefixEnd_3076492 117016231534228329229739 := by
  unfold tailWord_3076492
  simp only [CollatzResearch.WordTrace]
  refine ⟨56104440785201190923823865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74805921046934921231765153 56104440785201190923823865)
  ·
    refine ⟨42078330588900893192867899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56104440785201190923823865 42078330588900893192867899)
    ·
      refine ⟨63117495883351339789301849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42078330588900893192867899 63117495883351339789301849)
      ·
        refine ⟨47338121912513504841976387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63117495883351339789301849 47338121912513504841976387)
        ·
          refine ⟨71007182868770257262964581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47338121912513504841976387 71007182868770257262964581)
          ·
            refine ⟨13313846787894423236805859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71007182868770257262964581 13313846787894423236805859)
            ·
              refine ⟨19970770181841634855208789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13313846787894423236805859 19970770181841634855208789)
              ·
                refine ⟨117016231534228329229739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19970770181841634855208789 117016231534228329229739)
                ·
                  rfl

theorem cell22_3076492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 9].length) (baseStart_3076492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076492 prefixEnd_3076492 := by exact prefixLift 3076492
  have htrace : WordTrace (prefixWord ++ tailWord_3076492) baseStart_3076492 baseEnd_3076492 := by
    simpa [prefixWord, tailWord_3076492, baseEnd_3076492] using wordTrace_append hprefix tailTrace_3076492
  have hstable : (prefixWord ++ tailWord_3076492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076492).length < 2 ^ (prefixWord ++ tailWord_3076492).sum := by decide
  have hdescent : baseEnd_3076492 < baseStart_3076492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076500 : List Nat := [2, 4, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_3076500 : Nat := 118140960795 + 3076500 * 2 ^ 59
def prefixEnd_3076500 : Nat := 4983230072969 + 3 ^ 40 * 3076500 * 2
def baseEnd_3076500 : Nat := 1053148822371545608867627

theorem tailTrace_3076500 : CollatzResearch.WordTrace tailWord_3076500 prefixEnd_3076500 1053148822371545608867627 := by
  unfold tailWord_3076500
  simp only [CollatzResearch.WordTrace]
  refine ⟨56104586677186699606969477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74806115569582266142625969 56104586677186699606969477)
  ·
    refine ⟨10519610001972506176306777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56104586677186699606969477 10519610001972506176306777)
    ·
      refine ⟨7889707501479379632230083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10519610001972506176306777 7889707501479379632230083)
      ·
        refine ⟨11834561252219069448345125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7889707501479379632230083 11834561252219069448345125)
        ·
          refine ⟨2218980234791075521564711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11834561252219069448345125 2218980234791075521564711)
          ·
            refine ⟨3328470352186613282347067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218980234791075521564711 3328470352186613282347067)
            ·
              refine ⟨4992705528279919923520601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328470352186613282347067 4992705528279919923520601)
              ·
                refine ⟨3744529146209939942640451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4992705528279919923520601 3744529146209939942640451)
                ·
                  refine ⟨5616793719314909913960677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3744529146209939942640451 5616793719314909913960677)
                  ·
                    refine ⟨1053148822371545608867627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5616793719314909913960677 1053148822371545608867627)
                    ·
                      rfl

theorem cell22_3076500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_3076500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076500 prefixEnd_3076500 := by exact prefixLift 3076500
  have htrace : WordTrace (prefixWord ++ tailWord_3076500) baseStart_3076500 baseEnd_3076500 := by
    simpa [prefixWord, tailWord_3076500, baseEnd_3076500] using wordTrace_append hprefix tailTrace_3076500
  have hstable : (prefixWord ++ tailWord_3076500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076500).length < 2 ^ (prefixWord ++ tailWord_3076500).sum := by decide
  have hdescent : baseEnd_3076500 < baseStart_3076500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076554 : List Nat := [3, 1, 2, 1, 2, 2, 1, 5, 5]
def baseStart_3076554 : Nat := 118140960795 + 3076554 * 2 ^ 59
def prefixEnd_3076554 : Nat := 4983230072969 + 3 ^ 40 * 3076554 * 2
def baseEnd_3076554 : Nat := 351055769225035822672487

theorem tailTrace_3076554 : CollatzResearch.WordTrace tailWord_3076554 prefixEnd_3076554 351055769225035822672487 := by
  unfold tailWord_3076554
  simp only [CollatzResearch.WordTrace]
  refine ⟨28052785724044441609101179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74807428597451844290936477 28052785724044441609101179)
  ·
    refine ⟨42079178586066662413651769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28052785724044441609101179 42079178586066662413651769)
    ·
      refine ⟨31559383939549996810238827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42079178586066662413651769 31559383939549996810238827)
      ·
        refine ⟨47339075909324995215358241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31559383939549996810238827 47339075909324995215358241)
        ·
          refine ⟨35504306931993746411518681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47339075909324995215358241 35504306931993746411518681)
          ·
            refine ⟨26628230198995309808639011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35504306931993746411518681 26628230198995309808639011)
            ·
              refine ⟨39942345298492964712958517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26628230198995309808639011 39942345298492964712958517)
              ·
                refine ⟨3744594871733715441839861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39942345298492964712958517 3744594871733715441839861)
                ·
                  refine ⟨351055769225035822672487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3744594871733715441839861 351055769225035822672487)
                  ·
                    rfl

theorem cell22_3076554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_3076554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076554 prefixEnd_3076554 := by exact prefixLift 3076554
  have htrace : WordTrace (prefixWord ++ tailWord_3076554) baseStart_3076554 baseEnd_3076554 := by
    simpa [prefixWord, tailWord_3076554, baseEnd_3076554] using wordTrace_append hprefix tailTrace_3076554
  have hstable : (prefixWord ++ tailWord_3076554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076554).length < 2 ^ (prefixWord ++ tailWord_3076554).sum := by decide
  have hdescent : baseEnd_3076554 < baseStart_3076554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076629 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_3076629 : Nat := 118140960795 + 3076629 * 2 ^ 59
def prefixEnd_3076629 : Nat := 4983230072969 + 3 ^ 40 * 3076629 * 2
def baseEnd_3076629 : Nat := 1053192981707832272392231

theorem tailTrace_3076629 : CollatzResearch.WordTrace tailWord_3076629 prefixEnd_3076629 1053192981707832272392231 := by
  unfold tailWord_3076629
  simp only [CollatzResearch.WordTrace]
  refine ⟨112213878370906054245384941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74809252247270702830256627 112213878370906054245384941)
  ·
    refine ⟨42080204389089770342019353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112213878370906054245384941 42080204389089770342019353)
    ·
      refine ⟨31560153291817327756514515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42080204389089770342019353 31560153291817327756514515)
      ·
        refine ⟨47340229937725991634771773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31560153291817327756514515 47340229937725991634771773)
        ·
          refine ⟨17752586226647246863039415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47340229937725991634771773 17752586226647246863039415)
          ·
            refine ⟨26628879339970870294559123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17752586226647246863039415 26628879339970870294559123)
            ·
              refine ⟨39943319009956305441838685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26628879339970870294559123 39943319009956305441838685)
              ·
                refine ⟨14978744628733614540689507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39943319009956305441838685 14978744628733614540689507)
                ·
                  refine ⟨22468116943100421811034261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14978744628733614540689507 22468116943100421811034261)
                  ·
                    refine ⟨1053192981707832272392231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22468116943100421811034261 1053192981707832272392231)
                    ·
                      rfl

theorem cell22_3076629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_3076629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076629 prefixEnd_3076629 := by exact prefixLift 3076629
  have htrace : WordTrace (prefixWord ++ tailWord_3076629) baseStart_3076629 baseEnd_3076629 := by
    simpa [prefixWord, tailWord_3076629, baseEnd_3076629] using wordTrace_append hprefix tailTrace_3076629
  have hstable : (prefixWord ++ tailWord_3076629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076629).length < 2 ^ (prefixWord ++ tailWord_3076629).sum := by decide
  have hdescent : baseEnd_3076629 < baseStart_3076629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076648 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 4, 3]
def baseStart_3076648 : Nat := 118140960795 + 3076648 * 2 ^ 59
def prefixEnd_3076648 : Nat := 4983230072969 + 3 ^ 40 * 3076648 * 2
def baseEnd_3076648 : Nat := 1053199485796122556167173

theorem tailTrace_3076648 : CollatzResearch.WordTrace tailWord_3076648 prefixEnd_3076648 1053199485796122556167173 := by
  unfold tailWord_3076648
  simp only [CollatzResearch.WordTrace]
  refine ⟨56107285678918610245163299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74809714238558146993551065 56107285678918610245163299)
  ·
    refine ⟨84160928518377915367744949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56107285678918610245163299 84160928518377915367744949)
    ·
      refine ⟨7890087048597929565726089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84160928518377915367744949 7890087048597929565726089)
      ·
        refine ⟨5917565286448447174294567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7890087048597929565726089 5917565286448447174294567)
        ·
          refine ⟨8876347929672670761441851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5917565286448447174294567 8876347929672670761441851)
          ·
            refine ⟨13314521894509006142162777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8876347929672670761441851 13314521894509006142162777)
            ·
              refine ⟨9985891420881754606622083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13314521894509006142162777 9985891420881754606622083)
              ·
                refine ⟨14978837131322631909933125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9985891420881754606622083 14978837131322631909933125)
                ·
                  refine ⟨2808531962122993483112461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14978837131322631909933125 2808531962122993483112461)
                  ·
                    refine ⟨1053199485796122556167173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2808531962122993483112461 1053199485796122556167173)
                    ·
                      rfl

theorem cell22_3076648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_3076648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076648 prefixEnd_3076648 := by exact prefixLift 3076648
  have htrace : WordTrace (prefixWord ++ tailWord_3076648) baseStart_3076648 baseEnd_3076648 := by
    simpa [prefixWord, tailWord_3076648, baseEnd_3076648] using wordTrace_append hprefix tailTrace_3076648
  have hstable : (prefixWord ++ tailWord_3076648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076648).length < 2 ^ (prefixWord ++ tailWord_3076648).sum := by decide
  have hdescent : baseEnd_3076648 < baseStart_3076648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076650 : List Nat := [3, 1, 4, 1, 1, 3, 3, 2, 4]
def baseStart_3076650 : Nat := 118140960795 + 3076650 * 2 ^ 59
def prefixEnd_3076650 : Nat := 4983230072969 + 3 ^ 40 * 3076650 * 2
def baseEnd_3076650 : Nat := 351066723478998405872389

theorem tailTrace_3076650 : CollatzResearch.WordTrace tailWord_3076650 prefixEnd_3076650 351066723478998405872389 := by
  unfold tailWord_3076650
  simp only [CollatzResearch.WordTrace]
  refine ⟨28053661075957493707974851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74809762869219983221266269 28053661075957493707974851)
  ·
    refine ⟨42080491613936240561962277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28053661075957493707974851 42080491613936240561962277)
    ·
      refine ⟨7890092177613045105367927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42080491613936240561962277 7890092177613045105367927)
      ·
        refine ⟨11835138266419567658051891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7890092177613045105367927 11835138266419567658051891)
        ·
          refine ⟨17752707399629351487077837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11835138266419567658051891 17752707399629351487077837)
          ·
            refine ⟨6657265274861006807654189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17752707399629351487077837 6657265274861006807654189)
            ·
              refine ⟨2496474478072877552870321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6657265274861006807654189 2496474478072877552870321)
              ·
                refine ⟨1872355858554658164652741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2496474478072877552870321 1872355858554658164652741)
                ·
                  refine ⟨351066723478998405872389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1872355858554658164652741 351066723478998405872389)
                  ·
                    rfl

theorem cell22_3076650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_3076650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076650 prefixEnd_3076650 := by exact prefixLift 3076650
  have htrace : WordTrace (prefixWord ++ tailWord_3076650) baseStart_3076650 baseEnd_3076650 := by
    simpa [prefixWord, tailWord_3076650, baseEnd_3076650] using wordTrace_append hprefix tailTrace_3076650
  have hstable : (prefixWord ++ tailWord_3076650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076650).length < 2 ^ (prefixWord ++ tailWord_3076650).sum := by decide
  have hdescent : baseEnd_3076650 < baseStart_3076650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076678 : List Nat := [6, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3076678 : Nat := 118140960795 + 3076678 * 2 ^ 59
def prefixEnd_3076678 : Nat := 4983230072969 + 3 ^ 40 * 3076678 * 2
def baseEnd_3076678 : Nat := 117023306156579164213009

theorem tailTrace_3076678 : CollatzResearch.WordTrace tailWord_3076678 prefixEnd_3076678 117023306156579164213009 := by
  unfold tailWord_3076678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3506739548366516737934959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74810443698485690409279125 3506739548366516737934959)
  ·
    refine ⟨5260109322549775106902439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3506739548366516737934959 5260109322549775106902439)
    ·
      refine ⟨7890163983824662660353659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5260109322549775106902439 7890163983824662660353659)
      ·
        refine ⟨11835245975736993990530489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7890163983824662660353659 11835245975736993990530489)
        ·
          refine ⟨8876434481802745492897867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11835245975736993990530489 8876434481802745492897867)
          ·
            refine ⟨13314651722704118239346801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8876434481802745492897867 13314651722704118239346801)
            ·
              refine ⟨9985988792028088679510101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13314651722704118239346801 9985988792028088679510101)
              ·
                refine ⟨117023306156579164213009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9985988792028088679510101 117023306156579164213009)
                ·
                  rfl

theorem cell22_3076678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3076678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076678 prefixEnd_3076678 := by exact prefixLift 3076678
  have htrace : WordTrace (prefixWord ++ tailWord_3076678) baseStart_3076678 baseEnd_3076678 := by
    simpa [prefixWord, tailWord_3076678, baseEnd_3076678] using wordTrace_append hprefix tailTrace_3076678
  have hstable : (prefixWord ++ tailWord_3076678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076678).length < 2 ^ (prefixWord ++ tailWord_3076678).sum := by decide
  have hdescent : baseEnd_3076678 < baseStart_3076678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076736 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 3, 4]
def baseStart_3076736 : Nat := 118140960795 + 3076736 * 2 ^ 59
def prefixEnd_3076736 : Nat := 4983230072969 + 3 ^ 40 * 3076736 * 2
def baseEnd_3076736 : Nat := 1053229609994519659966903

theorem tailTrace_3076736 : CollatzResearch.WordTrace tailWord_3076736 prefixEnd_3076736 1053229609994519659966903 := by
  unfold tailWord_3076736
  simp only [CollatzResearch.WordTrace]
  refine ⟨56108890490759205759765031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74811853987678941013020041 56108890490759205759765031)
  ·
    refine ⟨84163335736138808639647547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56108890490759205759765031 84163335736138808639647547)
    ·
      refine ⟨126245003604208212959471321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84163335736138808639647547 126245003604208212959471321)
      ·
        refine ⟨94683752703156159719603491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126245003604208212959471321 94683752703156159719603491)
        ·
          refine ⟨142025629054734239579405237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94683752703156159719603491 142025629054734239579405237)
          ·
            refine ⟨13314902723881334960569241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142025629054734239579405237 13314902723881334960569241)
            ·
              refine ⟨9986177042911001220426931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13314902723881334960569241 9986177042911001220426931)
              ·
                refine ⟨14979265564366501830640397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9986177042911001220426931 14979265564366501830640397)
                ·
                  refine ⟨5617224586637438186490149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14979265564366501830640397 5617224586637438186490149)
                  ·
                    refine ⟨1053229609994519659966903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5617224586637438186490149 1053229609994519659966903)
                    ·
                      rfl

theorem cell22_3076736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_3076736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076736 prefixEnd_3076736 := by exact prefixLift 3076736
  have htrace : WordTrace (prefixWord ++ tailWord_3076736) baseStart_3076736 baseEnd_3076736 := by
    simpa [prefixWord, tailWord_3076736, baseEnd_3076736] using wordTrace_append hprefix tailTrace_3076736
  have hstable : (prefixWord ++ tailWord_3076736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076736).length < 2 ^ (prefixWord ++ tailWord_3076736).sum := by decide
  have hdescent : baseEnd_3076736 < baseStart_3076736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076768 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 6]
def baseStart_3076768 : Nat := 118140960795 + 3076768 * 2 ^ 59
def prefixEnd_3076768 : Nat := 4983230072969 + 3 ^ 40 * 3076768 * 2
def baseEnd_3076768 : Nat := 351080188082827414388935

theorem tailTrace_3076768 : CollatzResearch.WordTrace tailWord_3076768 prefixEnd_3076768 351080188082827414388935 := by
  unfold tailWord_3076768
  simp only [CollatzResearch.WordTrace]
  refine ⟨56109474058701240492347479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74812632078268320656463305 56109474058701240492347479)
  ·
    refine ⟨84164211088051860738521219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56109474058701240492347479 84164211088051860738521219)
    ·
      refine ⟨126246316632077791107781829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84164211088051860738521219 126246316632077791107781829)
      ·
        refine ⟨23671184368514585832709093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126246316632077791107781829 23671184368514585832709093)
        ·
          refine ⟨4438347069096484843632955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23671184368514585832709093 4438347069096484843632955)
          ·
            refine ⟨6657520603644727265449433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438347069096484843632955 6657520603644727265449433)
            ·
              refine ⟨4993140452733545449087075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6657520603644727265449433 4993140452733545449087075)
              ·
                refine ⟨7489710679100318173630613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4993140452733545449087075 7489710679100318173630613)
                ·
                  refine ⟨351080188082827414388935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7489710679100318173630613 351080188082827414388935)
                  ·
                    rfl

theorem cell22_3076768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 6].length) (baseStart_3076768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076768 prefixEnd_3076768 := by exact prefixLift 3076768
  have htrace : WordTrace (prefixWord ++ tailWord_3076768) baseStart_3076768 baseEnd_3076768 := by
    simpa [prefixWord, tailWord_3076768, baseEnd_3076768] using wordTrace_append hprefix tailTrace_3076768
  have hstable : (prefixWord ++ tailWord_3076768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076768).length < 2 ^ (prefixWord ++ tailWord_3076768).sum := by decide
  have hdescent : baseEnd_3076768 < baseStart_3076768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076783 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 1, 5]
def baseStart_3076783 : Nat := 118140960795 + 3076783 * 2 ^ 59
def prefixEnd_3076783 : Nat := 4983230072969 + 3 ^ 40 * 3076783 * 2
def baseEnd_3076783 : Nat := 1053245699055027204041759

theorem tailTrace_3076783 : CollatzResearch.WordTrace tailWord_3076783 prefixEnd_3076783 1053245699055027204041759 := by
  unfold tailWord_3076783
  simp only [CollatzResearch.WordTrace]
  refine ⟨112219495212348138546491003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74812996808232092364327335 112219495212348138546491003)
  ·
    refine ⟨168329242818522207819736505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112219495212348138546491003 168329242818522207819736505)
    ·
      refine ⟨126246932113891655864802379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168329242818522207819736505 126246932113891655864802379)
      ·
        refine ⟨189370398170837483797203569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126246932113891655864802379 189370398170837483797203569)
        ·
          refine ⟨142027798628128112847902677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189370398170837483797203569 142027798628128112847902677)
          ·
            refine ⟨3328776530346752644872719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 142027798628128112847902677 3328776530346752644872719)
            ·
              refine ⟨4993164795520128967309079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328776530346752644872719 4993164795520128967309079)
              ·
                refine ⟨7489747193280193450963619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4993164795520128967309079 7489747193280193450963619)
                ·
                  refine ⟨11234620789920290176445429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7489747193280193450963619 11234620789920290176445429)
                  ·
                    refine ⟨1053245699055027204041759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11234620789920290176445429 1053245699055027204041759)
                    ·
                      rfl

theorem cell22_3076783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 5].length) (baseStart_3076783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076783 prefixEnd_3076783 := by exact prefixLift 3076783
  have htrace : WordTrace (prefixWord ++ tailWord_3076783) baseStart_3076783 baseEnd_3076783 := by
    simpa [prefixWord, tailWord_3076783, baseEnd_3076783] using wordTrace_append hprefix tailTrace_3076783
  have hstable : (prefixWord ++ tailWord_3076783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076783).length < 2 ^ (prefixWord ++ tailWord_3076783).sum := by decide
  have hdescent : baseEnd_3076783 < baseStart_3076783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076796 : List Nat := [2, 2, 2, 3, 1, 1, 3, 8]
def baseStart_3076796 : Nat := 118140960795 + 3076796 * 2 ^ 59
def prefixEnd_3076796 : Nat := 4983230072969 + 3 ^ 40 * 3076796 * 2
def baseEnd_3076796 : Nat := 117027794357855500385191

theorem tailTrace_3076796 : CollatzResearch.WordTrace tailWord_3076796 prefixEnd_3076796 117027794357855500385191 := by
  unfold tailWord_3076796
  simp only [CollatzResearch.WordTrace]
  refine ⟨56109984680650520883357121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74813312907534027844476161 56109984680650520883357121)
  ·
    refine ⟨42082488510487890662517841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56109984680650520883357121 42082488510487890662517841)
    ·
      refine ⟨31561866382865917996888381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42082488510487890662517841 31561866382865917996888381)
      ·
        refine ⟨11835699893574719248833143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31561866382865917996888381 11835699893574719248833143)
        ·
          refine ⟨17753549840362078873249715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11835699893574719248833143 17753549840362078873249715)
          ·
            refine ⟨26630324760543118309874573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17753549840362078873249715 26630324760543118309874573)
            ·
              refine ⟨9986371785203669366202965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26630324760543118309874573 9986371785203669366202965)
              ·
                refine ⟨117027794357855500385191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9986371785203669366202965 117027794357855500385191)
                ·
                  rfl

theorem cell22_3076796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 8].length) (baseStart_3076796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076796 prefixEnd_3076796 := by exact prefixLift 3076796
  have htrace : WordTrace (prefixWord ++ tailWord_3076796) baseStart_3076796 baseEnd_3076796 := by
    simpa [prefixWord, tailWord_3076796, baseEnd_3076796] using wordTrace_append hprefix tailTrace_3076796
  have hstable : (prefixWord ++ tailWord_3076796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076796).length < 2 ^ (prefixWord ++ tailWord_3076796).sum := by decide
  have hdescent : baseEnd_3076796 < baseStart_3076796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076798 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_3076798 : Nat := 118140960795 + 3076798 * 2 ^ 59
def prefixEnd_3076798 : Nat := 4983230072969 + 3 ^ 40 * 3076798 * 2
def baseEnd_3076798 : Nat := 1053250833861572164916713

theorem tailTrace_3076798 : CollatzResearch.WordTrace tailWord_3076798 prefixEnd_3076798 1053250833861572164916713 := by
  unfold tailWord_3076798
  simp only [CollatzResearch.WordTrace]
  refine ⟨14027505288411724513535881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74813361538195864072191365 14027505288411724513535881)
  ·
    refine ⟨10520628966308793385151911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14027505288411724513535881 10520628966308793385151911)
    ·
      refine ⟨15780943449463190077727867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10520628966308793385151911 15780943449463190077727867)
      ·
        refine ⟨23671415174194785116591801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15780943449463190077727867 23671415174194785116591801)
        ·
          refine ⟨17753561380646088837443851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23671415174194785116591801 17753561380646088837443851)
          ·
            refine ⟨26630342070969133256165777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17753561380646088837443851 26630342070969133256165777)
            ·
              refine ⟨19972756553226849942124333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26630342070969133256165777 19972756553226849942124333)
              ·
                refine ⟨7489783707460068728296625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19972756553226849942124333 7489783707460068728296625)
                ·
                  refine ⟨5617337780595051546222469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7489783707460068728296625 5617337780595051546222469)
                  ·
                    refine ⟨1053250833861572164916713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5617337780595051546222469 1053250833861572164916713)
                    ·
                      rfl

theorem cell22_3076798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_3076798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076798 prefixEnd_3076798 := by exact prefixLift 3076798
  have htrace : WordTrace (prefixWord ++ tailWord_3076798) baseStart_3076798 baseEnd_3076798 := by
    simpa [prefixWord, tailWord_3076798, baseEnd_3076798] using wordTrace_append hprefix tailTrace_3076798
  have hstable : (prefixWord ++ tailWord_3076798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076798).length < 2 ^ (prefixWord ++ tailWord_3076798).sum := by decide
  have hdescent : baseEnd_3076798 < baseStart_3076798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076826 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_3076826 : Nat := 118140960795 + 3076826 * 2 ^ 59
def prefixEnd_3076826 : Nat := 4983230072969 + 3 ^ 40 * 3076826 * 2
def baseEnd_3076826 : Nat := 1053260418833789425216627

theorem tailTrace_3076826 : CollatzResearch.WordTrace tailWord_3076826 prefixEnd_3076826 1053260418833789425216627 := by
  unfold tailWord_3076826
  simp only [CollatzResearch.WordTrace]
  refine ⟨28055265887798089222576583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74814042367461571260204221 28055265887798089222576583)
  ·
    refine ⟨42082898831697133833864875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28055265887798089222576583 42082898831697133833864875)
    ·
      refine ⟨63124348247545700750797313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42082898831697133833864875 63124348247545700750797313)
      ·
        refine ⟨47343261185659275563097985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63124348247545700750797313 47343261185659275563097985)
        ·
          refine ⟨35507445889244456672323489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47343261185659275563097985 35507445889244456672323489)
          ·
            refine ⟨26630584416933342504242617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35507445889244456672323489 26630584416933342504242617)
            ·
              refine ⟨19972938312700006878181963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26630584416933342504242617 19972938312700006878181963)
              ·
                refine ⟨29959407469050010317272945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19972938312700006878181963 29959407469050010317272945)
                ·
                  refine ⟨22469555601787507737954709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29959407469050010317272945 22469555601787507737954709)
                  ·
                    refine ⟨1053260418833789425216627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22469555601787507737954709 1053260418833789425216627)
                    ·
                      rfl

theorem cell22_3076826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_3076826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076826 prefixEnd_3076826 := by exact prefixLift 3076826
  have htrace : WordTrace (prefixWord ++ tailWord_3076826) baseStart_3076826 baseEnd_3076826 := by
    simpa [prefixWord, tailWord_3076826, baseEnd_3076826] using wordTrace_append hprefix tailTrace_3076826
  have hstable : (prefixWord ++ tailWord_3076826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076826).length < 2 ^ (prefixWord ++ tailWord_3076826).sum := by decide
  have hdescent : baseEnd_3076826 < baseStart_3076826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076920 : List Nat := [2, 1, 2, 1, 3, 2, 4, 3, 4]
def baseStart_3076920 : Nat := 118140960795 + 3076920 * 2 ^ 59
def prefixEnd_3076920 : Nat := 4983230072969 + 3 ^ 40 * 3076920 * 2
def baseEnd_3076920 : Nat := 351097532318268171122113

theorem tailTrace_3076920 : CollatzResearch.WordTrace tailWord_3076920 prefixEnd_3076920 351097532318268171122113 := by
  unfold tailWord_3076920
  simp only [CollatzResearch.WordTrace]
  refine ⟨56112246006425905472114107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74816328008567873962818809 56112246006425905472114107)
  ·
    refine ⟨84168369009638858208171161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56112246006425905472114107 84168369009638858208171161)
    ·
      refine ⟨63126276757229143656128371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84168369009638858208171161 63126276757229143656128371)
      ·
        refine ⟨94689415135843715484192557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63126276757229143656128371 94689415135843715484192557)
        ·
          refine ⟨35508530675941393306572209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94689415135843715484192557 35508530675941393306572209)
          ·
            refine ⟨26631398006956044979929157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35508530675941393306572209 26631398006956044979929157)
            ·
              refine ⟨4993387126304258433736717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26631398006956044979929157 4993387126304258433736717)
              ·
                refine ⟨1872520172364096912651269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4993387126304258433736717 1872520172364096912651269)
                ·
                  refine ⟨351097532318268171122113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1872520172364096912651269 351097532318268171122113)
                  ·
                    rfl

theorem cell22_3076920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 4].length) (baseStart_3076920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076920 prefixEnd_3076920 := by exact prefixLift 3076920
  have htrace : WordTrace (prefixWord ++ tailWord_3076920) baseStart_3076920 baseEnd_3076920 := by
    simpa [prefixWord, tailWord_3076920, baseEnd_3076920] using wordTrace_append hprefix tailTrace_3076920
  have hstable : (prefixWord ++ tailWord_3076920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076920).length < 2 ^ (prefixWord ++ tailWord_3076920).sum := by decide
  have hdescent : baseEnd_3076920 < baseStart_3076920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076931 : List Nat := [1, 1, 1, 3, 1, 4, 11]
def baseStart_3076931 : Nat := 118140960795 + 3076931 * 2 ^ 59
def prefixEnd_3076931 : Nat := 4983230072969 + 3 ^ 40 * 3076931 * 2
def baseEnd_3076931 : Nat := 39010976388133487086715

theorem tailTrace_3076931 : CollatzResearch.WordTrace tailWord_3076931 prefixEnd_3076931 39010976388133487086715 := by
  unfold tailWord_3076931
  simp only [CollatzResearch.WordTrace]
  refine ⟨112224893215811959822878647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74816595477207973215252431 112224893215811959822878647)
  ·
    refine ⟨168337339823717939734317971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112224893215811959822878647 168337339823717939734317971)
    ·
      refine ⟨252506009735576909601476957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168337339823717939734317971 252506009735576909601476957)
      ·
        refine ⟨94689753650841341100553859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252506009735576909601476957 94689753650841341100553859)
        ·
          refine ⟨142034630476262011650830789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94689753650841341100553859 142034630476262011650830789)
          ·
            refine ⟨26631493214299127184530773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142034630476262011650830789 26631493214299127184530773)
            ·
              refine ⟨39010976388133487086715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26631493214299127184530773 39010976388133487086715)
              ·
                rfl

theorem cell22_3076931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 11].length) (baseStart_3076931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076931 prefixEnd_3076931 := by exact prefixLift 3076931
  have htrace : WordTrace (prefixWord ++ tailWord_3076931) baseStart_3076931 baseEnd_3076931 := by
    simpa [prefixWord, tailWord_3076931, baseEnd_3076931] using wordTrace_append hprefix tailTrace_3076931
  have hstable : (prefixWord ++ tailWord_3076931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076931).length < 2 ^ (prefixWord ++ tailWord_3076931).sum := by decide
  have hdescent : baseEnd_3076931 < baseStart_3076931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076997 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 3, 3]
def baseStart_3076997 : Nat := 118140960795 + 3076997 * 2 ^ 59
def prefixEnd_3076997 : Nat := 4983230072969 + 3 ^ 40 * 3076997 * 2
def baseEnd_3076997 : Nat := 1053318955628401979191103

theorem tailTrace_3076997 : CollatzResearch.WordTrace tailWord_3076997 prefixEnd_3076997 1053318955628401979191103 := by
  unfold tailWord_3076997
  simp only [CollatzResearch.WordTrace]
  refine ⟨112227300433572853094781245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74818200289048568729854163 112227300433572853094781245)
  ·
    refine ⟨42085237662589819910542967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112227300433572853094781245 42085237662589819910542967)
    ·
      refine ⟨63127856493884729865814451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42085237662589819910542967 63127856493884729865814451)
      ·
        refine ⟨94691784740827094798721677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63127856493884729865814451 94691784740827094798721677)
        ·
          refine ⟨35509419277810160549520629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94691784740827094798721677 35509419277810160549520629)
          ·
            refine ⟨3329008057294702551517559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35509419277810160549520629 3329008057294702551517559)
            ·
              refine ⟨4993512085942053827276339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3329008057294702551517559 4993512085942053827276339)
              ·
                refine ⟨7490268128913080740914509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4993512085942053827276339 7490268128913080740914509)
                ·
                  refine ⟨2808850548342405277842941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7490268128913080740914509 2808850548342405277842941)
                  ·
                    refine ⟨1053318955628401979191103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2808850548342405277842941 1053318955628401979191103)
                    ·
                      rfl

theorem cell22_3076997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_3076997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3076997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3076997 prefixEnd_3076997 := by exact prefixLift 3076997
  have htrace : WordTrace (prefixWord ++ tailWord_3076997) baseStart_3076997 baseEnd_3076997 := by
    simpa [prefixWord, tailWord_3076997, baseEnd_3076997] using wordTrace_append hprefix tailTrace_3076997
  have hstable : (prefixWord ++ tailWord_3076997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076997).length < 2 ^ (prefixWord ++ tailWord_3076997).sum := by decide
  have hdescent : baseEnd_3076997 < baseStart_3076997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077044 : List Nat := [2, 5, 2, 1, 1, 2, 2, 2, 5]
def baseStart_3077044 : Nat := 118140960795 + 3077044 * 2 ^ 59
def prefixEnd_3077044 : Nat := 4983230072969 + 3 ^ 40 * 3077044 * 2
def baseEnd_3077044 : Nat := 351111681562969841088653

theorem tailTrace_3077044 : CollatzResearch.WordTrace tailWord_3077044 prefixEnd_3077044 351111681562969841088653 := by
  unfold tailWord_3077044
  simp only [CollatzResearch.WordTrace]
  refine ⟨56114507332201290060871093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74819343109601720081161457 56114507332201290060871093)
  ·
    refine ⟨5260735062393870943206665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56114507332201290060871093 5260735062393870943206665)
    ·
      refine ⟨3945551296795403207404999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5260735062393870943206665 3945551296795403207404999)
      ·
        refine ⟨5918326945193104811107499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3945551296795403207404999 5918326945193104811107499)
        ·
          refine ⟨8877490417789657216661249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5918326945193104811107499 8877490417789657216661249)
          ·
            refine ⟨6658117813342242912495937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8877490417789657216661249 6658117813342242912495937)
            ·
              refine ⟨4993588360006682184371953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6658117813342242912495937 4993588360006682184371953)
              ·
                refine ⟨3745191270005011638278965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4993588360006682184371953 3745191270005011638278965)
                ·
                  refine ⟨351111681562969841088653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3745191270005011638278965 351111681562969841088653)
                  ·
                    rfl

theorem cell22_3077044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_3077044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077044 prefixEnd_3077044 := by exact prefixLift 3077044
  have htrace : WordTrace (prefixWord ++ tailWord_3077044) baseStart_3077044 baseEnd_3077044 := by
    simpa [prefixWord, tailWord_3077044, baseEnd_3077044] using wordTrace_append hprefix tailTrace_3077044
  have hstable : (prefixWord ++ tailWord_3077044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077044).length < 2 ^ (prefixWord ++ tailWord_3077044).sum := by decide
  have hdescent : baseEnd_3077044 < baseStart_3077044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077070 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_3077070 : Nat := 118140960795 + 3077070 * 2 ^ 59
def prefixEnd_3077070 : Nat := 4983230072969 + 3 ^ 40 * 3077070 * 2
def baseEnd_3077070 : Nat := 1053343945020254122115879

theorem tailTrace_3077070 : CollatzResearch.WordTrace tailWord_3077070 prefixEnd_3077070 1053343945020254122115879 := by
  unfold tailWord_3077070
  simp only [CollatzResearch.WordTrace]
  refine ⟨14028745370288548320273583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74819975308205591041459109 14028745370288548320273583)
  ·
    refine ⟨21043118055432822480410375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14028745370288548320273583 21043118055432822480410375)
    ·
      refine ⟨31564677083149233720615563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21043118055432822480410375 31564677083149233720615563)
      ·
        refine ⟨47347015624723850580923345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31564677083149233720615563 47347015624723850580923345)
        ·
          refine ⟨35510261718542887935692509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47347015624723850580923345 35510261718542887935692509)
          ·
            refine ⟨13316348144453582975884691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35510261718542887935692509 13316348144453582975884691)
            ·
              refine ⟨19974522216680374463827037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13316348144453582975884691 19974522216680374463827037)
              ·
                refine ⟨7490445831255140423935139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19974522216680374463827037 7490445831255140423935139)
                ·
                  refine ⟨11235668746882710635902709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7490445831255140423935139 11235668746882710635902709)
                  ·
                    refine ⟨1053343945020254122115879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11235668746882710635902709 1053343945020254122115879)
                    ·
                      rfl

theorem cell22_3077070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_3077070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077070 prefixEnd_3077070 := by exact prefixLift 3077070
  have htrace : WordTrace (prefixWord ++ tailWord_3077070) baseStart_3077070 baseEnd_3077070 := by
    simpa [prefixWord, tailWord_3077070, baseEnd_3077070] using wordTrace_append hprefix tailTrace_3077070
  have hstable : (prefixWord ++ tailWord_3077070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077070).length < 2 ^ (prefixWord ++ tailWord_3077070).sum := by decide
  have hdescent : baseEnd_3077070 < baseStart_3077070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077132 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 3, 3]
def baseStart_3077132 : Nat := 118140960795 + 3077132 * 2 ^ 59
def prefixEnd_3077132 : Nat := 4983230072969 + 3 ^ 40 * 3077132 * 2
def baseEnd_3077132 : Nat := 1053365168887306627065689

theorem tailTrace_3077132 : CollatzResearch.WordTrace tailWord_3077132 prefixEnd_3077132 1053365168887306627065689 := by
  unfold tailWord_3077132
  simp only [CollatzResearch.WordTrace]
  refine ⟨56116112144041885575472825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74821482858722514100630433 56116112144041885575472825)
  ·
    refine ⟨42087084108031414181604619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56116112144041885575472825 42087084108031414181604619)
    ·
      refine ⟨63130626162047121272406929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42087084108031414181604619 63130626162047121272406929)
      ·
        refine ⟨47347969621535340954305197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63130626162047121272406929 47347969621535340954305197)
        ·
          refine ⟨17755488608075752857864449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47347969621535340954305197 17755488608075752857864449)
          ·
            refine ⟨13316616456056814643398337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17755488608075752857864449 13316616456056814643398337)
            ·
              refine ⟨9987462342042610982548753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13316616456056814643398337 9987462342042610982548753)
              ·
                refine ⟨7490596756531958236911565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9987462342042610982548753 7490596756531958236911565)
                ·
                  refine ⟨2808973783699484338841837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7490596756531958236911565 2808973783699484338841837)
                  ·
                    refine ⟨1053365168887306627065689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2808973783699484338841837 1053365168887306627065689)
                    ·
                      rfl

theorem cell22_3077132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_3077132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077132 prefixEnd_3077132 := by exact prefixLift 3077132
  have htrace : WordTrace (prefixWord ++ tailWord_3077132) baseStart_3077132 baseEnd_3077132 := by
    simpa [prefixWord, tailWord_3077132, baseEnd_3077132] using wordTrace_append hprefix tailTrace_3077132
  have hstable : (prefixWord ++ tailWord_3077132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077132).length < 2 ^ (prefixWord ++ tailWord_3077132).sum := by decide
  have hdescent : baseEnd_3077132 < baseStart_3077132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077175 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 3, 4]
def baseStart_3077175 : Nat := 118140960795 + 3077175 * 2 ^ 59
def prefixEnd_3077175 : Nat := 4983230072969 + 3 ^ 40 * 3077175 * 2
def baseEnd_3077175 : Nat := 1053379888666068848240557

theorem tailTrace_3077175 : CollatzResearch.WordTrace tailWord_3077175 prefixEnd_3077175 1053379888666068848240557 := by
  unfold tailWord_3077175
  simp only [CollatzResearch.WordTrace]
  refine ⟨112233792626927989494760979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74822528417951992996507319 112233792626927989494760979)
  ·
    refine ⟨168350688940391984242141469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112233792626927989494760979 168350688940391984242141469)
    ·
      refine ⟨63131508352646994090803051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168350688940391984242141469 63131508352646994090803051)
      ·
        refine ⟨94697262528970491136204577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63131508352646994090803051 94697262528970491136204577)
        ·
          refine ⟨71022946896727868352153433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94697262528970491136204577 71022946896727868352153433)
          ·
            refine ⟨53267210172545901264115075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71022946896727868352153433 53267210172545901264115075)
            ·
              refine ⟨79900815258818851896172613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53267210172545901264115075 79900815258818851896172613)
              ·
                refine ⟨14981402861028534730532365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79900815258818851896172613 14981402861028534730532365)
                ·
                  refine ⟨5618026072885700523949637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14981402861028534730532365 5618026072885700523949637)
                  ·
                    refine ⟨1053379888666068848240557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5618026072885700523949637 1053379888666068848240557)
                    ·
                      rfl

theorem cell22_3077175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_3077175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077175 prefixEnd_3077175 := by exact prefixLift 3077175
  have htrace : WordTrace (prefixWord ++ tailWord_3077175) baseStart_3077175 baseEnd_3077175 := by
    simpa [prefixWord, tailWord_3077175, baseEnd_3077175] using wordTrace_append hprefix tailTrace_3077175
  have hstable : (prefixWord ++ tailWord_3077175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077175).length < 2 ^ (prefixWord ++ tailWord_3077175).sum := by decide
  have hdescent : baseEnd_3077175 < baseStart_3077175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077207 : List Nat := [1, 1, 3, 2, 2, 1, 1, 7, 4]
def baseStart_3077207 : Nat := 118140960795 + 3077207 * 2 ^ 59
def prefixEnd_3077207 : Nat := 4983230072969 + 3 ^ 40 * 3077207 * 2
def baseEnd_3077207 : Nat := 351130280973343810480153

theorem tailTrace_3077207 : CollatzResearch.WordTrace tailWord_3077207 prefixEnd_3077207 351130280973343810480153 := by
  unfold tailWord_3077207
  simp only [CollatzResearch.WordTrace]
  refine ⟨112234959762812058959925875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74823306508541372639950583 112234959762812058959925875)
  ·
    refine ⟨168352439644218088439888813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112234959762812058959925875 168352439644218088439888813)
    ·
      refine ⟨63132164866581783164958305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168352439644218088439888813 63132164866581783164958305)
      ·
        refine ⟨47349123649936337373718729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63132164866581783164958305 47349123649936337373718729)
        ·
          refine ⟨35511842737452253030289047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47349123649936337373718729 35511842737452253030289047)
          ·
            refine ⟨53267764106178379545433571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35511842737452253030289047 53267764106178379545433571)
            ·
              refine ⟨79901646159267569318150357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53267764106178379545433571 79901646159267569318150357)
              ·
                refine ⟨1872694831857833655894149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 79901646159267569318150357 1872694831857833655894149)
                ·
                  refine ⟨351130280973343810480153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1872694831857833655894149 351130280973343810480153)
                  ·
                    rfl

theorem cell22_3077207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 4].length) (baseStart_3077207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077207 prefixEnd_3077207 := by exact prefixLift 3077207
  have htrace : WordTrace (prefixWord ++ tailWord_3077207) baseStart_3077207 baseEnd_3077207 := by
    simpa [prefixWord, tailWord_3077207, baseEnd_3077207] using wordTrace_append hprefix tailTrace_3077207
  have hstable : (prefixWord ++ tailWord_3077207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077207).length < 2 ^ (prefixWord ++ tailWord_3077207).sum := by decide
  have hdescent : baseEnd_3077207 < baseStart_3077207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077220 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_3077220 : Nat := 118140960795 + 3077220 * 2 ^ 59
def prefixEnd_3077220 : Nat := 4983230072969 + 3 ^ 40 * 3077220 * 2
def baseEnd_3077220 : Nat := 1053395293085703730865419

theorem tailTrace_3077220 : CollatzResearch.WordTrace tailWord_3077220 prefixEnd_3077220 1053395293085703730865419 := by
  unfold tailWord_3077220
  simp only [CollatzResearch.WordTrace]
  refine ⟨56117716955882481090074557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74823622607843308120099409 56117716955882481090074557)
  ·
    refine ⟨21044143858455930408777959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56117716955882481090074557 21044143858455930408777959)
    ·
      refine ⟨31566215787683895613166939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21044143858455930408777959 31566215787683895613166939)
      ·
        refine ⟨47349323681525843419750409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31566215787683895613166939 47349323681525843419750409)
        ·
          refine ⟨35511992761144382564812807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47349323681525843419750409 35511992761144382564812807)
          ·
            refine ⟨53267989141716573847219211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35511992761144382564812807 53267989141716573847219211)
            ·
              refine ⟨79901983712574860770828817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53267989141716573847219211 79901983712574860770828817)
              ·
                refine ⟨59926487784431145578121613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79901983712574860770828817 59926487784431145578121613)
                ·
                  refine ⟨22472432919161679591795605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59926487784431145578121613 22472432919161679591795605)
                  ·
                    refine ⟨1053395293085703730865419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22472432919161679591795605 1053395293085703730865419)
                    ·
                      rfl

theorem cell22_3077220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_3077220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077220 prefixEnd_3077220 := by exact prefixLift 3077220
  have htrace : WordTrace (prefixWord ++ tailWord_3077220) baseStart_3077220 baseEnd_3077220 := by
    simpa [prefixWord, tailWord_3077220, baseEnd_3077220] using wordTrace_append hprefix tailTrace_3077220
  have hstable : (prefixWord ++ tailWord_3077220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077220).length < 2 ^ (prefixWord ++ tailWord_3077220).sum := by decide
  have hdescent : baseEnd_3077220 < baseStart_3077220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077284 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_3077284 : Nat := 118140960795 + 3077284 * 2 ^ 59
def prefixEnd_3077284 : Nat := 4983230072969 + 3 ^ 40 * 3077284 * 2
def baseEnd_3077284 : Nat := 1053417201593628897265223

theorem tailTrace_3077284 : CollatzResearch.WordTrace tailWord_3077284 prefixEnd_3077284 1053417201593628897265223 := by
  unfold tailWord_3077284
  simp only [CollatzResearch.WordTrace]
  refine ⟨56118884091766550555239453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74825178789022067406985937 56118884091766550555239453)
  ·
    refine ⟨21044581534412456458214795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56118884091766550555239453 21044581534412456458214795)
    ·
      refine ⟨31566872301618684687322193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21044581534412456458214795 31566872301618684687322193)
      ·
        refine ⟨23675154226214013515491645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31566872301618684687322193 23675154226214013515491645)
        ·
          refine ⟨8878182834830255068309367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23675154226214013515491645 8878182834830255068309367)
          ·
            refine ⟨13317274252245382602464051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8878182834830255068309367 13317274252245382602464051)
            ·
              refine ⟨19975911378368073903696077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13317274252245382602464051 19975911378368073903696077)
              ·
                refine ⟨7490966766888027713886029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19975911378368073903696077 7490966766888027713886029)
                ·
                  refine ⟨2809112537583010392707261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7490966766888027713886029 2809112537583010392707261)
                  ·
                    refine ⟨1053417201593628897265223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2809112537583010392707261 1053417201593628897265223)
                    ·
                      rfl

theorem cell22_3077284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_3077284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077284 prefixEnd_3077284 := by exact prefixLift 3077284
  have htrace : WordTrace (prefixWord ++ tailWord_3077284) baseStart_3077284 baseEnd_3077284 := by
    simpa [prefixWord, tailWord_3077284, baseEnd_3077284] using wordTrace_append hprefix tailTrace_3077284
  have hstable : (prefixWord ++ tailWord_3077284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077284).length < 2 ^ (prefixWord ++ tailWord_3077284).sum := by decide
  have hdescent : baseEnd_3077284 < baseStart_3077284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077374 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_3077374 : Nat := 118140960795 + 3077374 * 2 ^ 59
def prefixEnd_3077374 : Nat := 4983230072969 + 3 ^ 40 * 3077374 * 2
def baseEnd_3077374 : Nat := 1053448010432898662514947

theorem tailTrace_3077374 : CollatzResearch.WordTrace tailWord_3077374 prefixEnd_3077374 1053448010432898662514947 := by
  unfold tailWord_3077374
  simp only [CollatzResearch.WordTrace]
  refine ⟨14030131344150880810156897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74827367168804697654170117 14030131344150880810156897)
  ·
    refine ⟨10522598508113160607617673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14030131344150880810156897 10522598508113160607617673)
    ·
      refine ⟨7891948881084870455713255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10522598508113160607617673 7891948881084870455713255)
      ·
        refine ⟨11837923321627305683569883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7891948881084870455713255 11837923321627305683569883)
        ·
          refine ⟨17756884982440958525354825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11837923321627305683569883 17756884982440958525354825)
          ·
            refine ⟨13317663736830718894016119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17756884982440958525354825 13317663736830718894016119)
            ·
              refine ⟨19976495605246078341024179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13317663736830718894016119 19976495605246078341024179)
              ·
                refine ⟨29964743407869117511536269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19976495605246078341024179 29964743407869117511536269)
                ·
                  refine ⟨11236778777950919066826101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29964743407869117511536269 11236778777950919066826101)
                  ·
                    refine ⟨1053448010432898662514947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11236778777950919066826101 1053448010432898662514947)
                    ·
                      rfl

theorem cell22_3077374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_3077374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077374 prefixEnd_3077374 := by exact prefixLift 3077374
  have htrace : WordTrace (prefixWord ++ tailWord_3077374) baseStart_3077374 baseEnd_3077374 := by
    simpa [prefixWord, tailWord_3077374, baseEnd_3077374] using wordTrace_append hprefix tailTrace_3077374
  have hstable : (prefixWord ++ tailWord_3077374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077374).length < 2 ^ (prefixWord ++ tailWord_3077374).sum := by decide
  have hdescent : baseEnd_3077374 < baseStart_3077374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077432 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 7]
def baseStart_3077432 : Nat := 118140960795 + 3077432 * 2 ^ 59
def prefixEnd_3077432 : Nat := 4983230072969 + 3 ^ 40 * 3077432 * 2
def baseEnd_3077432 : Nat := 351155955006068614854923

theorem tailTrace_3077432 : CollatzResearch.WordTrace tailWord_3077432 prefixEnd_3077432 351155955006068614854923 := by
  unfold tailWord_3077432
  simp only [CollatzResearch.WordTrace]
  refine ⟨56121583093498461193433275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74828777457997948257911033 56121583093498461193433275)
  ·
    refine ⟨84182374640247691790149913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56121583093498461193433275 84182374640247691790149913)
    ·
      refine ⟨63136780980185768842612435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84182374640247691790149913 63136780980185768842612435)
      ·
        refine ⟨94705171470278653263918653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63136780980185768842612435 94705171470278653263918653)
        ·
          refine ⟨35514439301354494973969495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94705171470278653263918653 35514439301354494973969495)
          ·
            refine ⟨53271658952031742460954243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35514439301354494973969495 53271658952031742460954243)
            ·
              refine ⟨79907488428047613691431365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53271658952031742460954243 79907488428047613691431365)
              ·
                refine ⟨14982654080258927567143381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79907488428047613691431365 14982654080258927567143381)
                ·
                  refine ⟨351155955006068614854923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14982654080258927567143381 351155955006068614854923)
                  ·
                    rfl

theorem cell22_3077432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_3077432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077432 prefixEnd_3077432 := by exact prefixLift 3077432
  have htrace : WordTrace (prefixWord ++ tailWord_3077432) baseStart_3077432 baseEnd_3077432 := by
    simpa [prefixWord, tailWord_3077432, baseEnd_3077432] using wordTrace_append hprefix tailTrace_3077432
  have hstable : (prefixWord ++ tailWord_3077432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077432).length < 2 ^ (prefixWord ++ tailWord_3077432).sum := by decide
  have hdescent : baseEnd_3077432 < baseStart_3077432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077449 : List Nat := [1, 2, 1, 1, 2, 3, 5, 2, 5]
def baseStart_3077449 : Nat := 118140960795 + 3077449 * 2 ^ 59
def prefixEnd_3077449 : Nat := 4983230072969 + 3 ^ 40 * 3077449 * 2
def baseEnd_3077449 : Nat := 351157894821874488963239

theorem tailTrace_3077449 : CollatzResearch.WordTrace tailWord_3077449 prefixEnd_3077449 351157894821874488963239 := by
  unfold tailWord_3077449
  simp only [CollatzResearch.WordTrace]
  refine ⟨112243786227935334290235401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74829190818623556193490267 112243786227935334290235401)
  ·
    refine ⟨84182839670951500717676551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112243786227935334290235401 84182839670951500717676551)
    ·
      refine ⟨126274259506427251076514827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84182839670951500717676551 126274259506427251076514827)
      ·
        refine ⟨189411389259640876614772241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126274259506427251076514827 189411389259640876614772241)
        ·
          refine ⟨142058541944730657461079181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189411389259640876614772241 142058541944730657461079181)
          ·
            refine ⟨53271953229273996547904693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142058541944730657461079181 53271953229273996547904693)
            ·
              refine ⟨4994245615244437176366065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53271953229273996547904693 4994245615244437176366065)
              ·
                refine ⟨3745684211433327882274549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4994245615244437176366065 3745684211433327882274549)
                ·
                  refine ⟨351157894821874488963239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3745684211433327882274549 351157894821874488963239)
                  ·
                    rfl

theorem cell22_3077449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 5].length) (baseStart_3077449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077449 prefixEnd_3077449 := by exact prefixLift 3077449
  have htrace : WordTrace (prefixWord ++ tailWord_3077449) baseStart_3077449 baseEnd_3077449 := by
    simpa [prefixWord, tailWord_3077449, baseEnd_3077449] using wordTrace_append hprefix tailTrace_3077449
  have hstable : (prefixWord ++ tailWord_3077449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077449).length < 2 ^ (prefixWord ++ tailWord_3077449).sum := by decide
  have hdescent : baseEnd_3077449 < baseStart_3077449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077511 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 6]
def baseStart_3077511 : Nat := 118140960795 + 3077511 * 2 ^ 59
def prefixEnd_3077511 : Nat := 4983230072969 + 3 ^ 40 * 3077511 * 2
def baseEnd_3077511 : Nat := 351164969444225323946509

theorem tailTrace_3077511 : CollatzResearch.WordTrace tailWord_3077511 prefixEnd_3077511 351164969444225323946509 := by
  unfold tailWord_3077511
  simp only [CollatzResearch.WordTrace]
  refine ⟨112246047553710718878992387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74830698369140479252661591 112246047553710718878992387)
  ·
    refine ⟨168369071330566078318488581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112246047553710718878992387 168369071330566078318488581)
    ·
      refine ⟨31569200874481139684716609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168369071330566078318488581 31569200874481139684716609)
      ·
        refine ⟨23676900655860854763537457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31569200874481139684716609 23676900655860854763537457)
        ·
          refine ⟨17757675491895641072653093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23676900655860854763537457 17757675491895641072653093)
          ·
            refine ⟨3329564154730432701122455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17757675491895641072653093 3329564154730432701122455)
            ·
              refine ⟨4994346232095649051683683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3329564154730432701122455 4994346232095649051683683)
              ·
                refine ⟨7491519348143473577525525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4994346232095649051683683 7491519348143473577525525)
                ·
                  refine ⟨351164969444225323946509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7491519348143473577525525 351164969444225323946509)
                  ·
                    rfl

theorem cell22_3077511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 6].length) (baseStart_3077511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077511 prefixEnd_3077511 := by exact prefixLift 3077511
  have htrace : WordTrace (prefixWord ++ tailWord_3077511) baseStart_3077511 baseEnd_3077511 := by
    simpa [prefixWord, tailWord_3077511, baseEnd_3077511] using wordTrace_append hprefix tailTrace_3077511
  have hstable : (prefixWord ++ tailWord_3077511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077511).length < 2 ^ (prefixWord ++ tailWord_3077511).sum := by decide
  have hdescent : baseEnd_3077511 < baseStart_3077511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077599 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 1, 7]
def baseStart_3077599 : Nat := 118140960795 + 3077599 * 2 ^ 59
def prefixEnd_3077599 : Nat := 4983230072969 + 3 ^ 40 * 3077599 * 2
def baseEnd_3077599 : Nat := 1053525032531073075639257

theorem tailTrace_3077599 : CollatzResearch.WordTrace tailWord_3077599 prefixEnd_3077599 1053525032531073075639257 := by
  unfold tailWord_3077599
  simp only [CollatzResearch.WordTrace]
  refine ⟨112249257177391909908195851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74832838118261273272130567 112249257177391909908195851)
  ·
    refine ⟨168373885766087864862293777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112249257177391909908195851 168373885766087864862293777)
    ·
      refine ⟨126280414324565898646720333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168373885766087864862293777 126280414324565898646720333)
      ·
        refine ⟨47355155371712211992520125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126280414324565898646720333 47355155371712211992520125)
        ·
          refine ⟨17758183264392079497195047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47355155371712211992520125 17758183264392079497195047)
          ·
            refine ⟨26637274896588119245792571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17758183264392079497195047 26637274896588119245792571)
            ·
              refine ⟨39955912344882178868688857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26637274896588119245792571 39955912344882178868688857)
              ·
                refine ⟨29966934258661634151516643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39955912344882178868688857 29966934258661634151516643)
                ·
                  refine ⟨44950401387992451227274965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29966934258661634151516643 44950401387992451227274965)
                  ·
                    refine ⟨1053525032531073075639257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44950401387992451227274965 1053525032531073075639257)
                    ·
                      rfl

theorem cell22_3077599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_3077599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077599 prefixEnd_3077599 := by exact prefixLift 3077599
  have htrace : WordTrace (prefixWord ++ tailWord_3077599) baseStart_3077599 baseEnd_3077599 := by
    simpa [prefixWord, tailWord_3077599, baseEnd_3077599] using wordTrace_append hprefix tailTrace_3077599
  have hstable : (prefixWord ++ tailWord_3077599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077599).length < 2 ^ (prefixWord ++ tailWord_3077599).sum := by decide
  have hdescent : baseEnd_3077599 < baseStart_3077599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077605 : List Nat := [1, 3, 1, 5, 1, 1, 1, 5, 1, 3]
def baseStart_3077605 : Nat := 118140960795 + 3077605 * 2 ^ 59
def prefixEnd_3077605 : Nat := 4983230072969 + 3 ^ 40 * 3077605 * 2
def baseEnd_3077605 : Nat := 1053527086453691059989239

theorem tailTrace_3077605 : CollatzResearch.WordTrace tailWord_3077605 prefixEnd_3077605 1053527086453691059989239 := by
  unfold tailWord_3077605
  simp only [CollatzResearch.WordTrace]
  refine ⟨112249476015370172932914269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74832984010246781955276179 112249476015370172932914269)
  ·
    refine ⟨42093553505763814849842851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112249476015370172932914269 42093553505763814849842851)
    ·
      refine ⟨63140330258645722274764277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42093553505763814849842851 63140330258645722274764277)
      ·
        refine ⟨5919405961748036463259151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63140330258645722274764277 5919405961748036463259151)
        ·
          refine ⟨8879108942622054694888727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5919405961748036463259151 8879108942622054694888727)
          ·
            refine ⟨13318663413933082042333091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8879108942622054694888727 13318663413933082042333091)
            ·
              refine ⟨19977995120899623063499637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13318663413933082042333091 19977995120899623063499637)
              ·
                refine ⟨1872937042584339662203091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19977995120899623063499637 1872937042584339662203091)
                ·
                  refine ⟨2809405563876509493304637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872937042584339662203091 2809405563876509493304637)
                  ·
                    refine ⟨1053527086453691059989239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2809405563876509493304637 1053527086453691059989239)
                    ·
                      rfl

theorem cell22_3077605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_3077605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077605 prefixEnd_3077605 := by exact prefixLift 3077605
  have htrace : WordTrace (prefixWord ++ tailWord_3077605) baseStart_3077605 baseEnd_3077605 := by
    simpa [prefixWord, tailWord_3077605, baseEnd_3077605] using wordTrace_append hprefix tailTrace_3077605
  have hstable : (prefixWord ++ tailWord_3077605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077605).length < 2 ^ (prefixWord ++ tailWord_3077605).sum := by decide
  have hdescent : baseEnd_3077605 < baseStart_3077605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077618 : List Nat := [3, 2, 1, 4, 1, 1, 3, 2, 5]
def baseStart_3077618 : Nat := 118140960795 + 3077618 * 2 ^ 59
def prefixEnd_3077618 : Nat := 4983230072969 + 3 ^ 40 * 3077618 * 2
def baseEnd_3077618 : Nat := 351177178873121119804733

theorem tailTrace_3077618 : CollatzResearch.WordTrace tailWord_3077618 prefixEnd_3077618 351177178873121119804733 := by
  unfold tailWord_3077618
  simp only [CollatzResearch.WordTrace]
  refine ⟨28062487541080769038284377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74833300109548717435425005 28062487541080769038284377)
  ·
    refine ⟨21046865655810576778713283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28062487541080769038284377 21046865655810576778713283)
    ·
      refine ⟨31570298483715865168069925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21046865655810576778713283 31570298483715865168069925)
      ·
        refine ⟨5919430965696724719013111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31570298483715865168069925 5919430965696724719013111)
        ·
          refine ⟨8879146448545087078519667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5919430965696724719013111 8879146448545087078519667)
          ·
            refine ⟨13318719672817630617779501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8879146448545087078519667 13318719672817630617779501)
            ·
              refine ⟨4994519877306611481667313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13318719672817630617779501 4994519877306611481667313)
              ·
                refine ⟨3745889907979958611250485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4994519877306611481667313 3745889907979958611250485)
                ·
                  refine ⟨351177178873121119804733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3745889907979958611250485 351177178873121119804733)
                  ·
                    rfl

theorem cell22_3077618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_3077618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077618 prefixEnd_3077618 := by exact prefixLift 3077618
  have htrace : WordTrace (prefixWord ++ tailWord_3077618) baseStart_3077618 baseEnd_3077618 := by
    simpa [prefixWord, tailWord_3077618, baseEnd_3077618] using wordTrace_append hprefix tailTrace_3077618
  have hstable : (prefixWord ++ tailWord_3077618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077618).length < 2 ^ (prefixWord ++ tailWord_3077618).sum := by decide
  have hdescent : baseEnd_3077618 < baseStart_3077618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077661 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_3077661 : Nat := 118140960795 + 3077661 * 2 ^ 59
def prefixEnd_3077661 : Nat := 4983230072969 + 3 ^ 40 * 3077661 * 2
def baseEnd_3077661 : Nat := 1053546256398125580589067

theorem tailTrace_3077661 : CollatzResearch.WordTrace tailWord_3077661 prefixEnd_3077661 1053546256398125580589067 := by
  unfold tailWord_3077661
  simp only [CollatzResearch.WordTrace]
  refine ⟨112251518503167294496952837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74834345668778196331301891 112251518503167294496952837)
  ·
    refine ⟨21047159719343867718178657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112251518503167294496952837 21047159719343867718178657)
    ·
      refine ⟨15785369789507900788633993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21047159719343867718178657 15785369789507900788633993)
      ·
        refine ⟨11839027342130925591475495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15785369789507900788633993 11839027342130925591475495)
        ·
          refine ⟨17758541013196388387213243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11839027342130925591475495 17758541013196388387213243)
          ·
            refine ⟨26637811519794582580819865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17758541013196388387213243 26637811519794582580819865)
            ·
              refine ⟨19978358639845936935614899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26637811519794582580819865 19978358639845936935614899)
              ·
                refine ⟨29967537959768905403422349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19978358639845936935614899 29967537959768905403422349)
                ·
                  refine ⟨11237826734913339526283381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29967537959768905403422349 11237826734913339526283381)
                  ·
                    refine ⟨1053546256398125580589067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11237826734913339526283381 1053546256398125580589067)
                    ·
                      rfl

theorem cell22_3077661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_3077661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077661 prefixEnd_3077661 := by exact prefixLift 3077661
  have htrace : WordTrace (prefixWord ++ tailWord_3077661) baseStart_3077661 baseEnd_3077661 := by
    simpa [prefixWord, tailWord_3077661, baseEnd_3077661] using wordTrace_append hprefix tailTrace_3077661
  have hstable : (prefixWord ++ tailWord_3077661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077661).length < 2 ^ (prefixWord ++ tailWord_3077661).sum := by decide
  have hdescent : baseEnd_3077661 < baseStart_3077661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077663 : List Nat := [1, 1, 2, 4, 1, 1, 5, 3, 4]
def baseStart_3077663 : Nat := 118140960795 + 3077663 * 2 ^ 59
def prefixEnd_3077663 : Nat := 4983230072969 + 3 ^ 40 * 3077663 * 2
def baseEnd_3077663 : Nat := 351182313679666080679687

theorem tailTrace_3077663 : CollatzResearch.WordTrace tailWord_3077663 prefixEnd_3077663 351182313679666080679687 := by
  unfold tailWord_3077663
  simp only [CollatzResearch.WordTrace]
  refine ⟨112251591449160048838525643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74834394299440032559017095 112251591449160048838525643)
  ·
    refine ⟨168377387173740073257788465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112251591449160048838525643 168377387173740073257788465)
    ·
      refine ⟨126283040380305054943341349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168377387173740073257788465 126283040380305054943341349)
      ·
        refine ⟨23678070071307197801876503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126283040380305054943341349 23678070071307197801876503)
        ·
          refine ⟨35517105106960796702814755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23678070071307197801876503 35517105106960796702814755)
          ·
            refine ⟨53275657660441195054222133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35517105106960796702814755 53275657660441195054222133)
            ·
              refine ⟨4994592905666362036333325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53275657660441195054222133 4994592905666362036333325)
              ·
                refine ⟨1872972339624885763624997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4994592905666362036333325 1872972339624885763624997)
                ·
                  refine ⟨351182313679666080679687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1872972339624885763624997 351182313679666080679687)
                  ·
                    rfl

theorem cell22_3077663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 4].length) (baseStart_3077663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077663 prefixEnd_3077663 := by exact prefixLift 3077663
  have htrace : WordTrace (prefixWord ++ tailWord_3077663) baseStart_3077663 baseEnd_3077663 := by
    simpa [prefixWord, tailWord_3077663, baseEnd_3077663] using wordTrace_append hprefix tailTrace_3077663
  have hstable : (prefixWord ++ tailWord_3077663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077663).length < 2 ^ (prefixWord ++ tailWord_3077663).sum := by decide
  have hdescent : baseEnd_3077663 < baseStart_3077663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077695 : List Nat := [1, 1, 2, 2, 3, 3, 4, 1, 2, 3]
def baseStart_3077695 : Nat := 118140960795 + 3077695 * 2 ^ 59
def prefixEnd_3077695 : Nat := 4983230072969 + 3 ^ 40 * 3077695 * 2
def baseEnd_3077695 : Nat := 1053557895292960825238963

theorem tailTrace_3077695 : CollatzResearch.WordTrace tailWord_3077695 prefixEnd_3077695 1053557895292960825238963 := by
  unfold tailWord_3077695
  simp only [CollatzResearch.WordTrace]
  refine ⟨112252758585044118303690539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74835172390029412202460359 112252758585044118303690539)
  ·
    refine ⟨168379137877566177455535809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112252758585044118303690539 168379137877566177455535809)
    ·
      refine ⟨126284353408174633091651857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168379137877566177455535809 126284353408174633091651857)
      ·
        refine ⟨94713265056130974818738893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126284353408174633091651857 94713265056130974818738893)
        ·
          refine ⟨35517474396049115557027085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94713265056130974818738893 35517474396049115557027085)
          ·
            refine ⟨13319052898518418333885157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35517474396049115557027085 13319052898518418333885157)
            ·
              refine ⟨2497322418472203437603467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13319052898518418333885157 2497322418472203437603467)
              ·
                refine ⟨3745983627708305156405201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497322418472203437603467 3745983627708305156405201)
                ·
                  refine ⟨2809487720781228867303901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3745983627708305156405201 2809487720781228867303901)
                  ·
                    refine ⟨1053557895292960825238963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2809487720781228867303901 1053557895292960825238963)
                    ·
                      rfl

theorem cell22_3077695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 2, 3].length) (baseStart_3077695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077695 prefixEnd_3077695 := by exact prefixLift 3077695
  have htrace : WordTrace (prefixWord ++ tailWord_3077695) baseStart_3077695 baseEnd_3077695 := by
    simpa [prefixWord, tailWord_3077695, baseEnd_3077695] using wordTrace_append hprefix tailTrace_3077695
  have hstable : (prefixWord ++ tailWord_3077695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077695).length < 2 ^ (prefixWord ++ tailWord_3077695).sum := by decide
  have hdescent : baseEnd_3077695 < baseStart_3077695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077725 : List Nat := [1, 4, 4, 2, 2, 9]
def baseStart_3077725 : Nat := 118140960795 + 3077725 * 2 ^ 59
def prefixEnd_3077725 : Nat := 4983230072969 + 3 ^ 40 * 3077725 * 2
def baseEnd_3077725 : Nat := 13007014381556182061591

theorem tailTrace_3077725 : CollatzResearch.WordTrace tailWord_3077725 prefixEnd_3077725 13007014381556182061591 := by
  unfold tailWord_3077725
  simp only [CollatzResearch.WordTrace]
  refine ⟨112253852774935433427282629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74835901849956955618188419 112253852774935433427282629)
  ·
    refine ⟨21047597395300393767615493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112253852774935433427282629 21047597395300393767615493)
    ·
      refine ⟨3946424511618823831427905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21047597395300393767615493 3946424511618823831427905)
      ·
        refine ⟨2959818383714117873570929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3946424511618823831427905 2959818383714117873570929)
        ·
          refine ⟨2219863787785588405178197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2959818383714117873570929 2219863787785588405178197)
          ·
            refine ⟨13007014381556182061591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2219863787785588405178197 13007014381556182061591)
            ·
              rfl

theorem cell22_3077725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 9].length) (baseStart_3077725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077725 prefixEnd_3077725 := by exact prefixLift 3077725
  have htrace : WordTrace (prefixWord ++ tailWord_3077725) baseStart_3077725 baseEnd_3077725 := by
    simpa [prefixWord, tailWord_3077725, baseEnd_3077725] using wordTrace_append hprefix tailTrace_3077725
  have hstable : (prefixWord ++ tailWord_3077725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077725).length < 2 ^ (prefixWord ++ tailWord_3077725).sum := by decide
  have hdescent : baseEnd_3077725 < baseStart_3077725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077811 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 3, 6]
def baseStart_3077811 : Nat := 118140960795 + 3077811 * 2 ^ 59
def prefixEnd_3077811 : Nat := 4983230072969 + 3 ^ 40 * 3077811 * 2
def baseEnd_3077811 : Nat := 1053597604463575189338607

theorem tailTrace_3077811 : CollatzResearch.WordTrace tailWord_3077811 prefixEnd_3077811 1053597604463575189338607 := by
  unfold tailWord_3077811
  simp only [CollatzResearch.WordTrace]
  refine ⟨112256989452623870114913287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74837992968415913409942191 112256989452623870114913287)
  ·
    refine ⟨168385484178935805172369931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112256989452623870114913287 168385484178935805172369931)
    ·
      refine ⟨252578226268403707758554897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168385484178935805172369931 252578226268403707758554897)
      ·
        refine ⟨189433669701302780818916173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252578226268403707758554897 189433669701302780818916173)
        ·
          refine ⟨71037626137988542807093565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189433669701302780818916173 71037626137988542807093565)
          ·
            refine ⟨26639109801745703552660087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71037626137988542807093565 26639109801745703552660087)
            ·
              refine ⟨39958664702618555328990131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26639109801745703552660087 39958664702618555328990131)
              ·
                refine ⟨59937997053927832993485197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39958664702618555328990131 59937997053927832993485197)
                ·
                  refine ⟨22476748895222937372556949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59937997053927832993485197 22476748895222937372556949)
                  ·
                    refine ⟨1053597604463575189338607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22476748895222937372556949 1053597604463575189338607)
                    ·
                      rfl

theorem cell22_3077811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 6].length) (baseStart_3077811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077811 prefixEnd_3077811 := by exact prefixLift 3077811
  have htrace : WordTrace (prefixWord ++ tailWord_3077811) baseStart_3077811 baseEnd_3077811 := by
    simpa [prefixWord, tailWord_3077811, baseEnd_3077811] using wordTrace_append hprefix tailTrace_3077811
  have hstable : (prefixWord ++ tailWord_3077811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077811).length < 2 ^ (prefixWord ++ tailWord_3077811).sum := by decide
  have hdescent : baseEnd_3077811 < baseStart_3077811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077828 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3077828 : Nat := 118140960795 + 3077828 * 2 ^ 59
def prefixEnd_3077828 : Nat := 4983230072969 + 3 ^ 40 * 3077828 * 2
def baseEnd_3077828 : Nat := 1053603423910992811663555

theorem tailTrace_3077828 : CollatzResearch.WordTrace tailWord_3077828 prefixEnd_3077828 1053603423910992811663555 := by
  unfold tailWord_3077828
  simp only [CollatzResearch.WordTrace]
  refine ⟨56128804746781141009141069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74838406329041521345521425 56128804746781141009141069)
  ·
    refine ⟨21048301780042927878427901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56128804746781141009141069 21048301780042927878427901)
    ·
      refine ⟨7893113167516097954410463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21048301780042927878427901 7893113167516097954410463)
      ·
        refine ⟨11839669751274146931615695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7893113167516097954410463 11839669751274146931615695)
        ·
          refine ⟨17759504626911220397423543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11839669751274146931615695 17759504626911220397423543)
          ·
            refine ⟨26639256940366830596135315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17759504626911220397423543 26639256940366830596135315)
            ·
              refine ⟨39958885410550245894202973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26639256940366830596135315 39958885410550245894202973)
              ·
                refine ⟨14984582028956342210326115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39958885410550245894202973 14984582028956342210326115)
                ·
                  refine ⟨22476873043434513315489173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14984582028956342210326115 22476873043434513315489173)
                  ·
                    refine ⟨1053603423910992811663555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22476873043434513315489173 1053603423910992811663555)
                    ·
                      rfl

theorem cell22_3077828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3077828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077828 prefixEnd_3077828 := by exact prefixLift 3077828
  have htrace : WordTrace (prefixWord ++ tailWord_3077828) baseStart_3077828 baseEnd_3077828 := by
    simpa [prefixWord, tailWord_3077828, baseEnd_3077828] using wordTrace_append hprefix tailTrace_3077828
  have hstable : (prefixWord ++ tailWord_3077828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077828).length < 2 ^ (prefixWord ++ tailWord_3077828).sum := by decide
  have hdescent : baseEnd_3077828 < baseStart_3077828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077864 : List Nat := [2, 1, 4, 1, 3, 3, 2, 1, 2, 3]
def baseStart_3077864 : Nat := 118140960795 + 3077864 * 2 ^ 59
def prefixEnd_3077864 : Nat := 4983230072969 + 3 ^ 40 * 3077864 * 2
def baseEnd_3077864 : Nat := 1053615747446700717763445

theorem tailTrace_3077864 : CollatzResearch.WordTrace tailWord_3077864 prefixEnd_3077864 1053615747446700717763445 := by
  unfold tailWord_3077864
  simp only [CollatzResearch.WordTrace]
  refine ⟨56129461260715930083296323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74839281680954573444395097 56129461260715930083296323)
  ·
    refine ⟨84194191891073895124944485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56129461260715930083296323 84194191891073895124944485)
    ·
      refine ⟨15786410979576355335927091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84194191891073895124944485 15786410979576355335927091)
      ·
        refine ⟨23679616469364533003890637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15786410979576355335927091 23679616469364533003890637)
        ·
          refine ⟨8879856176011699876458989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23679616469364533003890637 8879856176011699876458989)
          ·
            refine ⟨3329946066004387453672121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8879856176011699876458989 3329946066004387453672121)
            ·
              refine ⟨2497459549503290590254091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3329946066004387453672121 2497459549503290590254091)
              ·
                refine ⟨3746189324254935885381137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497459549503290590254091 3746189324254935885381137)
                ·
                  refine ⟨2809641993191201914035853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3746189324254935885381137 2809641993191201914035853)
                  ·
                    refine ⟨1053615747446700717763445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2809641993191201914035853 1053615747446700717763445)
                    ·
                      rfl

theorem cell22_3077864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_3077864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077864 prefixEnd_3077864 := by exact prefixLift 3077864
  have htrace : WordTrace (prefixWord ++ tailWord_3077864) baseStart_3077864 baseEnd_3077864 := by
    simpa [prefixWord, tailWord_3077864, baseEnd_3077864] using wordTrace_append hprefix tailTrace_3077864
  have hstable : (prefixWord ++ tailWord_3077864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077864).length < 2 ^ (prefixWord ++ tailWord_3077864).sum := by decide
  have hdescent : baseEnd_3077864 < baseStart_3077864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077894 : List Nat := [6, 2, 2, 1, 11]
def baseStart_3077894 : Nat := 118140960795 + 3077894 * 2 ^ 59
def prefixEnd_3077894 : Nat := 4983230072969 + 3 ^ 40 * 3077894 * 2
def baseEnd_3077894 : Nat := 4335909535225475882771

theorem tailTrace_3077894 : CollatzResearch.WordTrace tailWord_3077894 prefixEnd_3077894 4335909535225475882771 := by
  unfold tailWord_3077894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3508125522228849227818273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74840011140882116860123157 3508125522228849227818273)
  ·
    refine ⟨2631094141671636920863705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3508125522228849227818273 2631094141671636920863705)
    ·
      refine ⟨1973320606253727690647779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2631094141671636920863705 1973320606253727690647779)
      ·
        refine ⟨2959980909380591535971669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1973320606253727690647779 2959980909380591535971669)
        ·
          refine ⟨4335909535225475882771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2959980909380591535971669 4335909535225475882771)
          ·
            rfl

theorem cell22_3077894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 11].length) (baseStart_3077894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077894 prefixEnd_3077894 := by exact prefixLift 3077894
  have htrace : WordTrace (prefixWord ++ tailWord_3077894) baseStart_3077894 baseEnd_3077894 := by
    simpa [prefixWord, tailWord_3077894, baseEnd_3077894] using wordTrace_append hprefix tailTrace_3077894
  have hstable : (prefixWord ++ tailWord_3077894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077894).length < 2 ^ (prefixWord ++ tailWord_3077894).sum := by decide
  have hdescent : baseEnd_3077894 < baseStart_3077894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077909 : List Nat := [1, 3, 2, 1, 2, 3, 4, 2, 1, 3]
def baseStart_3077909 : Nat := 118140960795 + 3077909 * 2 ^ 59
def prefixEnd_3077909 : Nat := 4983230072969 + 3 ^ 40 * 3077909 * 2
def baseEnd_3077909 : Nat := 1053631151866335600388307

theorem tailTrace_3077909 : CollatzResearch.WordTrace tailWord_3077909 prefixEnd_3077909 1053631151866335600388307 := by
  unfold tailWord_3077909
  simp only [CollatzResearch.WordTrace]
  refine ⟨112260563806268832851980781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74840375870845888567987187 112260563806268832851980781)
  ·
    refine ⟨42097711427350812319492793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112260563806268832851980781 42097711427350812319492793)
    ·
      refine ⟨31573283570513109239619595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42097711427350812319492793 31573283570513109239619595)
      ·
        refine ⟨47359925355769663859429393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31573283570513109239619595 47359925355769663859429393)
        ·
          refine ⟨35519944016827247894572045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47359925355769663859429393 35519944016827247894572045)
          ·
            refine ⟨13319979006310217960464517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35519944016827247894572045 13319979006310217960464517)
            ·
              refine ⟨2497496063683165867587097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13319979006310217960464517 2497496063683165867587097)
              ·
                refine ⟨1873122047762374400690323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2497496063683165867587097 1873122047762374400690323)
                ·
                  refine ⟨2809683071643561601035485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873122047762374400690323 2809683071643561601035485)
                  ·
                    refine ⟨1053631151866335600388307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2809683071643561601035485 1053631151866335600388307)
                    ·
                      rfl

theorem cell22_3077909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_3077909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077909 prefixEnd_3077909 := by exact prefixLift 3077909
  have htrace : WordTrace (prefixWord ++ tailWord_3077909) baseStart_3077909 baseEnd_3077909 := by
    simpa [prefixWord, tailWord_3077909, baseEnd_3077909] using wordTrace_append hprefix tailTrace_3077909
  have hstable : (prefixWord ++ tailWord_3077909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077909).length < 2 ^ (prefixWord ++ tailWord_3077909).sum := by decide
  have hdescent : baseEnd_3077909 < baseStart_3077909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077978 : List Nat := [3, 1, 1, 2, 1, 3, 2, 9]
def baseStart_3077978 : Nat := 118140960795 + 3077978 * 2 ^ 59
def prefixEnd_3077978 : Nat := 4983230072969 + 3 ^ 40 * 3077978 * 2
def baseEnd_3077978 : Nat := 117072752441826935601455

theorem tailTrace_3077978 : CollatzResearch.WordTrace tailWord_3077978 prefixEnd_3077978 117072752441826935601455 := by
  unfold tailWord_3077978
  simp only [CollatzResearch.WordTrace]
  refine ⟨28065770110754714409060647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74842053628679238424161725 28065770110754714409060647)
  ·
    refine ⟨42098655166132071613590971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28065770110754714409060647 42098655166132071613590971)
    ·
      refine ⟨63147982749198107420386457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42098655166132071613590971 63147982749198107420386457)
      ·
        refine ⟨47360987061898580565289843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63147982749198107420386457 47360987061898580565289843)
        ·
          refine ⟨71041480592847870847934765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47360987061898580565289843 71041480592847870847934765)
          ·
            refine ⟨26640555222317951567975537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71041480592847870847934765 26640555222317951567975537)
            ·
              refine ⟨19980416416738463675981653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26640555222317951567975537 19980416416738463675981653)
              ·
                refine ⟨117072752441826935601455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19980416416738463675981653 117072752441826935601455)
                ·
                  rfl

theorem cell22_3077978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_3077978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3077978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3077978 prefixEnd_3077978 := by exact prefixLift 3077978
  have htrace : WordTrace (prefixWord ++ tailWord_3077978) baseStart_3077978 baseEnd_3077978 := by
    simpa [prefixWord, tailWord_3077978, baseEnd_3077978] using wordTrace_append hprefix tailTrace_3077978
  have hstable : (prefixWord ++ tailWord_3077978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077978).length < 2 ^ (prefixWord ++ tailWord_3077978).sum := by decide
  have hdescent : baseEnd_3077978 < baseStart_3077978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078010 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 5, 3]
def baseStart_3078010 : Nat := 118140960795 + 3078010 * 2 ^ 59
def prefixEnd_3078010 : Nat := 4983230072969 + 3 ^ 40 * 3078010 * 2
def baseEnd_3078010 : Nat := 1053665726230405003612997

theorem tailTrace_3078010 : CollatzResearch.WordTrace tailWord_3078010 prefixEnd_3078010 1053665726230405003612997 := by
  unfold tailWord_3078010
  simp only [CollatzResearch.WordTrace]
  refine ⟨28066061894725731775351871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74842831719268618067604989 28066061894725731775351871)
  ·
    refine ⟨42099092842088597663027807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28066061894725731775351871 42099092842088597663027807)
    ·
      refine ⟨63148639263132896494541711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42099092842088597663027807 63148639263132896494541711)
      ·
        refine ⟨94722958894699344741812567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63148639263132896494541711 94722958894699344741812567)
        ·
          refine ⟨142084438342049017112718851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94722958894699344741812567 142084438342049017112718851)
          ·
            refine ⟨213126657513073525669078277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142084438342049017112718851 213126657513073525669078277)
            ·
              refine ⟨39961248283701286062952177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213126657513073525669078277 39961248283701286062952177)
              ·
                refine ⟨29970936212775964547214133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39961248283701286062952177 29970936212775964547214133)
                ·
                  refine ⟨2809775269947746676301325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29970936212775964547214133 2809775269947746676301325)
                  ·
                    refine ⟨1053665726230405003612997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2809775269947746676301325 1053665726230405003612997)
                    ·
                      rfl

theorem cell22_3078010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_3078010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078010 prefixEnd_3078010 := by exact prefixLift 3078010
  have htrace : WordTrace (prefixWord ++ tailWord_3078010) baseStart_3078010 baseEnd_3078010 := by
    simpa [prefixWord, tailWord_3078010, baseEnd_3078010] using wordTrace_append hprefix tailTrace_3078010
  have hstable : (prefixWord ++ tailWord_3078010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078010).length < 2 ^ (prefixWord ++ tailWord_3078010).sum := by decide
  have hdescent : baseEnd_3078010 < baseStart_3078010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078014 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3078014 : Nat := 118140960795 + 3078014 * 2 ^ 59
def prefixEnd_3078014 : Nat := 4983230072969 + 3 ^ 40 * 3078014 * 2
def baseEnd_3078014 : Nat := 1053667095512150326512985

theorem tailTrace_3078014 : CollatzResearch.WordTrace tailWord_3078014 prefixEnd_3078014 1053667095512150326512985 := by
  unfold tailWord_3078014
  simp only [CollatzResearch.WordTrace]
  refine ⟨14033049183861054473069137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74842928980592290523035397 14033049183861054473069137)
  ·
    refine ⟨10524786887895790854801853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14033049183861054473069137 10524786887895790854801853)
    ·
      refine ⟨3946795082960921570550695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10524786887895790854801853 3946795082960921570550695)
      ·
        refine ⟨5920192624441382355826043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3946795082960921570550695 5920192624441382355826043)
        ·
          refine ⟨8880288936662073533739065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5920192624441382355826043 8880288936662073533739065)
          ·
            refine ⟨6660216702496555150304299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8880288936662073533739065 6660216702496555150304299)
            ·
              refine ⟨9990325053744832725456449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6660216702496555150304299 9990325053744832725456449)
              ·
                refine ⟨7492743790308624544092337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9990325053744832725456449 7492743790308624544092337)
                ·
                  refine ⟨5619557842731468408069253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7492743790308624544092337 5619557842731468408069253)
                  ·
                    refine ⟨1053667095512150326512985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5619557842731468408069253 1053667095512150326512985)
                    ·
                      rfl

theorem cell22_3078014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3078014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078014 prefixEnd_3078014 := by exact prefixLift 3078014
  have htrace : WordTrace (prefixWord ++ tailWord_3078014) baseStart_3078014 baseEnd_3078014 := by
    simpa [prefixWord, tailWord_3078014, baseEnd_3078014] using wordTrace_append hprefix tailTrace_3078014
  have hstable : (prefixWord ++ tailWord_3078014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078014).length < 2 ^ (prefixWord ++ tailWord_3078014).sum := by decide
  have hdescent : baseEnd_3078014 < baseStart_3078014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078078 : List Nat := [4, 2, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_3078078 : Nat := 118140960795 + 3078078 * 2 ^ 59
def prefixEnd_3078078 : Nat := 4983230072969 + 3 ^ 40 * 3078078 * 2
def baseEnd_3078078 : Nat := 1053689004020075492912789

theorem tailTrace_3078078 : CollatzResearch.WordTrace tailWord_3078078 prefixEnd_3078078 1053689004020075492912789 := by
  unfold tailWord_3078078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14033340967832071839360361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74844485161771049809921925 14033340967832071839360361)
  ·
    refine ⟨10525005725874053879520271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14033340967832071839360361 10525005725874053879520271)
    ·
      refine ⟨15787508588811080819280407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10525005725874053879520271 15787508588811080819280407)
      ·
        refine ⟨23681262883216621228920611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15787508588811080819280407 23681262883216621228920611)
        ·
          refine ⟨35521894324824931843380917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23681262883216621228920611 35521894324824931843380917)
          ·
            refine ⟨3330177592952337360316961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35521894324824931843380917 3330177592952337360316961)
            ·
              refine ⟨2497633194714253020237721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3330177592952337360316961 2497633194714253020237721)
              ·
                refine ⟨1873224896035689765178291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2497633194714253020237721 1873224896035689765178291)
                ·
                  refine ⟨2809837344053534647767437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873224896035689765178291 2809837344053534647767437)
                  ·
                    refine ⟨1053689004020075492912789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2809837344053534647767437 1053689004020075492912789)
                    ·
                      rfl

theorem cell22_3078078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_3078078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078078 prefixEnd_3078078 := by exact prefixLift 3078078
  have htrace : WordTrace (prefixWord ++ tailWord_3078078) baseStart_3078078 baseEnd_3078078 := by
    simpa [prefixWord, tailWord_3078078, baseEnd_3078078] using wordTrace_append hprefix tailTrace_3078078
  have hstable : (prefixWord ++ tailWord_3078078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078078).length < 2 ^ (prefixWord ++ tailWord_3078078).sum := by decide
  have hdescent : baseEnd_3078078 < baseStart_3078078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078151 : List Nat := [1, 1, 4, 3, 1, 3, 3, 1, 2, 3]
def baseStart_3078151 : Nat := 118140960795 + 3078151 * 2 ^ 59
def prefixEnd_3078151 : Nat := 4983230072969 + 3 ^ 40 * 3078151 * 2
def baseEnd_3078151 : Nat := 1053713993411927635837565

theorem tailTrace_3078151 : CollatzResearch.WordTrace tailWord_3078151 prefixEnd_3078151 1053713993411927635837565 := by
  unfold tailWord_3078151
  simp only [CollatzResearch.WordTrace]
  refine ⟨112269390271392108182290307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74846260180928072121526871 112269390271392108182290307)
  ·
    refine ⟨168404085407088162273435461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112269390271392108182290307 168404085407088162273435461)
    ·
      refine ⟨31575766013829030426269149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168404085407088162273435461 31575766013829030426269149)
      ·
        refine ⟨11840912255185886409850931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31575766013829030426269149 11840912255185886409850931)
        ·
          refine ⟨17761368382778829614776397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11840912255185886409850931 17761368382778829614776397)
          ·
            refine ⟨6660513143542061105541149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17761368382778829614776397 6660513143542061105541149)
            ·
              refine ⟨2497692428828272914577931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6660513143542061105541149 2497692428828272914577931)
              ·
                refine ⟨3746538643242409371866897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497692428828272914577931 3746538643242409371866897)
                ·
                  refine ⟨2809903982431807028900173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3746538643242409371866897 2809903982431807028900173)
                  ·
                    refine ⟨1053713993411927635837565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2809903982431807028900173 1053713993411927635837565)
                    ·
                      rfl

theorem cell22_3078151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_3078151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078151 prefixEnd_3078151 := by exact prefixLift 3078151
  have htrace : WordTrace (prefixWord ++ tailWord_3078151) baseStart_3078151 baseEnd_3078151 := by
    simpa [prefixWord, tailWord_3078151, baseEnd_3078151] using wordTrace_append hprefix tailTrace_3078151
  have hstable : (prefixWord ++ tailWord_3078151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078151).length < 2 ^ (prefixWord ++ tailWord_3078151).sum := by decide
  have hdescent : baseEnd_3078151 < baseStart_3078151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078175 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 9]
def baseStart_3078175 : Nat := 118140960795 + 3078175 * 2 ^ 59
def prefixEnd_3078175 : Nat := 4983230072969 + 3 ^ 40 * 3078175 * 2
def baseEnd_3078175 : Nat := 351240736367466524412497

theorem tailTrace_3078175 : CollatzResearch.WordTrace tailWord_3078175 prefixEnd_3078175 351240736367466524412497 := by
  unfold tailWord_3078175
  simp only [CollatzResearch.WordTrace]
  refine ⟨112270265623305160281163979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74846843748870106854109319 112270265623305160281163979)
  ·
    refine ⟨168405398434957740421745969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112270265623305160281163979 168405398434957740421745969)
    ·
      refine ⟨126304048826218305316309477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168405398434957740421745969 126304048826218305316309477)
      ·
        refine ⟨23682009154915932246808027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126304048826218305316309477 23682009154915932246808027)
        ·
          refine ⟨35523013732373898370212041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23682009154915932246808027 35523013732373898370212041)
          ·
            refine ⟨26642260299280423777659031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35523013732373898370212041 26642260299280423777659031)
            ·
              refine ⟨39963390448920635666488547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26642260299280423777659031 39963390448920635666488547)
              ·
                refine ⟨59945085673380953499732821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39963390448920635666488547 59945085673380953499732821)
                ·
                  refine ⟨351240736367466524412497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59945085673380953499732821 351240736367466524412497)
                  ·
                    rfl

theorem cell22_3078175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 9].length) (baseStart_3078175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078175 prefixEnd_3078175 := by exact prefixLift 3078175
  have htrace : WordTrace (prefixWord ++ tailWord_3078175) baseStart_3078175 baseEnd_3078175 := by
    simpa [prefixWord, tailWord_3078175, baseEnd_3078175] using wordTrace_append hprefix tailTrace_3078175
  have hstable : (prefixWord ++ tailWord_3078175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078175).length < 2 ^ (prefixWord ++ tailWord_3078175).sum := by decide
  have hdescent : baseEnd_3078175 < baseStart_3078175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078209 : List Nat := [1, 2, 5, 1, 2, 2, 1, 3, 5]
def baseStart_3078209 : Nat := 118140960795 + 3078209 * 2 ^ 59
def prefixEnd_3078209 : Nat := 4983230072969 + 3 ^ 40 * 3078209 * 2
def baseEnd_3078209 : Nat := 351244615999078272629129

theorem tailTrace_3078209 : CollatzResearch.WordTrace tailWord_3078209 prefixEnd_3078209 351244615999078272629129 := by
  unfold tailWord_3078209
  simp only [CollatzResearch.WordTrace]
  refine ⟨112271505705181984087901681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74847670470121322725267787 112271505705181984087901681)
  ·
    refine ⟨84203629278886488065926261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112271505705181984087901681 84203629278886488065926261)
    ·
      refine ⟨7894090244895608256180587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84203629278886488065926261 7894090244895608256180587)
      ·
        refine ⟨11841135367343412384270881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7894090244895608256180587 11841135367343412384270881)
        ·
          refine ⟨8880851525507559288203161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11841135367343412384270881 8880851525507559288203161)
          ·
            refine ⟨6660638644130669466152371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8880851525507559288203161 6660638644130669466152371)
            ·
              refine ⟨9990957966196004199228557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6660638644130669466152371 9990957966196004199228557)
              ·
                refine ⟨3746609237323501574710709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9990957966196004199228557 3746609237323501574710709)
                ·
                  refine ⟨351244615999078272629129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3746609237323501574710709 351244615999078272629129)
                  ·
                    rfl

theorem cell22_3078209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 5].length) (baseStart_3078209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078209 prefixEnd_3078209 := by exact prefixLift 3078209
  have htrace : WordTrace (prefixWord ++ tailWord_3078209) baseStart_3078209 baseEnd_3078209 := by
    simpa [prefixWord, tailWord_3078209, baseEnd_3078209] using wordTrace_append hprefix tailTrace_3078209
  have hstable : (prefixWord ++ tailWord_3078209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078209).length < 2 ^ (prefixWord ++ tailWord_3078209).sum := by decide
  have hdescent : baseEnd_3078209 < baseStart_3078209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078269 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_3078269 : Nat := 118140960795 + 3078269 * 2 ^ 59
def prefixEnd_3078269 : Nat := 4983230072969 + 3 ^ 40 * 3078269 * 2
def baseEnd_3078269 : Nat := 1053754387223414661387203

theorem tailTrace_3078269 : CollatzResearch.WordTrace tailWord_3078269 prefixEnd_3078269 1053754387223414661387203 := by
  unfold tailWord_3078269
  simp only [CollatzResearch.WordTrace]
  refine ⟨112273694084964614335085861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74849129389976409556723907 112273694084964614335085861)
  ·
    refine ⟨21051317640930865187828599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112273694084964614335085861 21051317640930865187828599)
    ·
      refine ⟨31576976461396297781742899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21051317640930865187828599 31576976461396297781742899)
      ·
        refine ⟨47365464692094446672614349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31576976461396297781742899 47365464692094446672614349)
        ·
          refine ⟨17762049259535417502230381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47365464692094446672614349 17762049259535417502230381)
          ·
            refine ⟨6660768472325781563336393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17762049259535417502230381 6660768472325781563336393)
            ·
              refine ⟨4995576354244336172502295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6660768472325781563336393 4995576354244336172502295)
              ·
                refine ⟨7493364531366504258753443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4995576354244336172502295 7493364531366504258753443)
                ·
                  refine ⟨11240046797049756388130165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7493364531366504258753443 11240046797049756388130165)
                  ·
                    refine ⟨1053754387223414661387203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11240046797049756388130165 1053754387223414661387203)
                    ·
                      rfl

theorem cell22_3078269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_3078269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078269 prefixEnd_3078269 := by exact prefixLift 3078269
  have htrace : WordTrace (prefixWord ++ tailWord_3078269) baseStart_3078269 baseEnd_3078269 := by
    simpa [prefixWord, tailWord_3078269, baseEnd_3078269] using wordTrace_append hprefix tailTrace_3078269
  have hstable : (prefixWord ++ tailWord_3078269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078269).length < 2 ^ (prefixWord ++ tailWord_3078269).sum := by decide
  have hdescent : baseEnd_3078269 < baseStart_3078269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078294 : List Nat := [5, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3078294 : Nat := 118140960795 + 3078294 * 2 ^ 59
def prefixEnd_3078294 : Nat := 4983230072969 + 3 ^ 40 * 3078294 * 2
def baseEnd_3078294 : Nat := 351254315078107643170709

theorem tailTrace_3078294 : CollatzResearch.WordTrace tailWord_3078294 prefixEnd_3078294 351254315078107643170709 := by
  unfold tailWord_3078294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7017162869367127725296621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74849737273249362403163957 7017162869367127725296621)
  ·
    refine ⟨2631436076012672896986233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7017162869367127725296621 2631436076012672896986233)
    ·
      refine ⟨1973577057009504672739675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2631436076012672896986233 1973577057009504672739675)
      ·
        refine ⟨2960365585514257009109513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1973577057009504672739675 2960365585514257009109513)
        ·
          refine ⟨2220274189135692756832135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2960365585514257009109513 2220274189135692756832135)
          ·
            refine ⟨3330411283703539135248203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2220274189135692756832135 3330411283703539135248203)
            ·
              refine ⟨4995616925555308702872305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3330411283703539135248203 4995616925555308702872305)
              ·
                refine ⟨3746712694166481527154229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4995616925555308702872305 3746712694166481527154229)
                ·
                  refine ⟨351254315078107643170709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3746712694166481527154229 351254315078107643170709)
                  ·
                    rfl

theorem cell22_3078294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3078294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078294 prefixEnd_3078294 := by exact prefixLift 3078294
  have htrace : WordTrace (prefixWord ++ tailWord_3078294) baseStart_3078294 baseEnd_3078294 := by
    simpa [prefixWord, tailWord_3078294, baseEnd_3078294] using wordTrace_append hprefix tailTrace_3078294
  have hstable : (prefixWord ++ tailWord_3078294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078294).length < 2 ^ (prefixWord ++ tailWord_3078294).sum := by decide
  have hdescent : baseEnd_3078294 < baseStart_3078294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078303 : List Nat := [1, 1, 2, 6, 1, 3, 1, 2, 2, 3]
def baseStart_3078303 : Nat := 118140960795 + 3078303 * 2 ^ 59
def prefixEnd_3078303 : Nat := 4983230072969 + 3 ^ 40 * 3078303 * 2
def baseEnd_3078303 : Nat := 1053766026118249906037099

theorem tailTrace_3078303 : CollatzResearch.WordTrace tailWord_3078303 prefixEnd_3078303 1053766026118249906037099 := by
  unfold tailWord_3078303
  simp only [CollatzResearch.WordTrace]
  refine ⟨112274934166841438141823563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74849956111227625427882375 112274934166841438141823563)
  ·
    refine ⟨168412401250262157212735345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112274934166841438141823563 168412401250262157212735345)
    ·
      refine ⟨126309300937696617909551509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168412401250262157212735345 126309300937696617909551509)
      ·
        refine ⟨5920748481454528964510227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126309300937696617909551509 5920748481454528964510227)
        ·
          refine ⟨8881122722181793446765341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5920748481454528964510227 8881122722181793446765341)
          ·
            refine ⟨3330421020818172542537003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8881122722181793446765341 3330421020818172542537003)
            ·
              refine ⟨4995631531227258813805505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3330421020818172542537003 4995631531227258813805505)
              ·
                refine ⟨3746723648420444110354129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4995631531227258813805505 3746723648420444110354129)
                ·
                  refine ⟨2810042736315333082765597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3746723648420444110354129 2810042736315333082765597)
                  ·
                    refine ⟨1053766026118249906037099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810042736315333082765597 1053766026118249906037099)
                    ·
                      rfl

theorem cell22_3078303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 3].length) (baseStart_3078303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078303 prefixEnd_3078303 := by exact prefixLift 3078303
  have htrace : WordTrace (prefixWord ++ tailWord_3078303) baseStart_3078303 baseEnd_3078303 := by
    simpa [prefixWord, tailWord_3078303, baseEnd_3078303] using wordTrace_append hprefix tailTrace_3078303
  have hstable : (prefixWord ++ tailWord_3078303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078303).length < 2 ^ (prefixWord ++ tailWord_3078303).sum := by decide
  have hdescent : baseEnd_3078303 < baseStart_3078303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078408 : List Nat := [2, 1, 3, 2, 3, 2, 3, 1, 1, 4]
def baseStart_3078408 : Nat := 118140960795 + 3078408 * 2 ^ 59
def prefixEnd_3078408 : Nat := 4983230072969 + 3 ^ 40 * 3078408 * 2
def baseEnd_3078408 : Nat := 1053801969764064632161777

theorem tailTrace_3078408 : CollatzResearch.WordTrace tailWord_3078408 prefixEnd_3078408 1053801969764064632161777 := by
  unfold tailWord_3078408
  simp only [CollatzResearch.WordTrace]
  refine ⟨56139381915730520537197939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74852509220974027382930585 56139381915730520537197939)
  ·
    refine ⟨84209072873595780805796909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56139381915730520537197939 84209072873595780805796909)
    ·
      refine ⟨31578402327598417802173841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84209072873595780805796909 31578402327598417802173841)
      ·
        refine ⟨23683801745698813351630381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31578402327598417802173841 23683801745698813351630381)
        ·
          refine ⟨8881425654637055006861393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23683801745698813351630381 8881425654637055006861393)
          ·
            refine ⟨6661069240977791255146045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8881425654637055006861393 6661069240977791255146045)
            ·
              refine ⟨2497900965366671720679767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6661069240977791255146045 2497900965366671720679767)
              ·
                refine ⟨3746851448050007581019651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497900965366671720679767 3746851448050007581019651)
                ·
                  refine ⟨5620277172075011371529477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3746851448050007581019651 5620277172075011371529477)
                  ·
                    refine ⟨1053801969764064632161777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5620277172075011371529477 1053801969764064632161777)
                    ·
                      rfl

theorem cell22_3078408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_3078408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078408 prefixEnd_3078408 := by exact prefixLift 3078408
  have htrace : WordTrace (prefixWord ++ tailWord_3078408) baseStart_3078408 baseEnd_3078408 := by
    simpa [prefixWord, tailWord_3078408, baseEnd_3078408] using wordTrace_append hprefix tailTrace_3078408
  have hstable : (prefixWord ++ tailWord_3078408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078408).length < 2 ^ (prefixWord ++ tailWord_3078408).sum := by decide
  have hdescent : baseEnd_3078408 < baseStart_3078408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078417 : List Nat := [1, 2, 2, 1, 1, 15]
def baseStart_3078417 : Nat := 118140960795 + 3078417 * 2 ^ 59
def prefixEnd_3078417 : Nat := 4983230072969 + 3 ^ 40 * 3078417 * 2
def baseEnd_3078417 : Nat := 13009938896888785292429

theorem tailTrace_3078417 : CollatzResearch.WordTrace tailWord_3078417 prefixEnd_3078417 13009938896888785292429 := by
  unfold tailWord_3078417
  simp only [CollatzResearch.WordTrace]
  refine ⟨112279092088428435611473505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74852728058952290407649003 112279092088428435611473505)
  ·
    refine ⟨84209319066321326708605129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112279092088428435611473505 84209319066321326708605129)
    ·
      refine ⟨63156989299740995031453847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84209319066321326708605129 63156989299740995031453847)
      ·
        refine ⟨94735483949611492547180771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63156989299740995031453847 94735483949611492547180771)
        ·
          refine ⟨142103225924417238820771157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94735483949611492547180771 142103225924417238820771157)
          ·
            refine ⟨13009938896888785292429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 142103225924417238820771157 13009938896888785292429)
            ·
              rfl

theorem cell22_3078417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 15].length) (baseStart_3078417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078417 prefixEnd_3078417 := by exact prefixLift 3078417
  have htrace : WordTrace (prefixWord ++ tailWord_3078417) baseStart_3078417 baseEnd_3078417 := by
    simpa [prefixWord, tailWord_3078417, baseEnd_3078417] using wordTrace_append hprefix tailTrace_3078417
  have hstable : (prefixWord ++ tailWord_3078417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078417).length < 2 ^ (prefixWord ++ tailWord_3078417).sum := by decide
  have hdescent : baseEnd_3078417 < baseStart_3078417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078421 : List Nat := [1, 3, 2, 1, 2, 1, 3, 4, 2, 3]
def baseStart_3078421 : Nat := 118140960795 + 3078421 * 2 ^ 59
def prefixEnd_3078421 : Nat := 4983230072969 + 3 ^ 40 * 3078421 * 2
def baseEnd_3078421 : Nat := 1053806419929736931586737

theorem tailTrace_3078421 : CollatzResearch.WordTrace tailWord_3078421 prefixEnd_3078421 1053806419929736931586737 := by
  unfold tailWord_3078421
  simp only [CollatzResearch.WordTrace]
  refine ⟨112279237980413944294619117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74852825320275962863079411 112279237980413944294619117)
  ·
    refine ⟨42104714242655229110482169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112279237980413944294619117 42104714242655229110482169)
    ·
      refine ⟨31578535681991421832861627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42104714242655229110482169 31578535681991421832861627)
      ·
        refine ⟨47367803522987132749292441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31578535681991421832861627 47367803522987132749292441)
        ·
          refine ⟨35525852642240349561969331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47367803522987132749292441 35525852642240349561969331)
          ·
            refine ⟨53288778963360524342953997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35525852642240349561969331 53288778963360524342953997)
            ·
              refine ⟨19983292111260196628607749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53288778963360524342953997 19983292111260196628607749)
              ·
                refine ⟨3746867270861286867863953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19983292111260196628607749 3746867270861286867863953)
                ·
                  refine ⟨2810150453145965150897965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3746867270861286867863953 2810150453145965150897965)
                  ·
                    refine ⟨1053806419929736931586737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810150453145965150897965 1053806419929736931586737)
                    ·
                      rfl

theorem cell22_3078421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_3078421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078421 prefixEnd_3078421 := by exact prefixLift 3078421
  have htrace : WordTrace (prefixWord ++ tailWord_3078421) baseStart_3078421 baseEnd_3078421 := by
    simpa [prefixWord, tailWord_3078421, baseEnd_3078421] using wordTrace_append hprefix tailTrace_3078421
  have hstable : (prefixWord ++ tailWord_3078421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078421).length < 2 ^ (prefixWord ++ tailWord_3078421).sum := by decide
  have hdescent : baseEnd_3078421 < baseStart_3078421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078423 : List Nat := [1, 1, 3, 4, 1, 2, 4, 2, 4]
def baseStart_3078423 : Nat := 118140960795 + 3078423 * 2 ^ 59
def prefixEnd_3078423 : Nat := 4983230072969 + 3 ^ 40 * 3078423 * 2
def baseEnd_3078423 : Nat := 351269034856869864345577

theorem tailTrace_3078423 : CollatzResearch.WordTrace tailWord_3078423 prefixEnd_3078423 351269034856869864345577 := by
  unfold tailWord_3078423
  simp only [CollatzResearch.WordTrace]
  refine ⟨112279310926406698636191923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74852873950937799090794615 112279310926406698636191923)
  ·
    refine ⟨168418966389610047954287885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112279310926406698636191923 168418966389610047954287885)
    ·
      refine ⟨63157112396103767982857957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168418966389610047954287885 63157112396103767982857957)
      ·
        refine ⟨11841958574269456496785867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63157112396103767982857957 11841958574269456496785867)
        ·
          refine ⟨17762937861404184745178801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11841958574269456496785867 17762937861404184745178801)
          ·
            refine ⟨13322203396053138558884101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17762937861404184745178801 13322203396053138558884101)
            ·
              refine ⟨2497913136759963479790769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13322203396053138558884101 2497913136759963479790769)
              ·
                refine ⟨1873434852569972609843077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2497913136759963479790769 1873434852569972609843077)
                ·
                  refine ⟨351269034856869864345577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1873434852569972609843077 351269034856869864345577)
                  ·
                    rfl

theorem cell22_3078423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 4].length) (baseStart_3078423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078423 prefixEnd_3078423 := by exact prefixLift 3078423
  have htrace : WordTrace (prefixWord ++ tailWord_3078423) baseStart_3078423 baseEnd_3078423 := by
    simpa [prefixWord, tailWord_3078423, baseEnd_3078423] using wordTrace_append hprefix tailTrace_3078423
  have hstable : (prefixWord ++ tailWord_3078423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078423).length < 2 ^ (prefixWord ++ tailWord_3078423).sum := by decide
  have hdescent : baseEnd_3078423 < baseStart_3078423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078479 : List Nat := [1, 1, 2, 1, 1, 2, 1, 8, 5]
def baseStart_3078479 : Nat := 118140960795 + 3078479 * 2 ^ 59
def prefixEnd_3078479 : Nat := 4983230072969 + 3 ^ 40 * 3078479 * 2
def baseEnd_3078479 : Nat := 351275424838348037878853

theorem tailTrace_3078479 : CollatzResearch.WordTrace tailWord_3078479 prefixEnd_3078479 351275424838348037878853 := by
  unfold tailWord_3078479
  simp only [CollatzResearch.WordTrace]
  refine ⟨112281353414203820200230491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74854235609469213466820327 112281353414203820200230491)
  ·
    refine ⟨168422030121305730300345737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112281353414203820200230491 168422030121305730300345737)
    ·
      refine ⟨126316522590979297725259303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168422030121305730300345737 126316522590979297725259303)
      ·
        refine ⟨189474783886468946587888955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126316522590979297725259303 189474783886468946587888955)
        ·
          refine ⟨284212175829703419881833433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189474783886468946587888955 284212175829703419881833433)
          ·
            refine ⟨213159131872277564911375075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284212175829703419881833433 213159131872277564911375075)
            ·
              refine ⟨319738697808416347367062613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213159131872277564911375075 319738697808416347367062613)
              ·
                refine ⟨3746937864942379070707765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 319738697808416347367062613 3746937864942379070707765)
                ·
                  refine ⟨351275424838348037878853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3746937864942379070707765 351275424838348037878853)
                  ·
                    rfl

theorem cell22_3078479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 5].length) (baseStart_3078479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078479 prefixEnd_3078479 := by exact prefixLift 3078479
  have htrace : WordTrace (prefixWord ++ tailWord_3078479) baseStart_3078479 baseEnd_3078479 := by
    simpa [prefixWord, tailWord_3078479, baseEnd_3078479] using wordTrace_append hprefix tailTrace_3078479
  have hstable : (prefixWord ++ tailWord_3078479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078479).length < 2 ^ (prefixWord ++ tailWord_3078479).sum := by decide
  have hdescent : baseEnd_3078479 < baseStart_3078479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078517 : List Nat := [1, 3, 4, 1, 2, 3, 1, 3, 1, 3]
def baseStart_3078517 : Nat := 118140960795 + 3078517 * 2 ^ 59
def prefixEnd_3078517 : Nat := 4983230072969 + 3 ^ 40 * 3078517 * 2
def baseEnd_3078517 : Nat := 1053839282691624681186443

theorem tailTrace_3078517 : CollatzResearch.WordTrace tailWord_3078517 prefixEnd_3078517 1053839282691624681186443 := by
  unfold tailWord_3078517
  simp only [CollatzResearch.WordTrace]
  refine ⟨112282739388066152690113805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74855159592044101793409203 112282739388066152690113805)
  ·
    refine ⟨42106027270524807258792677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112282739388066152690113805 42106027270524807258792677)
    ·
      refine ⟨7894880113223401361023627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42106027270524807258792677 7894880113223401361023627)
      ·
        refine ⟨11842320169835102041535441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7894880113223401361023627 11842320169835102041535441)
        ·
          refine ⟨8881740127376326531151581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11842320169835102041535441 8881740127376326531151581)
          ·
            refine ⟨3330652547766122449181843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8881740127376326531151581 3330652547766122449181843)
            ·
              refine ⟨4995978821649183673772765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3330652547766122449181843 4995978821649183673772765)
              ·
                refine ⟨1873492058118443877664787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4995978821649183673772765 1873492058118443877664787)
                ·
                  refine ⟨2810238087177665816497181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873492058118443877664787 2810238087177665816497181)
                  ·
                    refine ⟨1053839282691624681186443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810238087177665816497181 1053839282691624681186443)
                    ·
                      rfl

theorem cell22_3078517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_3078517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078517 prefixEnd_3078517 := by exact prefixLift 3078517
  have htrace : WordTrace (prefixWord ++ tailWord_3078517) baseStart_3078517 baseEnd_3078517 := by
    simpa [prefixWord, tailWord_3078517, baseEnd_3078517] using wordTrace_append hprefix tailTrace_3078517
  have hstable : (prefixWord ++ tailWord_3078517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078517).length < 2 ^ (prefixWord ++ tailWord_3078517).sum := by decide
  have hdescent : baseEnd_3078517 < baseStart_3078517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078588 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_3078588 : Nat := 118140960795 + 3078588 * 2 ^ 59
def prefixEnd_3078588 : Nat := 4983230072969 + 3 ^ 40 * 3078588 * 2
def baseEnd_3078588 : Nat := 1053863587442604162661225

theorem tailTrace_3078588 : CollatzResearch.WordTrace tailWord_3078588 prefixEnd_3078588 1053863587442604162661225 := by
  unfold tailWord_3078588
  simp only [CollatzResearch.WordTrace]
  refine ⟨56142664485404465907974209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74856885980539287877298945 56142664485404465907974209)
  ·
    refine ⟨42106998364053349430980657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56142664485404465907974209 42106998364053349430980657)
    ·
      refine ⟨31580248773040012073235493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42106998364053349430980657 31580248773040012073235493)
      ·
        refine ⟨5921296644945002263731655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31580248773040012073235493 5921296644945002263731655)
        ·
          refine ⟨8881944967417503395597483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5921296644945002263731655 8881944967417503395597483)
          ·
            refine ⟨13322917451126255093396225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8881944967417503395597483 13322917451126255093396225)
            ·
              refine ⟨9992188088344691320047169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13322917451126255093396225 9992188088344691320047169)
              ·
                refine ⟨7494141066258518490035377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9992188088344691320047169 7494141066258518490035377)
                ·
                  refine ⟨5620605799693888867526533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7494141066258518490035377 5620605799693888867526533)
                  ·
                    refine ⟨1053863587442604162661225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5620605799693888867526533 1053863587442604162661225)
                    ·
                      rfl

theorem cell22_3078588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_3078588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078588 prefixEnd_3078588 := by exact prefixLift 3078588
  have htrace : WordTrace (prefixWord ++ tailWord_3078588) baseStart_3078588 baseEnd_3078588 := by
    simpa [prefixWord, tailWord_3078588, baseEnd_3078588] using wordTrace_append hprefix tailTrace_3078588
  have hstable : (prefixWord ++ tailWord_3078588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078588).length < 2 ^ (prefixWord ++ tailWord_3078588).sum := by decide
  have hdescent : baseEnd_3078588 < baseStart_3078588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078618 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 3, 3]
def baseStart_3078618 : Nat := 118140960795 + 3078618 * 2 ^ 59
def prefixEnd_3078618 : Nat := 4983230072969 + 3 ^ 40 * 3078618 * 2
def baseEnd_3078618 : Nat := 1053873857055694084411133

theorem tailTrace_3078618 : CollatzResearch.WordTrace tailWord_3078618 prefixEnd_3078618 1053873857055694084411133 := by
  unfold tailWord_3078618
  simp only [CollatzResearch.WordTrace]
  refine ⟨28071605790175061734885127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74857615440466831293027005 28071605790175061734885127)
  ·
    refine ⟨42107408685262592602327691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28071605790175061734885127 42107408685262592602327691)
    ·
      refine ⟨63161113027893888903491537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42107408685262592602327691 63161113027893888903491537)
      ·
        refine ⟨47370834770920416677618653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63161113027893888903491537 47370834770920416677618653)
        ·
          refine ⟨17764063039095156254106995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47370834770920416677618653 17764063039095156254106995)
          ·
            refine ⟨26646094558642734381160493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17764063039095156254106995 26646094558642734381160493)
            ·
              refine ⟨9992285459491025392935185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26646094558642734381160493 9992285459491025392935185)
              ·
                refine ⟨7494214094618269044701389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9992285459491025392935185 7494214094618269044701389)
                ·
                  refine ⟨2810330285481850891763021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7494214094618269044701389 2810330285481850891763021)
                  ·
                    refine ⟨1053873857055694084411133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810330285481850891763021 1053873857055694084411133)
                    ·
                      rfl

theorem cell22_3078618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_3078618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078618 prefixEnd_3078618 := by exact prefixLift 3078618
  have htrace : WordTrace (prefixWord ++ tailWord_3078618) baseStart_3078618 baseEnd_3078618 := by
    simpa [prefixWord, tailWord_3078618, baseEnd_3078618] using wordTrace_append hprefix tailTrace_3078618
  have hstable : (prefixWord ++ tailWord_3078618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078618).length < 2 ^ (prefixWord ++ tailWord_3078618).sum := by decide
  have hdescent : baseEnd_3078618 < baseStart_3078618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078631 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 7]
def baseStart_3078631 : Nat := 118140960795 + 3078631 * 2 ^ 59
def prefixEnd_3078631 : Nat := 4983230072969 + 3 ^ 40 * 3078631 * 2
def baseEnd_3078631 : Nat := 351292769073788794612031

theorem tailTrace_3078631 : CollatzResearch.WordTrace tailWord_3078631 prefixEnd_3078631 351292769073788794612031 := by
  unfold tailWord_3078631
  simp only [CollatzResearch.WordTrace]
  refine ⟨112286897309653150159763747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74857931539768766773175831 112286897309653150159763747)
  ·
    refine ⟨168430345964479725239645621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112286897309653150159763747 168430345964479725239645621)
    ·
      refine ⟨15790344934169974241216777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168430345964479725239645621 15790344934169974241216777)
      ·
        refine ⟨11842758700627480680912583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15790344934169974241216777 11842758700627480680912583)
        ·
          refine ⟨17764138050941221021368875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11842758700627480680912583 17764138050941221021368875)
          ·
            refine ⟨26646207076411831532053313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17764138050941221021368875 26646207076411831532053313)
            ·
              refine ⟨19984655307308873649039985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26646207076411831532053313 19984655307308873649039985)
              ·
                refine ⟨14988491480481655236779989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19984655307308873649039985 14988491480481655236779989)
                ·
                  refine ⟨351292769073788794612031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14988491480481655236779989 351292769073788794612031)
                  ·
                    rfl

theorem cell22_3078631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 7].length) (baseStart_3078631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078631 prefixEnd_3078631 := by exact prefixLift 3078631
  have htrace : WordTrace (prefixWord ++ tailWord_3078631) baseStart_3078631 baseEnd_3078631 := by
    simpa [prefixWord, tailWord_3078631, baseEnd_3078631] using wordTrace_append hprefix tailTrace_3078631
  have hstable : (prefixWord ++ tailWord_3078631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078631).length < 2 ^ (prefixWord ++ tailWord_3078631).sum := by decide
  have hdescent : baseEnd_3078631 < baseStart_3078631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078635 : List Nat := [1, 1, 1, 1, 2, 3, 6, 3, 1, 3]
def baseStart_3078635 : Nat := 118140960795 + 3078635 * 2 ^ 59
def prefixEnd_3078635 : Nat := 4983230072969 + 3 ^ 40 * 3078635 * 2
def baseEnd_3078635 : Nat := 1053879676503111706736081

theorem tailTrace_3078635 : CollatzResearch.WordTrace tailWord_3078635 prefixEnd_3078635 1053879676503111706736081 := by
  unfold tailWord_3078635
  simp only [CollatzResearch.WordTrace]
  refine ⟨112287043201638658842909359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74858028801092439228606239 112287043201638658842909359)
  ·
    refine ⟨168430564802457988264364039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112287043201638658842909359 168430564802457988264364039)
    ·
      refine ⟨252645847203686982396546059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168430564802457988264364039 252645847203686982396546059)
      ·
        refine ⟨378968770805530473594819089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252645847203686982396546059 378968770805530473594819089)
        ·
          refine ⟨284226578104147855196114317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378968770805530473594819089 284226578104147855196114317)
          ·
            refine ⟨106584966789055445698542869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284226578104147855196114317 106584966789055445698542869)
            ·
              refine ⟨4996170318236974017119197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106584966789055445698542869 4996170318236974017119197)
              ·
                refine ⟨1873563869338865256419699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4996170318236974017119197 1873563869338865256419699)
                ·
                  refine ⟨2810345804008297884629549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873563869338865256419699 2810345804008297884629549)
                  ·
                    refine ⟨1053879676503111706736081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810345804008297884629549 1053879676503111706736081)
                    ·
                      rfl

theorem cell22_3078635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 1, 3].length) (baseStart_3078635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078635 prefixEnd_3078635 := by exact prefixLift 3078635
  have htrace : WordTrace (prefixWord ++ tailWord_3078635) baseStart_3078635 baseEnd_3078635 := by
    simpa [prefixWord, tailWord_3078635, baseEnd_3078635] using wordTrace_append hprefix tailTrace_3078635
  have hstable : (prefixWord ++ tailWord_3078635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078635).length < 2 ^ (prefixWord ++ tailWord_3078635).sum := by decide
  have hdescent : baseEnd_3078635 < baseStart_3078635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078661 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_3078661 : Nat := 118140960795 + 3078661 * 2 ^ 59
def prefixEnd_3078661 : Nat := 4983230072969 + 3 ^ 40 * 3078661 * 2
def baseEnd_3078661 : Nat := 1053888576834456305586001

theorem tailTrace_3078661 : CollatzResearch.WordTrace tailWord_3078661 prefixEnd_3078661 1053888576834456305586001 := by
  unfold tailWord_3078661
  simp only [CollatzResearch.WordTrace]
  refine ⟨112287991499544465283355837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74858660999696310188903891 112287991499544465283355837)
  ·
    refine ⟨42107996812329174481258439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112287991499544465283355837 42107996812329174481258439)
    ·
      refine ⟨63161995218493761721887659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42107996812329174481258439 63161995218493761721887659)
      ·
        refine ⟨94742992827740642582831489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63161995218493761721887659 94742992827740642582831489)
        ·
          refine ⟨71057244620805481937123617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94742992827740642582831489 71057244620805481937123617)
          ·
            refine ⟨53292933465604111452842713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71057244620805481937123617 53292933465604111452842713)
            ·
              refine ⟨39969700099203083589632035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53292933465604111452842713 39969700099203083589632035)
              ·
                refine ⟨59954550148804625384448053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39969700099203083589632035 59954550148804625384448053)
                ·
                  refine ⟨5620739076450433629792005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59954550148804625384448053 5620739076450433629792005)
                  ·
                    refine ⟨1053888576834456305586001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5620739076450433629792005 1053888576834456305586001)
                    ·
                      rfl

theorem cell22_3078661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_3078661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078661 prefixEnd_3078661 := by exact prefixLift 3078661
  have htrace : WordTrace (prefixWord ++ tailWord_3078661) baseStart_3078661 baseEnd_3078661 := by
    simpa [prefixWord, tailWord_3078661, baseEnd_3078661] using wordTrace_append hprefix tailTrace_3078661
  have hstable : (prefixWord ++ tailWord_3078661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078661).length < 2 ^ (prefixWord ++ tailWord_3078661).sum := by decide
  have hdescent : baseEnd_3078661 < baseStart_3078661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078710 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_3078710 : Nat := 118140960795 + 3078710 * 2 ^ 59
def prefixEnd_3078710 : Nat := 4983230072969 + 3 ^ 40 * 3078710 * 2
def baseEnd_3078710 : Nat := 351301783511945503703617

theorem tailTrace_3078710 : CollatzResearch.WordTrace tailWord_3078710 prefixEnd_3078710 351301783511945503703617 := by
  unfold tailWord_3078710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7018111167272934165743099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74859852450911297767926389 7018111167272934165743099)
  ·
    refine ⟨10527166750909401248614649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7018111167272934165743099 10527166750909401248614649)
    ·
      refine ⟨7895375063182050936460987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10527166750909401248614649 7895375063182050936460987)
      ·
        refine ⟨11843062594773076404691481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7895375063182050936460987 11843062594773076404691481)
        ·
          refine ⟨8882296946079807303518611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11843062594773076404691481 8882296946079807303518611)
          ·
            refine ⟨13323445419119710955277917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8882296946079807303518611 13323445419119710955277917)
            ·
              refine ⟨4996292032169891608229219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13323445419119710955277917 4996292032169891608229219)
              ·
                refine ⟨7494438048254837412343829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4996292032169891608229219 7494438048254837412343829)
                ·
                  refine ⟨351301783511945503703617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7494438048254837412343829 351301783511945503703617)
                  ·
                    rfl

theorem cell22_3078710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_3078710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078710 prefixEnd_3078710 := by exact prefixLift 3078710
  have htrace : WordTrace (prefixWord ++ tailWord_3078710) baseStart_3078710 baseEnd_3078710 := by
    simpa [prefixWord, tailWord_3078710, baseEnd_3078710] using wordTrace_append hprefix tailTrace_3078710
  have hstable : (prefixWord ++ tailWord_3078710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078710).length < 2 ^ (prefixWord ++ tailWord_3078710).sum := by decide
  have hdescent : baseEnd_3078710 < baseStart_3078710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078725 : List Nat := [1, 3, 1, 1, 1, 6, 1, 3, 2, 3]
def baseStart_3078725 : Nat := 118140960795 + 3078725 * 2 ^ 59
def prefixEnd_3078725 : Nat := 4983230072969 + 3 ^ 40 * 3078725 * 2
def baseEnd_3078725 : Nat := 1053910485342381471985805

theorem tailTrace_3078725 : CollatzResearch.WordTrace tailWord_3078725 prefixEnd_3078725 1053910485342381471985805 := by
  unfold tailWord_3078725
  simp only [CollatzResearch.WordTrace]
  refine ⟨112290325771312604213685629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74860217180875069475790419 112290325771312604213685629)
  ·
    refine ⟨42108872164242226580132111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112290325771312604213685629 42108872164242226580132111)
    ·
      refine ⟨63163308246363339870198167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42108872164242226580132111 63163308246363339870198167)
      ·
        refine ⟨94744962369545009805297251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63163308246363339870198167 94744962369545009805297251)
        ·
          refine ⟨142117443554317514707945877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94744962369545009805297251 142117443554317514707945877)
          ·
            refine ⟨6661755166608633501934963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142117443554317514707945877 6661755166608633501934963)
            ·
              refine ⟨9992632749912950252902445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6661755166608633501934963 9992632749912950252902445)
              ·
                refine ⟨3747237281217356344838417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9992632749912950252902445 3747237281217356344838417)
                ·
                  refine ⟨2810427960913017258628813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3747237281217356344838417 2810427960913017258628813)
                  ·
                    refine ⟨1053910485342381471985805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810427960913017258628813 1053910485342381471985805)
                    ·
                      rfl

theorem cell22_3078725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_3078725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078725 prefixEnd_3078725 := by exact prefixLift 3078725
  have htrace : WordTrace (prefixWord ++ tailWord_3078725) baseStart_3078725 baseEnd_3078725 := by
    simpa [prefixWord, tailWord_3078725, baseEnd_3078725] using wordTrace_append hprefix tailTrace_3078725
  have hstable : (prefixWord ++ tailWord_3078725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078725).length < 2 ^ (prefixWord ++ tailWord_3078725).sum := by decide
  have hdescent : baseEnd_3078725 < baseStart_3078725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078740 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3078740 : Nat := 118140960795 + 3078740 * 2 ^ 59
def prefixEnd_3078740 : Nat := 4983230072969 + 3 ^ 40 * 3078740 * 2
def baseEnd_3078740 : Nat := 1053915620148926432860759

theorem tailTrace_3078740 : CollatzResearch.WordTrace tailWord_3078740 prefixEnd_3078740 1053915620148926432860759 := by
  unfold tailWord_3078740
  simp only [CollatzResearch.WordTrace]
  refine ⟨56145436433129130887740837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74860581910838841183654449 56145436433129130887740837)
  ·
    refine ⟨10527269331211712041451407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56145436433129130887740837 10527269331211712041451407)
    ·
      refine ⟨15790903996817568062177111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10527269331211712041451407 15790903996817568062177111)
      ·
        refine ⟨23686355995226352093265667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15790903996817568062177111 23686355995226352093265667)
        ·
          refine ⟨35529533992839528139898501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23686355995226352093265667 35529533992839528139898501)
          ·
            refine ⟨6661787623657411526230969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35529533992839528139898501 6661787623657411526230969)
            ·
              refine ⟨4996340717743058644673227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6661787623657411526230969 4996340717743058644673227)
              ·
                refine ⟨7494511076614587967009841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4996340717743058644673227 7494511076614587967009841)
                ·
                  refine ⟨5620883307460940975257381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7494511076614587967009841 5620883307460940975257381)
                  ·
                    refine ⟨1053915620148926432860759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5620883307460940975257381 1053915620148926432860759)
                    ·
                      rfl

theorem cell22_3078740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3078740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078740 prefixEnd_3078740 := by exact prefixLift 3078740
  have htrace : WordTrace (prefixWord ++ tailWord_3078740) baseStart_3078740 baseEnd_3078740 := by
    simpa [prefixWord, tailWord_3078740, baseEnd_3078740] using wordTrace_append hprefix tailTrace_3078740
  have hstable : (prefixWord ++ tailWord_3078740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078740).length < 2 ^ (prefixWord ++ tailWord_3078740).sum := by decide
  have hdescent : baseEnd_3078740 < baseStart_3078740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078751 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 4, 6]
def baseStart_3078751 : Nat := 118140960795 + 3078751 * 2 ^ 59
def prefixEnd_3078751 : Nat := 4983230072969 + 3 ^ 40 * 3078751 * 2
def baseEnd_3078751 : Nat := 1053919385673726070835725

theorem tailTrace_3078751 : CollatzResearch.WordTrace tailWord_3078751 prefixEnd_3078751 1053919385673726070835725 := by
  unfold tailWord_3078751
  simp only [CollatzResearch.WordTrace]
  refine ⟨112291274069218410654132107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74860849379478940436088071 112291274069218410654132107)
  ·
    refine ⟨168436911103827615981198161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112291274069218410654132107 168436911103827615981198161)
    ·
      refine ⟨126327683327870711985898621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168436911103827615981198161 126327683327870711985898621)
      ·
        refine ⟨47372881247951516994711983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126327683327870711985898621 47372881247951516994711983)
        ·
          refine ⟨71059321871927275492067975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47372881247951516994711983 71059321871927275492067975)
          ·
            refine ⟨106588982807890913238101963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71059321871927275492067975 106588982807890913238101963)
            ·
              refine ⟨159883474211836369857152945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106588982807890913238101963 159883474211836369857152945)
              ·
                refine ⟨119912605658877277392864709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159883474211836369857152945 119912605658877277392864709)
                ·
                  refine ⟨22483613561039489511162133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119912605658877277392864709 22483613561039489511162133)
                  ·
                    refine ⟨1053919385673726070835725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22483613561039489511162133 1053919385673726070835725)
                    ·
                      rfl

theorem cell22_3078751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_3078751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078751 prefixEnd_3078751 := by exact prefixLift 3078751
  have htrace : WordTrace (prefixWord ++ tailWord_3078751) baseStart_3078751 baseEnd_3078751 := by
    simpa [prefixWord, tailWord_3078751, baseEnd_3078751] using wordTrace_append hprefix tailTrace_3078751
  have hstable : (prefixWord ++ tailWord_3078751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078751).length < 2 ^ (prefixWord ++ tailWord_3078751).sum := by decide
  have hdescent : baseEnd_3078751 < baseStart_3078751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078798 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_3078798 : Nat := 118140960795 + 3078798 * 2 ^ 59
def prefixEnd_3078798 : Nat := 4983230072969 + 3 ^ 40 * 3078798 * 2
def baseEnd_3078798 : Nat := 1053935474734233614910581

theorem tailTrace_3078798 : CollatzResearch.WordTrace tailWord_3078798 prefixEnd_3078798 1053935474734233614910581 := by
  unfold tailWord_3078798
  simp only [CollatzResearch.WordTrace]
  refine ⟨14036623537506017210136631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74861992200032091787395365 14036623537506017210136631)
  ·
    refine ⟨21054935306259025815204947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14036623537506017210136631 21054935306259025815204947)
    ·
      refine ⟨31582402959388538722807421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21054935306259025815204947 31582402959388538722807421)
      ·
        refine ⟨11843401109770702021052783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31582402959388538722807421 11843401109770702021052783)
        ·
          refine ⟨17765101664656053031579175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11843401109770702021052783 17765101664656053031579175)
          ·
            refine ⟨26647652496984079547368763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17765101664656053031579175 26647652496984079547368763)
            ·
              refine ⟨39971478745476119321053145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26647652496984079547368763 39971478745476119321053145)
              ·
                refine ⟨29978609059107089490789859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39971478745476119321053145 29978609059107089490789859)
                ·
                  refine ⟨44967913588660634236184789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29978609059107089490789859 44967913588660634236184789)
                  ·
                    refine ⟨1053935474734233614910581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44967913588660634236184789 1053935474734233614910581)
                    ·
                      rfl

theorem cell22_3078798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_3078798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078798 prefixEnd_3078798 := by exact prefixLift 3078798
  have htrace : WordTrace (prefixWord ++ tailWord_3078798) baseStart_3078798 baseEnd_3078798 := by
    simpa [prefixWord, tailWord_3078798, baseEnd_3078798] using wordTrace_append hprefix tailTrace_3078798
  have hstable : (prefixWord ++ tailWord_3078798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078798).length < 2 ^ (prefixWord ++ tailWord_3078798).sum := by decide
  have hdescent : baseEnd_3078798 < baseStart_3078798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078804 : List Nat := [2, 4, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_3078804 : Nat := 118140960795 + 3078804 * 2 ^ 59
def prefixEnd_3078804 : Nat := 4983230072969 + 3 ^ 40 * 3078804 * 2
def baseEnd_3078804 : Nat := 1053937528656851599260563

theorem tailTrace_3078804 : CollatzResearch.WordTrace tailWord_3078804 prefixEnd_3078804 1053937528656851599260563 := by
  unfold tailWord_3078804
  simp only [CollatzResearch.WordTrace]
  refine ⟨56146603569013200352905733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74862138092017600470540977 56146603569013200352905733)
  ·
    refine ⟨10527488169189975066169825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56146603569013200352905733 10527488169189975066169825)
    ·
      refine ⟨7895616126892481299627369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10527488169189975066169825 7895616126892481299627369)
      ·
        refine ⟨5921712095169360974720527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7895616126892481299627369 5921712095169360974720527)
        ·
          refine ⟨8882568142754041462080791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5921712095169360974720527 8882568142754041462080791)
          ·
            refine ⟨13323852214131062193121187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8882568142754041462080791 13323852214131062193121187)
            ·
              refine ⟨19985778321196593289681781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13323852214131062193121187 19985778321196593289681781)
              ·
                refine ⟨1873666717612180620907667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19985778321196593289681781 1873666717612180620907667)
                ·
                  refine ⟨2810500076418270931361501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873666717612180620907667 2810500076418270931361501)
                  ·
                    refine ⟨1053937528656851599260563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810500076418270931361501 1053937528656851599260563)
                    ·
                      rfl

theorem cell22_3078804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_3078804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078804 prefixEnd_3078804 := by exact prefixLift 3078804
  have htrace : WordTrace (prefixWord ++ tailWord_3078804) baseStart_3078804 baseEnd_3078804 := by
    simpa [prefixWord, tailWord_3078804, baseEnd_3078804] using wordTrace_append hprefix tailTrace_3078804
  have hstable : (prefixWord ++ tailWord_3078804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078804).length < 2 ^ (prefixWord ++ tailWord_3078804).sum := by decide
  have hdescent : baseEnd_3078804 < baseStart_3078804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078817 : List Nat := [1, 2, 3, 3, 3, 2, 1, 2, 5]
def baseStart_3078817 : Nat := 118140960795 + 3078817 * 2 ^ 59
def prefixEnd_3078817 : Nat := 4983230072969 + 3 ^ 40 * 3078817 * 2
def baseEnd_3078817 : Nat := 351313992940841299561841

theorem tailTrace_3078817 : CollatzResearch.WordTrace tailWord_3078817 prefixEnd_3078817 351313992940841299561841 := by
  unfold tailWord_3078817
  simp only [CollatzResearch.WordTrace]
  refine ⟨112293681286979303926034705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74862454191319535950689803 112293681286979303926034705)
  ·
    refine ⟨84220260965234477944526029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112293681286979303926034705 84220260965234477944526029)
    ·
      refine ⟨31582597861962929229197261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84220260965234477944526029 31582597861962929229197261)
      ·
        refine ⟨11843474198236098460948973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31582597861962929229197261 11843474198236098460948973)
        ·
          refine ⟨4441302824338536922855865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11843474198236098460948973 4441302824338536922855865)
          ·
            refine ⟨3330977118253902692141899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4441302824338536922855865 3330977118253902692141899)
            ·
              refine ⟨4996465677380854038212849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3330977118253902692141899 4996465677380854038212849)
              ·
                refine ⟨3747349258035640528659637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4996465677380854038212849 3747349258035640528659637)
                ·
                  refine ⟨351313992940841299561841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3747349258035640528659637 351313992940841299561841)
                  ·
                    rfl

theorem cell22_3078817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 5].length) (baseStart_3078817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3078817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3078817 prefixEnd_3078817 := by exact prefixLift 3078817
  have htrace : WordTrace (prefixWord ++ tailWord_3078817) baseStart_3078817 baseEnd_3078817 := by
    simpa [prefixWord, tailWord_3078817, baseEnd_3078817] using wordTrace_append hprefix tailTrace_3078817
  have hstable : (prefixWord ++ tailWord_3078817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078817).length < 2 ^ (prefixWord ++ tailWord_3078817).sum := by decide
  have hdescent : baseEnd_3078817 < baseStart_3078817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
