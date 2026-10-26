import V185TrunkScan23Chunk0336

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1992925 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1992925 : Nat := 118140960795 + 1992925 * 2 ^ 59
def prefixEnd_1992925 : Nat := 4983230072969 + 3 ^ 40 * 1992925 * 2
def baseEnd_1992925 : Nat := 1023328433361720405472211

theorem tailTrace_1992925 : CollatzResearch.WordTrace tailWord_1992925 prefixEnd_1992925 1023328433361720405472211 := by
  unfold tailWord_1992925
  simp only [CollatzResearch.WordTrace]
  refine ⟨72687946304980564337308229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48458630869987042891538819 72687946304980564337308229)
  ·
    refine ⟨13628989932183855813245293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72687946304980564337308229 13628989932183855813245293)
    ·
      refine ⟨5110871224568945929966985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13628989932183855813245293 5110871224568945929966985)
      ·
        refine ⟨3833153418426709447475239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5110871224568945929966985 3833153418426709447475239)
        ·
          refine ⟨5749730127640064171212859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3833153418426709447475239 5749730127640064171212859)
          ·
            refine ⟨8624595191460096256819289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5749730127640064171212859 8624595191460096256819289)
            ·
              refine ⟨6468446393595072192614467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8624595191460096256819289 6468446393595072192614467)
              ·
                refine ⟨9702669590392608288921701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6468446393595072192614467 9702669590392608288921701)
                ·
                  refine ⟨1819250548198614054172819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9702669590392608288921701 1819250548198614054172819)
                  ·
                    refine ⟨2728875822297921081259229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1819250548198614054172819 2728875822297921081259229)
                    ·
                      refine ⟨1023328433361720405472211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2728875822297921081259229 1023328433361720405472211)
                      ·
                        rfl

theorem cell23_1992925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1992925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992925 prefixEnd_1992925 := by exact prefixLift 1992925
  have htrace : WordTrace (prefixWord ++ tailWord_1992925) baseStart_1992925 baseEnd_1992925 := by
    simpa [prefixWord, tailWord_1992925, baseEnd_1992925] using wordTrace_append hprefix tailTrace_1992925
  have hstable : (prefixWord ++ tailWord_1992925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992925).length < 2 ^ (prefixWord ++ tailWord_1992925).sum := by decide
  have hdescent : baseEnd_1992925 < baseStart_1992925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992944 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 6]
def baseStart_1992944 : Nat := 118140960795 + 1992944 * 2 ^ 59
def prefixEnd_1992944 : Nat := 4983230072969 + 3 ^ 40 * 1992944 * 2
def baseEnd_1992944 : Nat := 1023338189494155831134623

theorem tailTrace_1992944 : CollatzResearch.WordTrace tailWord_1992944 prefixEnd_1992944 1023338189494155831134623 := by
  unfold tailWord_1992944
  simp only [CollatzResearch.WordTrace]
  refine ⟨36344319645955865291124943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48459092861274487054833257 36344319645955865291124943)
  ·
    refine ⟨54516479468933797936687415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36344319645955865291124943 54516479468933797936687415)
    ·
      refine ⟨81774719203400696905031123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54516479468933797936687415 81774719203400696905031123)
      ·
        refine ⟨122662078805101045357546685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81774719203400696905031123 122662078805101045357546685)
        ·
          refine ⟨45998279551912892009080007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122662078805101045357546685 45998279551912892009080007)
          ·
            refine ⟨68997419327869338013620011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45998279551912892009080007 68997419327869338013620011)
            ·
              refine ⟨103496128991804007020430017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68997419327869338013620011 103496128991804007020430017)
              ·
                refine ⟨77622096743853005265322513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103496128991804007020430017 77622096743853005265322513)
                ·
                  refine ⟨58216572557889753948991885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77622096743853005265322513 58216572557889753948991885)
                  ·
                    refine ⟨21831214709208657730871957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58216572557889753948991885 21831214709208657730871957)
                    ·
                      refine ⟨1023338189494155831134623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21831214709208657730871957 1023338189494155831134623)
                      ·
                        rfl

theorem cell23_1992944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_1992944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1992944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1992944 prefixEnd_1992944 := by exact prefixLift 1992944
  have htrace : WordTrace (prefixWord ++ tailWord_1992944) baseStart_1992944 baseEnd_1992944 := by
    simpa [prefixWord, tailWord_1992944, baseEnd_1992944] using wordTrace_append hprefix tailTrace_1992944
  have hstable : (prefixWord ++ tailWord_1992944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992944).length < 2 ^ (prefixWord ++ tailWord_1992944).sum := by decide
  have hdescent : baseEnd_1992944 < baseStart_1992944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993005 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 7]
def baseStart_1993005 : Nat := 118140960795 + 1993005 * 2 ^ 59
def prefixEnd_1993005 : Nat := 4983230072969 + 3 ^ 40 * 1993005 * 2
def baseEnd_1993005 : Nat := 113707723534897788052427

theorem tailTrace_1993005 : CollatzResearch.WordTrace tailWord_1993005 prefixEnd_1993005 113707723534897788052427 := by
  unfold tailWord_1993005
  simp only [CollatzResearch.WordTrace]
  refine ⟨72690864144690738000220469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48460576096460492000146979 72690864144690738000220469)
  ·
    refine ⟨6814768513564756687520669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72690864144690738000220469 6814768513564756687520669)
    ·
      refine ⟨2555538192586783757820251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6814768513564756687520669 2555538192586783757820251)
      ·
        refine ⟨3833307288880175636730377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2555538192586783757820251 3833307288880175636730377)
        ·
          refine ⟨2874980466660131727547783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3833307288880175636730377 2874980466660131727547783)
          ·
            refine ⟨4312470699990197591321675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2874980466660131727547783 4312470699990197591321675)
            ·
              refine ⟨6468706049985296386982513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312470699990197591321675 6468706049985296386982513)
              ·
                refine ⟨4851529537488972290236885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6468706049985296386982513 4851529537488972290236885)
                ·
                  refine ⟨113707723534897788052427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4851529537488972290236885 113707723534897788052427)
                  ·
                    rfl

theorem cell23_1993005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_1993005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993005 prefixEnd_1993005 := by exact prefixLift 1993005
  have htrace : WordTrace (prefixWord ++ tailWord_1993005) baseStart_1993005 baseEnd_1993005 := by
    simpa [prefixWord, tailWord_1993005, baseEnd_1993005] using wordTrace_append hprefix tailTrace_1993005
  have hstable : (prefixWord ++ tailWord_1993005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993005).length < 2 ^ (prefixWord ++ tailWord_1993005).sum := by decide
  have hdescent : baseEnd_1993005 < baseStart_1993005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993018 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 2, 5]
def baseStart_1993018 : Nat := 118140960795 + 1993018 * 2 ^ 59
def prefixEnd_1993018 : Nat := 4983230072969 + 3 ^ 40 * 1993018 * 2
def baseEnd_1993018 : Nat := 341125395687529513869761

theorem tailTrace_1993018 : CollatzResearch.WordTrace tailWord_1993018 prefixEnd_1993018 341125395687529513869761 := by
  unfold tailWord_1993018
  simp only [CollatzResearch.WordTrace]
  refine ⟨18172834573410910305110927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48460892195762427480295805 18172834573410910305110927)
  ·
    refine ⟨27259251860116365457666391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18172834573410910305110927 27259251860116365457666391)
    ·
      refine ⟨40888877790174548186499587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27259251860116365457666391 40888877790174548186499587)
      ·
        refine ⟨61333316685261822279749381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40888877790174548186499587 61333316685261822279749381)
        ·
          refine ⟨11499996878486591677453009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61333316685261822279749381 11499996878486591677453009)
          ·
            refine ⟨8624997658864943758089757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11499996878486591677453009 8624997658864943758089757)
            ·
              refine ⟨3234374122074353909283659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8624997658864943758089757 3234374122074353909283659)
              ·
                refine ⟨4851561183111530863925489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3234374122074353909283659 4851561183111530863925489)
                ·
                  refine ⟨3638670887333648147944117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4851561183111530863925489 3638670887333648147944117)
                  ·
                    refine ⟨341125395687529513869761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3638670887333648147944117 341125395687529513869761)
                    ·
                      rfl

theorem cell23_1993018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_1993018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993018 prefixEnd_1993018 := by exact prefixLift 1993018
  have htrace : WordTrace (prefixWord ++ tailWord_1993018) baseStart_1993018 baseEnd_1993018 := by
    simpa [prefixWord, tailWord_1993018, baseEnd_1993018] using wordTrace_append hprefix tailTrace_1993018
  have hstable : (prefixWord ++ tailWord_1993018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993018).length < 2 ^ (prefixWord ++ tailWord_1993018).sum := by decide
  have hdescent : baseEnd_1993018 < baseStart_1993018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993112 : List Nat := [2, 1, 2, 5, 1, 3, 2, 1, 6]
def baseStart_1993112 : Nat := 118140960795 + 1993112 * 2 ^ 59
def prefixEnd_1993112 : Nat := 4983230072969 + 3 ^ 40 * 1993112 * 2
def baseEnd_1993112 : Nat := 113713828249345685981539

theorem tailTrace_1993112 : CollatzResearch.WordTrace tailWord_1993112 prefixEnd_1993112 113713828249345685981539 := by
  unfold tailWord_1993112
  simp only [CollatzResearch.WordTrace]
  refine ⟨36347383377651547637182795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48463177836868730182910393 36347383377651547637182795)
  ·
    refine ⟨54521075066477321455774193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36347383377651547637182795 54521075066477321455774193)
    ·
      refine ⟨40890806299857991091830645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54521075066477321455774193 40890806299857991091830645)
      ·
        refine ⟨3833513090611686664859123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40890806299857991091830645 3833513090611686664859123)
        ·
          refine ⟨5750269635917529997288685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3833513090611686664859123 5750269635917529997288685)
          ·
            refine ⟨2156351113469073748983257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5750269635917529997288685 2156351113469073748983257)
            ·
              refine ⟨1617263335101805311737443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156351113469073748983257 1617263335101805311737443)
              ·
                refine ⟨2425895002652707967606165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617263335101805311737443 2425895002652707967606165)
                ·
                  refine ⟨113713828249345685981539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2425895002652707967606165 113713828249345685981539)
                  ·
                    rfl

theorem cell23_1993112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 6].length) (baseStart_1993112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993112 prefixEnd_1993112 := by exact prefixLift 1993112
  have htrace : WordTrace (prefixWord ++ tailWord_1993112) baseStart_1993112 baseEnd_1993112 := by
    simpa [prefixWord, tailWord_1993112, baseEnd_1993112] using wordTrace_append hprefix tailTrace_1993112
  have hstable : (prefixWord ++ tailWord_1993112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993112).length < 2 ^ (prefixWord ++ tailWord_1993112).sum := by decide
  have hdescent : baseEnd_1993112 < baseStart_1993112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993138 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_1993138 : Nat := 118140960795 + 1993138 * 2 ^ 59
def prefixEnd_1993138 : Nat := 4983230072969 + 3 ^ 40 * 1993138 * 2
def baseEnd_1993138 : Nat := 341145934913709357369577

theorem tailTrace_1993138 : CollatzResearch.WordTrace tailWord_1993138 prefixEnd_1993138 341145934913709357369577 := by
  unfold tailWord_1993138
  simp only [CollatzResearch.WordTrace]
  refine ⟨18173928763302225428703017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48463810035472601143208045 18173928763302225428703017)
  ·
    refine ⟨13630446572476669071527263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18173928763302225428703017 13630446572476669071527263)
    ·
      refine ⟨20445669858715003607290895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13630446572476669071527263 20445669858715003607290895)
      ·
        refine ⟨30668504788072505410936343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20445669858715003607290895 30668504788072505410936343)
        ·
          refine ⟨46002757182108758116404515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30668504788072505410936343 46002757182108758116404515)
          ·
            refine ⟨69004135773163137174606773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46002757182108758116404515 69004135773163137174606773)
            ·
              refine ⟨6469137728734044110119385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69004135773163137174606773 6469137728734044110119385)
              ·
                refine ⟨4851853296550533082589539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6469137728734044110119385 4851853296550533082589539)
                ·
                  refine ⟨7277779944825799623884309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4851853296550533082589539 7277779944825799623884309)
                  ·
                    refine ⟨341145934913709357369577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7277779944825799623884309 341145934913709357369577)
                    ·
                      rfl

theorem cell23_1993138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_1993138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993138 prefixEnd_1993138 := by exact prefixLift 1993138
  have htrace : WordTrace (prefixWord ++ tailWord_1993138) baseStart_1993138 baseEnd_1993138 := by
    simpa [prefixWord, tailWord_1993138, baseEnd_1993138] using wordTrace_append hprefix tailTrace_1993138
  have hstable : (prefixWord ++ tailWord_1993138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993138).length < 2 ^ (prefixWord ++ tailWord_1993138).sum := by decide
  have hdescent : baseEnd_1993138 < baseStart_1993138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993156 : List Nat := [2, 3, 3, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_1993156 : Nat := 118140960795 + 1993156 * 2 ^ 59
def prefixEnd_1993156 : Nat := 4983230072969 + 3 ^ 40 * 1993156 * 2
def baseEnd_1993156 : Nat := 1023447047392909001683649

theorem tailTrace_1993156 : CollatzResearch.WordTrace tailWord_1993156 prefixEnd_1993156 1023447047392909001683649 := by
  unfold tailWord_1993156
  simp only [CollatzResearch.WordTrace]
  refine ⟨36348185783571845394483661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48464247711429127192644881 36348185783571845394483661)
  ·
    refine ⟨13630569668839442022931373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36348185783571845394483661 13630569668839442022931373)
    ·
      refine ⟨5111463625814790758599265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13630569668839442022931373 5111463625814790758599265)
      ·
        refine ⟨3833597719361093068949449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5111463625814790758599265 3833597719361093068949449)
        ·
          refine ⟨2875198289520819801712087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3833597719361093068949449 2875198289520819801712087)
          ·
            refine ⟨4312797434281229702568131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875198289520819801712087 4312797434281229702568131)
            ·
              refine ⟨6469196151421844553852197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312797434281229702568131 6469196151421844553852197)
              ·
                refine ⟨1212974278391595853847287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6469196151421844553852197 1212974278391595853847287)
                ·
                  refine ⟨1819461417587393780770931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1212974278391595853847287 1819461417587393780770931)
                  ·
                    refine ⟨2729192126381090671156397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1819461417587393780770931 2729192126381090671156397)
                    ·
                      refine ⟨1023447047392909001683649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2729192126381090671156397 1023447047392909001683649)
                      ·
                        rfl

theorem cell23_1993156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_1993156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993156 prefixEnd_1993156 := by exact prefixLift 1993156
  have htrace : WordTrace (prefixWord ++ tailWord_1993156) baseStart_1993156 baseEnd_1993156 := by
    simpa [prefixWord, tailWord_1993156, baseEnd_1993156] using wordTrace_append hprefix tailTrace_1993156
  have hstable : (prefixWord ++ tailWord_1993156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993156).length < 2 ^ (prefixWord ++ tailWord_1993156).sum := by decide
  have hdescent : baseEnd_1993156 < baseStart_1993156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993162 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 3, 2, 2]
def baseStart_1993162 : Nat := 118140960795 + 1993162 * 2 ^ 59
def prefixEnd_1993162 : Nat := 4983230072969 + 3 ^ 40 * 1993162 * 2
def baseEnd_1993162 : Nat := 1023450128276835978208621

theorem tailTrace_1993162 : CollatzResearch.WordTrace tailWord_1993162 prefixEnd_1993162 1023450128276835978208621 := by
  unfold tailWord_1993162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18174147601280488453421435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48464393603414635875790493 18174147601280488453421435)
  ·
    refine ⟨27261221401920732680132153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18174147601280488453421435 27261221401920732680132153)
    ·
      refine ⟨20445916051440549510099115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27261221401920732680132153 20445916051440549510099115)
      ·
        refine ⟨30668874077160824265148673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20445916051440549510099115 30668874077160824265148673)
        ·
          refine ⟨23001655557870618198861505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30668874077160824265148673 23001655557870618198861505)
          ·
            refine ⟨17251241668402963649146129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23001655557870618198861505 17251241668402963649146129)
            ·
              refine ⟨12938431251302222736859597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17251241668402963649146129 12938431251302222736859597)
              ·
                refine ⟨4851911719238333526322349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12938431251302222736859597 4851911719238333526322349)
                ·
                  refine ⟨1819466894714375072370881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4851911719238333526322349 1819466894714375072370881)
                  ·
                    refine ⟨1364600171035781304278161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1819466894714375072370881 1364600171035781304278161)
                    ·
                      refine ⟨1023450128276835978208621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1364600171035781304278161 1023450128276835978208621)
                      ·
                        rfl

theorem cell23_1993162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_1993162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993162 prefixEnd_1993162 := by exact prefixLift 1993162
  have htrace : WordTrace (prefixWord ++ tailWord_1993162) baseStart_1993162 baseEnd_1993162 := by
    simpa [prefixWord, tailWord_1993162, baseEnd_1993162] using wordTrace_append hprefix tailTrace_1993162
  have hstable : (prefixWord ++ tailWord_1993162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993162).length < 2 ^ (prefixWord ++ tailWord_1993162).sum := by decide
  have hdescent : baseEnd_1993162 < baseStart_1993162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993172 : List Nat := [2, 4, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_1993172 : Nat := 118140960795 + 1993172 * 2 ^ 59
def prefixEnd_1993172 : Nat := 4983230072969 + 3 ^ 40 * 1993172 * 2
def baseEnd_1993172 : Nat := 341151754361126979694525

theorem tailTrace_1993172 : CollatzResearch.WordTrace tailWord_1993172 prefixEnd_1993172 341151754361126979694525 := by
  unfold tailWord_1993172
  simp only [CollatzResearch.WordTrace]
  refine ⟨36348477567542862760774885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48464636756723817014366513 36348477567542862760774885)
  ·
    refine ⟨6815339543914286767645291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36348477567542862760774885 6815339543914286767645291)
    ·
      refine ⟨10223009315871430151467937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6815339543914286767645291 10223009315871430151467937)
      ·
        refine ⟨7667256986903572613600953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10223009315871430151467937 7667256986903572613600953)
        ·
          refine ⟨5750442740177679460200715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7667256986903572613600953 5750442740177679460200715)
          ·
            refine ⟨8625664110266519190301073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5750442740177679460200715 8625664110266519190301073)
            ·
              refine ⟨6469248082699889392725805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8625664110266519190301073 6469248082699889392725805)
              ·
                refine ⟨2425968031012458522272177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6469248082699889392725805 2425968031012458522272177)
                ·
                  refine ⟨1819476023259343891704133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2425968031012458522272177 1819476023259343891704133)
                  ·
                    refine ⟨341151754361126979694525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1819476023259343891704133 341151754361126979694525)
                    ·
                      rfl

theorem cell23_1993172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_1993172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993172 prefixEnd_1993172 := by exact prefixLift 1993172
  have htrace : WordTrace (prefixWord ++ tailWord_1993172) baseStart_1993172 baseEnd_1993172 := by
    simpa [prefixWord, tailWord_1993172, baseEnd_1993172] using wordTrace_append hprefix tailTrace_1993172
  have hstable : (prefixWord ++ tailWord_1993172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993172).length < 2 ^ (prefixWord ++ tailWord_1993172).sum := by decide
  have hdescent : baseEnd_1993172 < baseStart_1993172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993195 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 4, 1, 3]
def baseStart_1993195 : Nat := 118140960795 + 1993195 * 2 ^ 59
def prefixEnd_1993195 : Nat := 4983230072969 + 3 ^ 40 * 1993195 * 2
def baseEnd_1993195 : Nat := 1023467073138434349095969

theorem tailTrace_1993195 : CollatzResearch.WordTrace tailWord_1993195 prefixEnd_1993195 1023467073138434349095969 := by
  unfold tailWord_1993195
  simp only [CollatzResearch.WordTrace]
  refine ⟨72697794014002400449637039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48465196009334933633091359 72697794014002400449637039)
  ·
    refine ⟨109046691021003600674455559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72697794014002400449637039 109046691021003600674455559)
    ·
      refine ⟨163570036531505401011683339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109046691021003600674455559 163570036531505401011683339)
      ·
        refine ⟨245355054797258101517525009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163570036531505401011683339 245355054797258101517525009)
        ·
          refine ⟨184016291097943576138143757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245355054797258101517525009 184016291097943576138143757)
          ·
            refine ⟨69006109161728841051803909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184016291097943576138143757 69006109161728841051803909)
            ·
              refine ⟨12938645467824157697213233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69006109161728841051803909 12938645467824157697213233)
              ·
                refine ⟨9703984100868118272909925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12938645467824157697213233 9703984100868118272909925)
                ·
                  refine ⟨1819497018912772176170611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9703984100868118272909925 1819497018912772176170611)
                  ·
                    refine ⟨2729245528369158264255917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1819497018912772176170611 2729245528369158264255917)
                    ·
                      refine ⟨1023467073138434349095969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2729245528369158264255917 1023467073138434349095969)
                      ·
                        rfl

theorem cell23_1993195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 1, 3].length) (baseStart_1993195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993195 prefixEnd_1993195 := by exact prefixLift 1993195
  have htrace : WordTrace (prefixWord ++ tailWord_1993195) baseStart_1993195 baseEnd_1993195 := by
    simpa [prefixWord, tailWord_1993195, baseEnd_1993195] using wordTrace_append hprefix tailTrace_1993195
  have hstable : (prefixWord ++ tailWord_1993195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993195).length < 2 ^ (prefixWord ++ tailWord_1993195).sum := by decide
  have hdescent : baseEnd_1993195 < baseStart_1993195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993269 : List Nat := [1, 3, 3, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_1993269 : Nat := 118140960795 + 1993269 * 2 ^ 59
def prefixEnd_1993269 : Nat := 4983230072969 + 3 ^ 40 * 1993269 * 2
def baseEnd_1993269 : Nat := 1023505070706867059570629

theorem tailTrace_1993269 : CollatzResearch.WordTrace tailWord_1993269 prefixEnd_1993269 1023505070706867059570629 := by
  unfold tailWord_1993269
  simp only [CollatzResearch.WordTrace]
  refine ⟨72700493015734311087830861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48466995343822874058553907 72700493015734311087830861)
  ·
    refine ⟨27262684880900366657936573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72700493015734311087830861 27262684880900366657936573)
    ·
      refine ⟨10223506830337637496726215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27262684880900366657936573 10223506830337637496726215)
      ·
        refine ⟨15335260245506456245089323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10223506830337637496726215 15335260245506456245089323)
        ·
          refine ⟨23002890368259684367633985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15335260245506456245089323 23002890368259684367633985)
          ·
            refine ⟨17252167776194763275725489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23002890368259684367633985 17252167776194763275725489)
            ·
              refine ⟨12939125832146072456794117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17252167776194763275725489 12939125832146072456794117)
              ·
                refine ⟨2426086093527388585648897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12939125832146072456794117 2426086093527388585648897)
                ·
                  refine ⟨1819564570145541439236673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2426086093527388585648897 1819564570145541439236673)
                  ·
                    refine ⟨1364673427609156079427505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1819564570145541439236673 1364673427609156079427505)
                    ·
                      refine ⟨1023505070706867059570629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1364673427609156079427505 1023505070706867059570629)
                      ·
                        rfl

theorem cell23_1993269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_1993269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993269 prefixEnd_1993269 := by exact prefixLift 1993269
  have htrace : WordTrace (prefixWord ++ tailWord_1993269) baseStart_1993269 baseEnd_1993269 := by
    simpa [prefixWord, tailWord_1993269, baseEnd_1993269] using wordTrace_append hprefix tailTrace_1993269
  have hstable : (prefixWord ++ tailWord_1993269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993269).length < 2 ^ (prefixWord ++ tailWord_1993269).sum := by decide
  have hdescent : baseEnd_1993269 < baseStart_1993269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993288 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 3, 7]
def baseStart_1993288 : Nat := 118140960795 + 1993288 * 2 ^ 59
def prefixEnd_1993288 : Nat := 4983230072969 + 3 ^ 40 * 1993288 * 2
def baseEnd_1993288 : Nat := 341171608946434161744347

theorem tailTrace_1993288 : CollatzResearch.WordTrace tailWord_1993288 prefixEnd_1993288 341171608946434161744347 := by
  unfold tailWord_1993288
  simp only [CollatzResearch.WordTrace]
  refine ⟨36350593001332738666386259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48467457335110318221848345 36350593001332738666386259)
  ·
    refine ⟨54525889501999107999579389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36350593001332738666386259 54525889501999107999579389)
    ·
      refine ⟨20447208563249665499842271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54525889501999107999579389 20447208563249665499842271)
      ·
        refine ⟨30670812844874498249763407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20447208563249665499842271 30670812844874498249763407)
        ·
          refine ⟨46006219267311747374645111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30670812844874498249763407 46006219267311747374645111)
          ·
            refine ⟨69009328900967621061967667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46006219267311747374645111 69009328900967621061967667)
            ·
              refine ⟨103513993351451431592951501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69009328900967621061967667 103513993351451431592951501)
              ·
                refine ⟨38817747506794286847356813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103513993351451431592951501 38817747506794286847356813)
                ·
                  refine ⟨14556655315047857567758805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38817747506794286847356813 14556655315047857567758805)
                  ·
                    refine ⟨341171608946434161744347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14556655315047857567758805 341171608946434161744347)
                    ·
                      rfl

theorem cell23_1993288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_1993288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993288 prefixEnd_1993288 := by exact prefixLift 1993288
  have htrace : WordTrace (prefixWord ++ tailWord_1993288) baseStart_1993288 baseEnd_1993288 := by
    simpa [prefixWord, tailWord_1993288, baseEnd_1993288] using wordTrace_append hprefix tailTrace_1993288
  have hstable : (prefixWord ++ tailWord_1993288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993288).length < 2 ^ (prefixWord ++ tailWord_1993288).sum := by decide
  have hdescent : baseEnd_1993288 < baseStart_1993288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993326 : List Nat := [4, 1, 2, 2, 2, 3, 2, 2, 5]
def baseStart_1993326 : Nat := 118140960795 + 1993326 * 2 ^ 59
def prefixEnd_1993326 : Nat := 4983230072969 + 3 ^ 40 * 1993326 * 2
def baseEnd_1993326 : Nat := 113726037678241481839763

theorem tailTrace_1993326 : CollatzResearch.WordTrace tailWord_1993326 prefixEnd_1993326 113726037678241481839763 := by
  unfold tailWord_1993326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9087821497065976227831979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48468381317685206548437221 9087821497065976227831979)
  ·
    refine ⟨13631732245598964341747969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9087821497065976227831979 13631732245598964341747969)
    ·
      refine ⟨10223799184199223256310977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13631732245598964341747969 10223799184199223256310977)
      ·
        refine ⟨7667849388149417442233233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10223799184199223256310977 7667849388149417442233233)
        ·
          refine ⟨5750887041112063081674925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7667849388149417442233233 5750887041112063081674925)
          ·
            refine ⟨2156582640417023655628097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5750887041112063081674925 2156582640417023655628097)
            ·
              refine ⟨1617436980312767741721073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156582640417023655628097 1617436980312767741721073)
              ·
                refine ⟨1213077735234575806290805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1617436980312767741721073 1213077735234575806290805)
                ·
                  refine ⟨113726037678241481839763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1213077735234575806290805 113726037678241481839763)
                  ·
                    rfl

theorem cell23_1993326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_1993326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993326 prefixEnd_1993326 := by exact prefixLift 1993326
  have htrace : WordTrace (prefixWord ++ tailWord_1993326) baseStart_1993326 baseEnd_1993326 := by
    simpa [prefixWord, tailWord_1993326, baseEnd_1993326] using wordTrace_append hprefix tailTrace_1993326
  have hstable : (prefixWord ++ tailWord_1993326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993326).length < 2 ^ (prefixWord ++ tailWord_1993326).sum := by decide
  have hdescent : baseEnd_1993326 < baseStart_1993326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993369 : List Nat := [1, 2, 1, 2, 1, 2, 6, 3, 1, 4]
def baseStart_1993369 : Nat := 118140960795 + 1993369 * 2 ^ 59
def prefixEnd_1993369 : Nat := 4983230072969 + 3 ^ 40 * 1993369 * 2
def baseEnd_1993369 : Nat := 341185472924105556106723

theorem tailTrace_1993369 : CollatzResearch.WordTrace tailWord_1993369 prefixEnd_1993369 341185472924105556106723 := by
  unfold tailWord_1993369
  simp only [CollatzResearch.WordTrace]
  refine ⟨72704140315372028166471161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48469426876914685444314107 72704140315372028166471161)
  ·
    refine ⟨54528105236529021124853371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72704140315372028166471161 54528105236529021124853371)
    ·
      refine ⟨81792157854793531687280057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54528105236529021124853371 81792157854793531687280057)
      ·
        refine ⟨61344118391095148765460043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81792157854793531687280057 61344118391095148765460043)
        ·
          refine ⟨92016177586642723148190065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61344118391095148765460043 92016177586642723148190065)
          ·
            refine ⟨69012133189982042361142549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92016177586642723148190065 69012133189982042361142549)
            ·
              refine ⟨3234943743280408235678557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69012133189982042361142549 3234943743280408235678557)
              ·
                refine ⟨1213103903730153088379459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3234943743280408235678557 1213103903730153088379459)
                ·
                  refine ⟨1819655855595229632569189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213103903730153088379459 1819655855595229632569189)
                  ·
                    refine ⟨341185472924105556106723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1819655855595229632569189 341185472924105556106723)
                    ·
                      rfl

theorem cell23_1993369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 1, 4].length) (baseStart_1993369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993369 prefixEnd_1993369 := by exact prefixLift 1993369
  have htrace : WordTrace (prefixWord ++ tailWord_1993369) baseStart_1993369 baseEnd_1993369 := by
    simpa [prefixWord, tailWord_1993369, baseEnd_1993369] using wordTrace_append hprefix tailTrace_1993369
  have hstable : (prefixWord ++ tailWord_1993369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993369).length < 2 ^ (prefixWord ++ tailWord_1993369).sum := by decide
  have hdescent : baseEnd_1993369 < baseStart_1993369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993399 : List Nat := [1, 1, 3, 1, 6, 1, 3, 1, 6]
def baseStart_1993399 : Nat := 118140960795 + 1993399 * 2 ^ 59
def prefixEnd_1993399 : Nat := 4983230072969 + 3 ^ 40 * 1993399 * 2
def baseEnd_1993399 : Nat := 113730202576883505660559

theorem tailTrace_1993399 : CollatzResearch.WordTrace tailWord_1993399 prefixEnd_1993399 113730202576883505660559 := by
  unfold tailWord_1993399
  simp only [CollatzResearch.WordTrace]
  refine ⟨72705234505263343290063251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48470156336842228860042167 72705234505263343290063251)
  ·
    refine ⟨109057851757895014935094877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72705234505263343290063251 109057851757895014935094877)
    ·
      refine ⟨40896694409210630600660579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109057851757895014935094877 40896694409210630600660579)
      ·
        refine ⟨61345041613815945900990869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40896694409210630600660579 61345041613815945900990869)
        ·
          refine ⟨2875548825647622464108947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61345041613815945900990869 2875548825647622464108947)
          ·
            refine ⟨4313323238471433696163421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875548825647622464108947 4313323238471433696163421)
            ·
              refine ⟨1617496214426787636061283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4313323238471433696163421 1617496214426787636061283)
              ·
                refine ⟨2426244321640181454091925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617496214426787636061283 2426244321640181454091925)
                ·
                  refine ⟨113730202576883505660559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2426244321640181454091925 113730202576883505660559)
                  ·
                    rfl

theorem cell23_1993399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 6].length) (baseStart_1993399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993399 prefixEnd_1993399 := by exact prefixLift 1993399
  have htrace : WordTrace (prefixWord ++ tailWord_1993399) baseStart_1993399 baseEnd_1993399 := by
    simpa [prefixWord, tailWord_1993399, baseEnd_1993399] using wordTrace_append hprefix tailTrace_1993399
  have hstable : (prefixWord ++ tailWord_1993399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993399).length < 2 ^ (prefixWord ++ tailWord_1993399).sum := by decide
  have hdescent : baseEnd_1993399 < baseStart_1993399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993402 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2]
def baseStart_1993402 : Nat := 118140960795 + 1993402 * 2 ^ 59
def prefixEnd_1993402 : Nat := 4983230072969 + 3 ^ 40 * 1993402 * 2
def baseEnd_1993402 : Nat := 1023573363633915039207517

theorem tailTrace_1993402 : CollatzResearch.WordTrace tailWord_1993402 prefixEnd_1993402 1023573363633915039207517 := by
  unfold tailWord_1993402
  simp only [CollatzResearch.WordTrace]
  refine ⟨18176335981063118700605615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48470229282834983201614973 18176335981063118700605615)
  ·
    refine ⟨27264503971594678050908423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18176335981063118700605615 27264503971594678050908423)
    ·
      refine ⟨40896755957392017076362635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27264503971594678050908423 40896755957392017076362635)
      ·
        refine ⟨61345133936088025614543953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40896755957392017076362635 61345133936088025614543953)
        ·
          refine ⟨46008850452066019210907965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61345133936088025614543953 46008850452066019210907965)
          ·
            refine ⟨17253318919524757204090487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46008850452066019210907965 17253318919524757204090487)
            ·
              refine ⟨25879978379287135806135731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17253318919524757204090487 25879978379287135806135731)
              ·
                refine ⟨38819967568930703709203597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25879978379287135806135731 38819967568930703709203597)
                ·
                  refine ⟨14557487838349013890951349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38819967568930703709203597 14557487838349013890951349)
                  ·
                    refine ⟨1364764484845220052276689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14557487838349013890951349 1364764484845220052276689)
                    ·
                      refine ⟨1023573363633915039207517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1364764484845220052276689 1023573363633915039207517)
                      ·
                        rfl

theorem cell23_1993402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2].length) (baseStart_1993402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993402 prefixEnd_1993402 := by exact prefixLift 1993402
  have htrace : WordTrace (prefixWord ++ tailWord_1993402) baseStart_1993402 baseEnd_1993402 := by
    simpa [prefixWord, tailWord_1993402, baseEnd_1993402] using wordTrace_append hprefix tailTrace_1993402
  have hstable : (prefixWord ++ tailWord_1993402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993402).length < 2 ^ (prefixWord ++ tailWord_1993402).sum := by decide
  have hdescent : baseEnd_1993402 < baseStart_1993402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993425 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 3, 6]
def baseStart_1993425 : Nat := 118140960795 + 1993425 * 2 ^ 59
def prefixEnd_1993425 : Nat := 4983230072969 + 3 ^ 40 * 1993425 * 2
def baseEnd_1993425 : Nat := 341195057896322816406637

theorem tailTrace_1993425 : CollatzResearch.WordTrace tailWord_1993425 prefixEnd_1993425 341195057896322816406637 := by
  unfold tailWord_1993425
  simp only [CollatzResearch.WordTrace]
  refine ⟨72706182803169149730509729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48470788535446099820339819 72706182803169149730509729)
  ·
    refine ⟨54529637102376862297882297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72706182803169149730509729 54529637102376862297882297)
    ·
      refine ⟨40897227826782646723411723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54529637102376862297882297 40897227826782646723411723)
      ·
        refine ⟨61345841740173970085117585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40897227826782646723411723 61345841740173970085117585)
        ·
          refine ⟨46009381305130477563838189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61345841740173970085117585 46009381305130477563838189)
          ·
            refine ⟨17253517989423929086439321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46009381305130477563838189 17253517989423929086439321)
            ·
              refine ⟨12940138492067946814829491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17253517989423929086439321 12940138492067946814829491)
              ·
                refine ⟨19410207738101920222244237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12940138492067946814829491 19410207738101920222244237)
                ·
                  refine ⟨7278827901788220083341589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19410207738101920222244237 7278827901788220083341589)
                  ·
                    refine ⟨341195057896322816406637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7278827901788220083341589 341195057896322816406637)
                    ·
                      rfl

theorem cell23_1993425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_1993425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993425 prefixEnd_1993425 := by exact prefixLift 1993425
  have htrace : WordTrace (prefixWord ++ tailWord_1993425) baseStart_1993425 baseEnd_1993425 := by
    simpa [prefixWord, tailWord_1993425, baseEnd_1993425] using wordTrace_append hprefix tailTrace_1993425
  have hstable : (prefixWord ++ tailWord_1993425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993425).length < 2 ^ (prefixWord ++ tailWord_1993425).sum := by decide
  have hdescent : baseEnd_1993425 < baseStart_1993425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993436 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_1993436 : Nat := 118140960795 + 1993436 * 2 ^ 59
def prefixEnd_1993436 : Nat := 4983230072969 + 3 ^ 40 * 1993436 * 2
def baseEnd_1993436 : Nat := 1023590821976167906182361

theorem tailTrace_1993436 : CollatzResearch.WordTrace tailWord_1993436 prefixEnd_1993436 1023590821976167906182361 := by
  unfold tailWord_1993436
  simp only [CollatzResearch.WordTrace]
  refine ⟨36353292003064649304580081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48471056004086199072773441 36353292003064649304580081)
  ·
    refine ⟨27264969002298486978435061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36353292003064649304580081 27264969002298486978435061)
    ·
      refine ⟨2556090843965483154228287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27264969002298486978435061 2556090843965483154228287)
      ·
        refine ⟨3834136265948224731342431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2556090843965483154228287 3834136265948224731342431)
        ·
          refine ⟨5751204398922337097013647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3834136265948224731342431 5751204398922337097013647)
          ·
            refine ⟨8626806598383505645520471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5751204398922337097013647 8626806598383505645520471)
            ·
              refine ⟨12940209897575258468280707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8626806598383505645520471 12940209897575258468280707)
              ·
                refine ⟨19410314846362887702421061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12940209897575258468280707 19410314846362887702421061)
                ·
                  refine ⟨3639434033693041444203949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19410314846362887702421061 3639434033693041444203949)
                  ·
                    refine ⟨1364787762634890541576481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639434033693041444203949 1364787762634890541576481)
                    ·
                      refine ⟨1023590821976167906182361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1364787762634890541576481 1023590821976167906182361)
                      ·
                        rfl

theorem cell23_1993436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_1993436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993436 prefixEnd_1993436 := by exact prefixLift 1993436
  have htrace : WordTrace (prefixWord ++ tailWord_1993436) baseStart_1993436 baseEnd_1993436 := by
    simpa [prefixWord, tailWord_1993436, baseEnd_1993436] using wordTrace_append hprefix tailTrace_1993436
  have hstable : (prefixWord ++ tailWord_1993436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993436).length < 2 ^ (prefixWord ++ tailWord_1993436).sum := by decide
  have hdescent : baseEnd_1993436 < baseStart_1993436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993452 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 3]
def baseStart_1993452 : Nat := 118140960795 + 1993452 * 2 ^ 59
def prefixEnd_1993452 : Nat := 4983230072969 + 3 ^ 40 * 1993452 * 2
def baseEnd_1993452 : Nat := 1023599037666639843582287

theorem tailTrace_1993452 : CollatzResearch.WordTrace tailWord_1993452 prefixEnd_1993452 1023599037666639843582287 := by
  unfold tailWord_1993452
  simp only [CollatzResearch.WordTrace]
  refine ⟨36353583787035666670871305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48471445049380888894495073 36353583787035666670871305)
  ·
    refine ⟨27265187840276750003153479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36353583787035666670871305 27265187840276750003153479)
    ·
      refine ⟨40897781760415125004730219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27265187840276750003153479 40897781760415125004730219)
      ·
        refine ⟨61346672640622687507095329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40897781760415125004730219 61346672640622687507095329)
        ·
          refine ⟨46010004480467015630321497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61346672640622687507095329 46010004480467015630321497)
          ·
            refine ⟨34507503360350261722741123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46010004480467015630321497 34507503360350261722741123)
            ·
              refine ⟨51761255040525392584111685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34507503360350261722741123 51761255040525392584111685)
              ·
                refine ⟨9705235320098511109520941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51761255040525392584111685 9705235320098511109520941)
                ·
                  refine ⟨3639463245036941666070353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9705235320098511109520941 3639463245036941666070353)
                  ·
                    refine ⟨2729597433777706249552765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3639463245036941666070353 2729597433777706249552765)
                    ·
                      refine ⟨1023599037666639843582287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2729597433777706249552765 1023599037666639843582287)
                      ·
                        rfl

theorem cell23_1993452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_1993452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993452 prefixEnd_1993452 := by exact prefixLift 1993452
  have htrace : WordTrace (prefixWord ++ tailWord_1993452) baseStart_1993452 baseEnd_1993452 := by
    simpa [prefixWord, tailWord_1993452, baseEnd_1993452] using wordTrace_append hprefix tailTrace_1993452
  have hstable : (prefixWord ++ tailWord_1993452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993452).length < 2 ^ (prefixWord ++ tailWord_1993452).sum := by decide
  have hdescent : baseEnd_1993452 < baseStart_1993452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993455 : List Nat := [1, 1, 2, 1, 5, 2, 1, 10]
def baseStart_1993455 : Nat := 118140960795 + 1993455 * 2 ^ 59
def prefixEnd_1993455 : Nat := 4983230072969 + 3 ^ 40 * 1993455 * 2
def baseEnd_1993455 : Nat := 37911132522540864142399

theorem tailTrace_1993455 : CollatzResearch.WordTrace tailWord_1993455 prefixEnd_1993455 37911132522540864142399 := by
  unfold tailWord_1993455
  simp only [CollatzResearch.WordTrace]
  refine ⟨72707276993060464854101819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48471517995373643236067879 72707276993060464854101819)
  ·
    refine ⟨109060915489590697281152729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72707276993060464854101819 109060915489590697281152729)
    ·
      refine ⟨81795686617193022960864547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109060915489590697281152729 81795686617193022960864547)
      ·
        refine ⟨122693529925789534441296821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81795686617193022960864547 122693529925789534441296821)
        ·
          refine ⟨11502518430542768853871577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122693529925789534441296821 11502518430542768853871577)
          ·
            refine ⟨8626888822907076640403683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11502518430542768853871577 8626888822907076640403683)
            ·
              refine ⟨12940333234360614960605525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8626888822907076640403683 12940333234360614960605525)
              ·
                refine ⟨37911132522540864142399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12940333234360614960605525 37911132522540864142399)
                ·
                  rfl

theorem cell23_1993455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 10].length) (baseStart_1993455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993455 prefixEnd_1993455 := by exact prefixLift 1993455
  have htrace : WordTrace (prefixWord ++ tailWord_1993455) baseStart_1993455 baseEnd_1993455 := by
    simpa [prefixWord, tailWord_1993455, baseEnd_1993455] using wordTrace_append hprefix tailTrace_1993455
  have hstable : (prefixWord ++ tailWord_1993455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993455).length < 2 ^ (prefixWord ++ tailWord_1993455).sum := by decide
  have hdescent : baseEnd_1993455 < baseStart_1993455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993462 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1993462 : Nat := 118140960795 + 1993462 * 2 ^ 59
def prefixEnd_1993462 : Nat := 4983230072969 + 3 ^ 40 * 1993462 * 2
def baseEnd_1993462 : Nat := 1023604172473184804457241

theorem tailTrace_1993462 : CollatzResearch.WordTrace tailWord_1993462 prefixEnd_1993462 1023604172473184804457241 := by
  unfold tailWord_1993462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4544220769002194065600415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48471688202690070033071093 4544220769002194065600415)
  ·
    refine ⟨6816331153503291098400623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4544220769002194065600415 6816331153503291098400623)
    ·
      refine ⟨10224496730254936647600935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6816331153503291098400623 10224496730254936647600935)
      ·
        refine ⟨15336745095382404971401403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10224496730254936647600935 15336745095382404971401403)
        ·
          refine ⟨23005117643073607457102105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15336745095382404971401403 23005117643073607457102105)
          ·
            refine ⟨17253838232305205592826579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23005117643073607457102105 17253838232305205592826579)
            ·
              refine ⟨25880757348457808389239869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17253838232305205592826579 25880757348457808389239869)
              ·
                refine ⟨9705284005671678145964951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25880757348457808389239869 9705284005671678145964951)
                ·
                  refine ⟨14557926008507517218947427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9705284005671678145964951 14557926008507517218947427)
                  ·
                    refine ⟨21836889012761275828421141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14557926008507517218947427 21836889012761275828421141)
                    ·
                      refine ⟨1023604172473184804457241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21836889012761275828421141 1023604172473184804457241)
                      ·
                        rfl

theorem cell23_1993462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1993462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993462 prefixEnd_1993462 := by exact prefixLift 1993462
  have htrace : WordTrace (prefixWord ++ tailWord_1993462) baseStart_1993462 baseEnd_1993462 := by
    simpa [prefixWord, tailWord_1993462, baseEnd_1993462] using wordTrace_append hprefix tailTrace_1993462
  have hstable : (prefixWord ++ tailWord_1993462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993462).length < 2 ^ (prefixWord ++ tailWord_1993462).sum := by decide
  have hdescent : baseEnd_1993462 < baseStart_1993462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993479 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1993479 : Nat := 118140960795 + 1993479 * 2 ^ 59
def prefixEnd_1993479 : Nat := 4983230072969 + 3 ^ 40 * 1993479 * 2
def baseEnd_1993479 : Nat := 1023612901644311237944663

theorem tailTrace_1993479 : CollatzResearch.WordTrace tailWord_1993479 prefixEnd_1993479 1023612901644311237944663 := by
  unfold tailWord_1993479
  simp only [CollatzResearch.WordTrace]
  refine ⟨72708152344973516952975491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48472101563315677968650327 72708152344973516952975491)
  ·
    refine ⟨109062228517460275429463237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72708152344973516952975491 109062228517460275429463237)
    ·
      refine ⟨20449167847023801643024357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109062228517460275429463237 20449167847023801643024357)
      ·
        refine ⟨3834218971316962808067067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20449167847023801643024357 3834218971316962808067067)
        ·
          refine ⟨5751328456975444212100601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3834218971316962808067067 5751328456975444212100601)
          ·
            refine ⟨4313496342731583159075451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5751328456975444212100601 4313496342731583159075451)
            ·
              refine ⟨6470244514097374738613177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313496342731583159075451 6470244514097374738613177)
              ·
                refine ⟨4852683385573031053959883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6470244514097374738613177 4852683385573031053959883)
                ·
                  refine ⟨7279025078359546580939825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852683385573031053959883 7279025078359546580939825)
                  ·
                    refine ⟨5459268808769659935704869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7279025078359546580939825 5459268808769659935704869)
                    ·
                      refine ⟨1023612901644311237944663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5459268808769659935704869 1023612901644311237944663)
                      ·
                        rfl

theorem cell23_1993479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1993479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993479 prefixEnd_1993479 := by exact prefixLift 1993479
  have htrace : WordTrace (prefixWord ++ tailWord_1993479) baseStart_1993479 baseEnd_1993479 := by
    simpa [prefixWord, tailWord_1993479, baseEnd_1993479] using wordTrace_append hprefix tailTrace_1993479
  have hstable : (prefixWord ++ tailWord_1993479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993479).length < 2 ^ (prefixWord ++ tailWord_1993479).sum := by decide
  have hdescent : baseEnd_1993479 < baseStart_1993479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993500 : List Nat := [2, 2, 3, 1, 1, 3, 4, 2, 1, 2, 2]
def baseStart_1993500 : Nat := 118140960795 + 1993500 * 2 ^ 59
def prefixEnd_1993500 : Nat := 4983230072969 + 3 ^ 40 * 1993500 * 2
def baseEnd_1993500 : Nat := 1023623684738055655782067

theorem tailTrace_1993500 : CollatzResearch.WordTrace tailWord_1993500 prefixEnd_1993500 1023623684738055655782067 := by
  unfold tailWord_1993500
  simp only [CollatzResearch.WordTrace]
  refine ⟨36354459138948718769744977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48472612185264958359659969 36354459138948718769744977)
  ·
    refine ⟨27265844354211539077308733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36354459138948718769744977 27265844354211539077308733)
    ·
      refine ⟨10224691632829327153990775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27265844354211539077308733 10224691632829327153990775)
      ·
        refine ⟨15337037449243990730986163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10224691632829327153990775 15337037449243990730986163)
        ·
          refine ⟨23005556173865986096479245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15337037449243990730986163 23005556173865986096479245)
          ·
            refine ⟨8627083565199744786179717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23005556173865986096479245 8627083565199744786179717)
            ·
              refine ⟨1617578168474952147408697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8627083565199744786179717 1617578168474952147408697)
              ·
                refine ⟨1213183626356214110556523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1617578168474952147408697 1213183626356214110556523)
                ·
                  refine ⟨1819775439534321165834785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213183626356214110556523 1819775439534321165834785)
                  ·
                    refine ⟨1364831579650740874376089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1819775439534321165834785 1364831579650740874376089)
                    ·
                      refine ⟨1023623684738055655782067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1364831579650740874376089 1023623684738055655782067)
                      ·
                        rfl

theorem cell23_1993500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_1993500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993500 prefixEnd_1993500 := by exact prefixLift 1993500
  have htrace : WordTrace (prefixWord ++ tailWord_1993500) baseStart_1993500 baseEnd_1993500 := by
    simpa [prefixWord, tailWord_1993500, baseEnd_1993500] using wordTrace_append hprefix tailTrace_1993500
  have hstable : (prefixWord ++ tailWord_1993500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993500).length < 2 ^ (prefixWord ++ tailWord_1993500).sum := by decide
  have hdescent : baseEnd_1993500 < baseStart_1993500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993509 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 5, 3, 2]
def baseStart_1993509 : Nat := 118140960795 + 1993509 * 2 ^ 59
def prefixEnd_1993509 : Nat := 4983230072969 + 3 ^ 40 * 1993509 * 2
def baseEnd_1993509 : Nat := 1023628306063946120569525

theorem tailTrace_1993509 : CollatzResearch.WordTrace tailWord_1993509 prefixEnd_1993509 1023628306063946120569525 := by
  unfold tailWord_1993509
  simp only [CollatzResearch.WordTrace]
  refine ⟨72709246534864832076567581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48472831023243221384378387 72709246534864832076567581)
  ·
    refine ⟨27265967450574312028712843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72709246534864832076567581 27265967450574312028712843)
    ·
      refine ⟨40898951175861468043069265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27265967450574312028712843 40898951175861468043069265)
      ·
        refine ⟨30674213381896101032301949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40898951175861468043069265 30674213381896101032301949)
        ·
          refine ⟨11502830018211037887113231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30674213381896101032301949 11502830018211037887113231)
          ·
            refine ⟨17254245027316556830669847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11502830018211037887113231 17254245027316556830669847)
            ·
              refine ⟨25881367540974835246004771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17254245027316556830669847 25881367540974835246004771)
              ·
                refine ⟨38822051311462252869007157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25881367540974835246004771 38822051311462252869007157)
                ·
                  refine ⟨3639567310449586206469421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38822051311462252869007157 3639567310449586206469421)
                  ·
                    refine ⟨1364837741418594827426033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639567310449586206469421 1364837741418594827426033)
                    ·
                      refine ⟨1023628306063946120569525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1364837741418594827426033 1023628306063946120569525)
                      ·
                        rfl

theorem cell23_1993509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_1993509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993509 prefixEnd_1993509 := by exact prefixLift 1993509
  have htrace : WordTrace (prefixWord ++ tailWord_1993509) baseStart_1993509 baseEnd_1993509 := by
    simpa [prefixWord, tailWord_1993509, baseEnd_1993509] using wordTrace_append hprefix tailTrace_1993509
  have hstable : (prefixWord ++ tailWord_1993509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993509).length < 2 ^ (prefixWord ++ tailWord_1993509).sum := by decide
  have hdescent : baseEnd_1993509 < baseStart_1993509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993515 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 1, 8]
def baseStart_1993515 : Nat := 118140960795 + 1993515 * 2 ^ 59
def prefixEnd_1993515 : Nat := 4983230072969 + 3 ^ 40 * 1993515 * 2
def baseEnd_1993515 : Nat := 341210462315957699031499

theorem tailTrace_1993515 : CollatzResearch.WordTrace tailWord_1993515 prefixEnd_1993515 341210462315957699031499 := by
  unfold tailWord_1993515
  simp only [CollatzResearch.WordTrace]
  refine ⟨72709465372843095101285999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48472976915228730067523999 72709465372843095101285999)
  ·
    refine ⟨109064198059264642651928999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72709465372843095101285999 109064198059264642651928999)
    ·
      refine ⟨163596297088896963977893499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109064198059264642651928999 163596297088896963977893499)
      ·
        refine ⟨245394445633345445966840249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163596297088896963977893499 245394445633345445966840249)
        ·
          refine ⟨184045834225009084475130187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245394445633345445966840249 184045834225009084475130187)
          ·
            refine ⟨276068751337513626712695281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184045834225009084475130187 276068751337513626712695281)
            ·
              refine ⟨207051563503135220034521461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276068751337513626712695281 207051563503135220034521461)
              ·
                refine ⟨19411084078418926878236387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207051563503135220034521461 19411084078418926878236387)
                ·
                  refine ⟨29116626117628390317354581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19411084078418926878236387 29116626117628390317354581)
                  ·
                    refine ⟨341210462315957699031499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29116626117628390317354581 341210462315957699031499)
                    ·
                      rfl

theorem cell23_1993515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 8].length) (baseStart_1993515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993515 prefixEnd_1993515 := by exact prefixLift 1993515
  have htrace : WordTrace (prefixWord ++ tailWord_1993515) baseStart_1993515 baseEnd_1993515 := by
    simpa [prefixWord, tailWord_1993515, baseEnd_1993515] using wordTrace_append hprefix tailTrace_1993515
  have hstable : (prefixWord ++ tailWord_1993515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993515).length < 2 ^ (prefixWord ++ tailWord_1993515).sum := by decide
  have hdescent : baseEnd_1993515 < baseStart_1993515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993522 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_1993522 : Nat := 118140960795 + 1993522 * 2 ^ 59
def prefixEnd_1993522 : Nat := 4983230072969 + 3 ^ 40 * 1993522 * 2
def baseEnd_1993522 : Nat := 1023634981312454569706965

theorem tailTrace_1993522 : CollatzResearch.WordTrace tailWord_1993522 prefixEnd_1993522 1023634981312454569706965 := by
  unfold tailWord_1993522
  simp only [CollatzResearch.WordTrace]
  refine ⟨18177430170954433824197705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48473147122545156864527213 18177430170954433824197705)
  ·
    refine ⟨13633072628215825368148279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18177430170954433824197705 13633072628215825368148279)
    ·
      refine ⟨20449608942323738052222419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13633072628215825368148279 20449608942323738052222419)
      ·
        refine ⟨30674413413485607078333629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20449608942323738052222419 30674413413485607078333629)
        ·
          refine ⟨11502905030057102654375111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30674413413485607078333629 11502905030057102654375111)
          ·
            refine ⟨17254357545085653981562667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11502905030057102654375111 17254357545085653981562667)
            ·
              refine ⟨25881536317628480972344001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17254357545085653981562667 25881536317628480972344001)
              ·
                refine ⟨19411152238221360729258001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25881536317628480972344001 19411152238221360729258001)
                ·
                  refine ⟨14558364178666020546943501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19411152238221360729258001 14558364178666020546943501)
                  ·
                    refine ⟨5459386566999757705103813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14558364178666020546943501 5459386566999757705103813)
                    ·
                      refine ⟨1023634981312454569706965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5459386566999757705103813 1023634981312454569706965)
                      ·
                        rfl

theorem cell23_1993522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_1993522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993522 prefixEnd_1993522 := by exact prefixLift 1993522
  have htrace : WordTrace (prefixWord ++ tailWord_1993522) baseStart_1993522 baseEnd_1993522 := by
    simpa [prefixWord, tailWord_1993522, baseEnd_1993522] using wordTrace_append hprefix tailTrace_1993522
  have hstable : (prefixWord ++ tailWord_1993522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993522).length < 2 ^ (prefixWord ++ tailWord_1993522).sum := by decide
  have hdescent : baseEnd_1993522 < baseStart_1993522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993537 : List Nat := [1, 2, 5, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_1993537 : Nat := 118140960795 + 1993537 * 2 ^ 59
def prefixEnd_1993537 : Nat := 4983230072969 + 3 ^ 40 * 1993537 * 2
def baseEnd_1993537 : Nat := 1023642683522272011019397

theorem tailTrace_1993537 : CollatzResearch.WordTrace tailWord_1993537 prefixEnd_1993537 1023642683522272011019397 := by
  unfold tailWord_1993537
  simp only [CollatzResearch.WordTrace]
  refine ⟨72710267778763392858586865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48473511852508928572391243 72710267778763392858586865)
  ·
    refine ⟨54532700834072544643940149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72710267778763392858586865 54532700834072544643940149)
    ·
      refine ⟨5112440703194301060369389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54532700834072544643940149 5112440703194301060369389)
      ·
        refine ⟨1917165263697862897638521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5112440703194301060369389 1917165263697862897638521)
        ·
          refine ⟨1437873947773397173228891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1917165263697862897638521 1437873947773397173228891)
          ·
            refine ⟨2156810921660095759843337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437873947773397173228891 2156810921660095759843337)
            ·
              refine ⟨1617608191245071819882503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156810921660095759843337 1617608191245071819882503)
              ·
                refine ⟨2426412286867607729823755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617608191245071819882503 2426412286867607729823755)
                ·
                  refine ⟨3639618430301411594735633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426412286867607729823755 3639618430301411594735633)
                  ·
                    refine ⟨2729713822726058696051725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3639618430301411594735633 2729713822726058696051725)
                    ·
                      refine ⟨1023642683522272011019397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2729713822726058696051725 1023642683522272011019397)
                      ·
                        rfl

theorem cell23_1993537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_1993537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993537 prefixEnd_1993537 := by exact prefixLift 1993537
  have htrace : WordTrace (prefixWord ++ tailWord_1993537) baseStart_1993537 baseEnd_1993537 := by
    simpa [prefixWord, tailWord_1993537, baseEnd_1993537] using wordTrace_append hprefix tailTrace_1993537
  have hstable : (prefixWord ++ tailWord_1993537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993537).length < 2 ^ (prefixWord ++ tailWord_1993537).sum := by decide
  have hdescent : baseEnd_1993537 < baseStart_1993537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993539 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 1, 4, 2]
def baseStart_1993539 : Nat := 118140960795 + 1993539 * 2 ^ 59
def prefixEnd_1993539 : Nat := 4983230072969 + 3 ^ 40 * 1993539 * 2
def baseEnd_1993539 : Nat := 1023643710483581003194387

theorem tailTrace_1993539 : CollatzResearch.WordTrace tailWord_1993539 prefixEnd_1993539 1023643710483581003194387 := by
  unfold tailWord_1993539
  simp only [CollatzResearch.WordTrace]
  refine ⟨72710340724756147200159671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48473560483170764800106447 72710340724756147200159671)
  ·
    refine ⟨109065511087134220800239507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72710340724756147200159671 109065511087134220800239507)
    ·
      refine ⟨163598266630701331200359261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109065511087134220800239507 163598266630701331200359261)
      ·
        refine ⟨61349349986512999200134723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163598266630701331200359261 61349349986512999200134723)
        ·
          refine ⟨92024024979769498800202085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61349349986512999200134723 92024024979769498800202085)
          ·
            refine ⟨17254504683706781025037891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92024024979769498800202085 17254504683706781025037891)
            ·
              refine ⟨25881757025560171537556837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17254504683706781025037891 25881757025560171537556837)
              ·
                refine ⟨4852829442292532163291907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25881757025560171537556837 4852829442292532163291907)
                ·
                  refine ⟨7279244163438798244937861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852829442292532163291907 7279244163438798244937861)
                  ·
                    refine ⟨1364858280644774670925849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7279244163438798244937861 1364858280644774670925849)
                    ·
                      refine ⟨1023643710483581003194387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1364858280644774670925849 1023643710483581003194387)
                      ·
                        rfl

theorem cell23_1993539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 4, 2].length) (baseStart_1993539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993539 prefixEnd_1993539 := by exact prefixLift 1993539
  have htrace : WordTrace (prefixWord ++ tailWord_1993539) baseStart_1993539 baseEnd_1993539 := by
    simpa [prefixWord, tailWord_1993539, baseEnd_1993539] using wordTrace_append hprefix tailTrace_1993539
  have hstable : (prefixWord ++ tailWord_1993539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993539).length < 2 ^ (prefixWord ++ tailWord_1993539).sum := by decide
  have hdescent : baseEnd_1993539 < baseStart_1993539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993552 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 4]
def baseStart_1993552 : Nat := 118140960795 + 1993552 * 2 ^ 59
def prefixEnd_1993552 : Nat := 4983230072969 + 3 ^ 40 * 1993552 * 2
def baseEnd_1993552 : Nat := 1023650385732089452331827

theorem tailTrace_1993552 : CollatzResearch.WordTrace tailWord_1993552 prefixEnd_1993552 1023650385732089452331827 := by
  unfold tailWord_1993552
  simp only [CollatzResearch.WordTrace]
  refine ⟨36355407436854525210191455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48473876582472700280255273 36355407436854525210191455)
  ·
    refine ⟨54533111155281787815287183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36355407436854525210191455 54533111155281787815287183)
    ·
      refine ⟨81799666732922681722930775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54533111155281787815287183 81799666732922681722930775)
      ·
        refine ⟨122699500099384022584396163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81799666732922681722930775 122699500099384022584396163)
        ·
          refine ⟨184049250149076033876594245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122699500099384022584396163 184049250149076033876594245)
          ·
            refine ⟨34509234402951756351861421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184049250149076033876594245 34509234402951756351861421)
            ·
              refine ⟨12940962901106908631948033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34509234402951756351861421 12940962901106908631948033)
              ·
                refine ⟨9705722175830181473961025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12940962901106908631948033 9705722175830181473961025)
                ·
                  refine ⟨7279291631872636105470769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9705722175830181473961025 7279291631872636105470769)
                  ·
                    refine ⟨5459468723904477079103077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7279291631872636105470769 5459468723904477079103077)
                    ·
                      refine ⟨1023650385732089452331827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5459468723904477079103077 1023650385732089452331827)
                      ·
                        rfl

theorem cell23_1993552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_1993552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993552 prefixEnd_1993552 := by exact prefixLift 1993552
  have htrace : WordTrace (prefixWord ++ tailWord_1993552) baseStart_1993552 baseEnd_1993552 := by
    simpa [prefixWord, tailWord_1993552, baseEnd_1993552] using wordTrace_append hprefix tailTrace_1993552
  have hstable : (prefixWord ++ tailWord_1993552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993552).length < 2 ^ (prefixWord ++ tailWord_1993552).sum := by decide
  have hdescent : baseEnd_1993552 < baseStart_1993552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993562 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 7]
def baseStart_1993562 : Nat := 118140960795 + 1993562 * 2 ^ 59
def prefixEnd_1993562 : Nat := 4983230072969 + 3 ^ 40 * 1993562 * 2
def baseEnd_1993562 : Nat := 113739502282070490356309

theorem tailTrace_1993562 : CollatzResearch.WordTrace tailWord_1993562 prefixEnd_1993562 113739502282070490356309 := by
  unfold tailWord_1993562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18177794900918205532061735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48474119735781881418831293 18177794900918205532061735)
  ·
    refine ⟨27266692351377308298092603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18177794900918205532061735 27266692351377308298092603)
    ·
      refine ⟨40900038527065962447138905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27266692351377308298092603 40900038527065962447138905)
      ·
        refine ⟨30675028895299471835354179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40900038527065962447138905 30675028895299471835354179)
        ·
          refine ⟨46012543342949207753031269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30675028895299471835354179 46012543342949207753031269)
          ·
            refine ⟨8627351876802976453693363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46012543342949207753031269 8627351876802976453693363)
            ·
              refine ⟨12941027815204464680540045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8627351876802976453693363 12941027815204464680540045)
              ·
                refine ⟨4852885430701674255202517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12941027815204464680540045 4852885430701674255202517)
                ·
                  refine ⟨113739502282070490356309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4852885430701674255202517 113739502282070490356309)
                  ·
                    rfl

theorem cell23_1993562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_1993562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993562 prefixEnd_1993562 := by exact prefixLift 1993562
  have htrace : WordTrace (prefixWord ++ tailWord_1993562) baseStart_1993562 baseEnd_1993562 := by
    simpa [prefixWord, tailWord_1993562, baseEnd_1993562] using wordTrace_append hprefix tailTrace_1993562
  have hstable : (prefixWord ++ tailWord_1993562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993562).length < 2 ^ (prefixWord ++ tailWord_1993562).sum := by decide
  have hdescent : baseEnd_1993562 < baseStart_1993562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993609 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 2, 5]
def baseStart_1993609 : Nat := 118140960795 + 1993609 * 2 ^ 59
def prefixEnd_1993609 : Nat := 4983230072969 + 3 ^ 40 * 1993609 * 2
def baseEnd_1993609 : Nat := 341226551376465243106355

theorem tailTrace_1993609 : CollatzResearch.WordTrace tailWord_1993609 prefixEnd_1993609 341226551376465243106355 := by
  unfold tailWord_1993609
  simp only [CollatzResearch.WordTrace]
  refine ⟨72712893834502549155207881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48475262556335032770138587 72712893834502549155207881)
  ·
    refine ⟨54534670375876911866405911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72712893834502549155207881 54534670375876911866405911)
    ·
      refine ⟨81802005563815367799608867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54534670375876911866405911 81802005563815367799608867)
      ·
        refine ⟨122703008345723051699413301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81802005563815367799608867 122703008345723051699413301)
        ·
          refine ⟨11503407032411536096819997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122703008345723051699413301 11503407032411536096819997)
          ·
            refine ⟨4313777637154326036307499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11503407032411536096819997 4313777637154326036307499)
            ·
              refine ⟨6470666455731489054461249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313777637154326036307499 6470666455731489054461249)
              ·
                refine ⟨4852999841798616790845937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6470666455731489054461249 4852999841798616790845937)
                ·
                  refine ⟨3639749881348962593134453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4852999841798616790845937 3639749881348962593134453)
                  ·
                    refine ⟨341226551376465243106355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3639749881348962593134453 341226551376465243106355)
                    ·
                      rfl

theorem cell23_1993609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 5].length) (baseStart_1993609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993609 prefixEnd_1993609 := by exact prefixLift 1993609
  have htrace : WordTrace (prefixWord ++ tailWord_1993609) baseStart_1993609 baseEnd_1993609 := by
    simpa [prefixWord, tailWord_1993609, baseEnd_1993609] using wordTrace_append hprefix tailTrace_1993609
  have hstable : (prefixWord ++ tailWord_1993609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993609).length < 2 ^ (prefixWord ++ tailWord_1993609).sum := by decide
  have hdescent : baseEnd_1993609 < baseStart_1993609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993629 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_1993629 : Nat := 118140960795 + 1993629 * 2 ^ 59
def prefixEnd_1993629 : Nat := 4983230072969 + 3 ^ 40 * 1993629 * 2
def baseEnd_1993629 : Nat := 1023689923742485651068973

theorem tailTrace_1993629 : CollatzResearch.WordTrace tailWord_1993629 prefixEnd_1993629 1023689923742485651068973 := by
  unfold tailWord_1993629
  simp only [CollatzResearch.WordTrace]
  refine ⟨72713623294430092570935941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48475748862953395047290627 72713623294430092570935941)
  ·
    refine ⟨13633804367705642357050489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72713623294430092570935941 13633804367705642357050489)
    ·
      refine ⟨10225353275779231767787867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13633804367705642357050489 10225353275779231767787867)
      ·
        refine ⟨15338029913668847651681801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10225353275779231767787867 15338029913668847651681801)
        ·
          refine ⟨11503522435251635738761351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15338029913668847651681801 11503522435251635738761351)
          ·
            refine ⟨17255283652877453608142027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11503522435251635738761351 17255283652877453608142027)
            ·
              refine ⟨25882925479316180412213041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17255283652877453608142027 25882925479316180412213041)
              ·
                refine ⟨19412194109487135309159781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25882925479316180412213041 19412194109487135309159781)
                ·
                  refine ⟨3639786395528837870467459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19412194109487135309159781 3639786395528837870467459)
                  ·
                    refine ⟨5459679593293256805701189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3639786395528837870467459 5459679593293256805701189)
                    ·
                      refine ⟨1023689923742485651068973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5459679593293256805701189 1023689923742485651068973)
                      ·
                        rfl

theorem cell23_1993629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_1993629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993629 prefixEnd_1993629 := by exact prefixLift 1993629
  have htrace : WordTrace (prefixWord ++ tailWord_1993629) baseStart_1993629 baseEnd_1993629 := by
    simpa [prefixWord, tailWord_1993629, baseEnd_1993629] using wordTrace_append hprefix tailTrace_1993629
  have hstable : (prefixWord ++ tailWord_1993629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993629).length < 2 ^ (prefixWord ++ tailWord_1993629).sum := by decide
  have hdescent : baseEnd_1993629 < baseStart_1993629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993699 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 3, 5]
def baseStart_1993699 : Nat := 118140960795 + 1993699 * 2 ^ 59
def prefixEnd_1993699 : Nat := 4983230072969 + 3 ^ 40 * 1993699 * 2
def baseEnd_1993699 : Nat := 341241955796100125731217

theorem tailTrace_1993699 : CollatzResearch.WordTrace tailWord_1993699 prefixEnd_1993699 341241955796100125731217 := by
  unfold tailWord_1993699
  simp only [CollatzResearch.WordTrace]
  refine ⟨72716176404176494525984151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48477450936117663017322767 72716176404176494525984151)
  ·
    refine ⟨109074264606264741788976227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72716176404176494525984151 109074264606264741788976227)
    ·
      refine ⟨163611396909397112683464341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109074264606264741788976227 163611396909397112683464341)
      ·
        refine ⟨7669284230127989657037391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163611396909397112683464341 7669284230127989657037391)
        ·
          refine ⟨11503926345191984485556087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7669284230127989657037391 11503926345191984485556087)
          ·
            refine ⟨17255889517787976728334131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11503926345191984485556087 17255889517787976728334131)
            ·
              refine ⟨25883834276681965092501197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17255889517787976728334131 25883834276681965092501197)
              ·
                refine ⟨9706437853755736909687949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25883834276681965092501197 9706437853755736909687949)
                ·
                  refine ⟨3639914195158401341132981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9706437853755736909687949 3639914195158401341132981)
                  ·
                    refine ⟨341241955796100125731217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3639914195158401341132981 341241955796100125731217)
                    ·
                      rfl

theorem cell23_1993699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 5].length) (baseStart_1993699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993699 prefixEnd_1993699 := by exact prefixLift 1993699
  have htrace : WordTrace (prefixWord ++ tailWord_1993699) baseStart_1993699 baseEnd_1993699 := by
    simpa [prefixWord, tailWord_1993699, baseEnd_1993699] using wordTrace_append hprefix tailTrace_1993699
  have hstable : (prefixWord ++ tailWord_1993699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993699).length < 2 ^ (prefixWord ++ tailWord_1993699).sum := by decide
  have hdescent : baseEnd_1993699 < baseStart_1993699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993739 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 5]
def baseStart_1993739 : Nat := 118140960795 + 1993739 * 2 ^ 59
def prefixEnd_1993739 : Nat := 4983230072969 + 3 ^ 40 * 1993739 * 2
def baseEnd_1993739 : Nat := 1023746406614480220693467

theorem tailTrace_1993739 : CollatzResearch.WordTrace tailWord_1993739 prefixEnd_1993739 1023746406614480220693467 := by
  unfold tailWord_1993739
  simp only [CollatzResearch.WordTrace]
  refine ⟨72717635324031581357440271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48478423549354387571626847 72717635324031581357440271)
  ·
    refine ⟨109076452986047372036160407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72717635324031581357440271 109076452986047372036160407)
    ·
      refine ⟨163614679479071058054240611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109076452986047372036160407 163614679479071058054240611)
      ·
        refine ⟨245422019218606587081360917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163614679479071058054240611 245422019218606587081360917)
        ·
          refine ⟨11504157150872183769438793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 245422019218606587081360917 11504157150872183769438793)
          ·
            refine ⟨8628117863154137827079095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11504157150872183769438793 8628117863154137827079095)
            ·
              refine ⟨12942176794731206740618643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8628117863154137827079095 12942176794731206740618643)
              ·
                refine ⟨19413265192096810110927965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12942176794731206740618643 19413265192096810110927965)
                ·
                  refine ⟨7279974447036303791597987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19413265192096810110927965 7279974447036303791597987)
                  ·
                    refine ⟨10919961670554455687396981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7279974447036303791597987 10919961670554455687396981)
                    ·
                      refine ⟨1023746406614480220693467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10919961670554455687396981 1023746406614480220693467)
                      ·
                        rfl

theorem cell23_1993739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 5].length) (baseStart_1993739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993739 prefixEnd_1993739 := by exact prefixLift 1993739
  have htrace : WordTrace (prefixWord ++ tailWord_1993739) baseStart_1993739 baseEnd_1993739 := by
    simpa [prefixWord, tailWord_1993739, baseEnd_1993739] using wordTrace_append hprefix tailTrace_1993739
  have hstable : (prefixWord ++ tailWord_1993739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993739).length < 2 ^ (prefixWord ++ tailWord_1993739).sum := by decide
  have hdescent : baseEnd_1993739 < baseStart_1993739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993753 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 3, 2, 2]
def baseStart_1993753 : Nat := 118140960795 + 1993753 * 2 ^ 59
def prefixEnd_1993753 : Nat := 4983230072969 + 3 ^ 40 * 1993753 * 2
def baseEnd_1993753 : Nat := 1023753595343643165918403

theorem tailTrace_1993753 : CollatzResearch.WordTrace tailWord_1993753 prefixEnd_1993753 1023753595343643165918403 := by
  unfold tailWord_1993753
  simp only [CollatzResearch.WordTrace]
  refine ⟨72718145945980861748449913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48478763963987241165633275 72718145945980861748449913)
  ·
    refine ⟨54538609459485646311337435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72718145945980861748449913 54538609459485646311337435)
    ·
      refine ⟨81807914189228469467006153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54538609459485646311337435 81807914189228469467006153)
      ·
        refine ⟨61355935641921352100254615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81807914189228469467006153 61355935641921352100254615)
        ·
          refine ⟨92033903462882028150381923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61355935641921352100254615 92033903462882028150381923)
          ·
            refine ⟨138050855194323042225572885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92033903462882028150381923 138050855194323042225572885)
            ·
              refine ⟨6471133837233892604323729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138050855194323042225572885 6471133837233892604323729)
              ·
                refine ⟨4853350377925419453242797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6471133837233892604323729 4853350377925419453242797)
                ·
                  refine ⟨1820006391722032294966049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4853350377925419453242797 1820006391722032294966049)
                  ·
                    refine ⟨1365004793791524221224537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1820006391722032294966049 1365004793791524221224537)
                    ·
                      refine ⟨1023753595343643165918403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1365004793791524221224537 1023753595343643165918403)
                      ·
                        rfl

theorem cell23_1993753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 2, 2].length) (baseStart_1993753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993753 prefixEnd_1993753 := by exact prefixLift 1993753
  have htrace : WordTrace (prefixWord ++ tailWord_1993753) baseStart_1993753 baseEnd_1993753 := by
    simpa [prefixWord, tailWord_1993753, baseEnd_1993753] using wordTrace_append hprefix tailTrace_1993753
  have hstable : (prefixWord ++ tailWord_1993753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993753).length < 2 ^ (prefixWord ++ tailWord_1993753).sum := by decide
  have hdescent : baseEnd_1993753 < baseStart_1993753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993759 : List Nat := [1, 1, 2, 4, 1, 4, 1, 9]
def baseStart_1993759 : Nat := 118140960795 + 1993759 * 2 ^ 59
def prefixEnd_1993759 : Nat := 4983230072969 + 3 ^ 40 * 1993759 * 2
def baseEnd_1993759 : Nat := 37916913934354449720125

theorem tailTrace_1993759 : CollatzResearch.WordTrace tailWord_1993759 prefixEnd_1993759 37916913934354449720125 := by
  unfold tailWord_1993759
  simp only [CollatzResearch.WordTrace]
  refine ⟨72718364783959124773168331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48478909855972749848778887 72718364783959124773168331)
  ·
    refine ⟨109077547175938687159752497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72718364783959124773168331 109077547175938687159752497)
    ·
      refine ⟨81808160381954015369814373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109077547175938687159752497 81808160381954015369814373)
      ·
        refine ⟨15339030071616377881840195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81808160381954015369814373 15339030071616377881840195)
        ·
          refine ⟨23008545107424566822760293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15339030071616377881840195 23008545107424566822760293)
          ·
            refine ⟨4314102207642106279267555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23008545107424566822760293 4314102207642106279267555)
            ·
              refine ⟨6471153311463159418901333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4314102207642106279267555 6471153311463159418901333)
              ·
                refine ⟨37916913934354449720125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6471153311463159418901333 37916913934354449720125)
                ·
                  rfl

theorem cell23_1993759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 9].length) (baseStart_1993759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993759 prefixEnd_1993759 := by exact prefixLift 1993759
  have htrace : WordTrace (prefixWord ++ tailWord_1993759) baseStart_1993759 baseEnd_1993759 := by
    simpa [prefixWord, tailWord_1993759, baseEnd_1993759] using wordTrace_append hprefix tailTrace_1993759
  have hstable : (prefixWord ++ tailWord_1993759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993759).length < 2 ^ (prefixWord ++ tailWord_1993759).sum := by decide
  have hdescent : baseEnd_1993759 < baseStart_1993759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993813 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 3, 3, 2]
def baseStart_1993813 : Nat := 118140960795 + 1993813 * 2 ^ 59
def prefixEnd_1993813 : Nat := 4983230072969 + 3 ^ 40 * 1993813 * 2
def baseEnd_1993813 : Nat := 1023784404182912931168127

theorem tailTrace_1993813 : CollatzResearch.WordTrace tailWord_1993813 prefixEnd_1993813 1023784404182912931168127 := by
  unfold tailWord_1993813
  simp only [CollatzResearch.WordTrace]
  refine ⟨72720334325763491995634093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48480222883842327997089395 72720334325763491995634093)
  ·
    refine ⟨27270125372161309498362785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72720334325763491995634093 27270125372161309498362785)
    ·
      refine ⟨20452594029120982123772089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27270125372161309498362785 20452594029120982123772089)
      ·
        refine ⟨15339445521840736592829067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20452594029120982123772089 15339445521840736592829067)
        ·
          refine ⟨23009168282761104889243601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15339445521840736592829067 23009168282761104889243601)
          ·
            refine ⟨17256876212070828666932701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23009168282761104889243601 17256876212070828666932701)
            ·
              refine ⟨6471328579526560750099763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17256876212070828666932701 6471328579526560750099763)
              ·
                refine ⟨9706992869289841125149645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6471328579526560750099763 9706992869289841125149645)
                ·
                  refine ⟨3640122325983690421931117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9706992869289841125149645 3640122325983690421931117)
                  ·
                    refine ⟨1365045872243883908224169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3640122325983690421931117 1365045872243883908224169)
                    ·
                      refine ⟨1023784404182912931168127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1365045872243883908224169 1023784404182912931168127)
                      ·
                        rfl

theorem cell23_1993813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_1993813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993813 prefixEnd_1993813 := by exact prefixLift 1993813
  have htrace : WordTrace (prefixWord ++ tailWord_1993813) baseStart_1993813 baseEnd_1993813 := by
    simpa [prefixWord, tailWord_1993813, baseEnd_1993813] using wordTrace_append hprefix tailTrace_1993813
  have hstable : (prefixWord ++ tailWord_1993813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993813).length < 2 ^ (prefixWord ++ tailWord_1993813).sum := by decide
  have hdescent : baseEnd_1993813 < baseStart_1993813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993854 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1993854 : Nat := 118140960795 + 1993854 * 2 ^ 59
def prefixEnd_1993854 : Nat := 4983230072969 + 3 ^ 40 * 1993854 * 2
def baseEnd_1993854 : Nat := 1023805456889747270755439

theorem tailTrace_1993854 : CollatzResearch.WordTrace tailWord_1993854 prefixEnd_1993854 1023805456889747270755439 := by
  unfold tailWord_1993854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9090228714826869499734577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48481219812409970665251077 9090228714826869499734577)
  ·
    refine ⟨6817671536120152124800933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9090228714826869499734577 6817671536120152124800933)
    ·
      refine ⟨1278313413022528523400175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6817671536120152124800933 1278313413022528523400175)
      ·
        refine ⟨1917470119533792785100263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1278313413022528523400175 1917470119533792785100263)
        ·
          refine ⟨2876205179300689177650395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917470119533792785100263 2876205179300689177650395)
          ·
            refine ⟨4314307768951033766475593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2876205179300689177650395 4314307768951033766475593)
            ·
              refine ⟨3235730826713275324856695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4314307768951033766475593 3235730826713275324856695)
              ·
                refine ⟨4853596240069912987285043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235730826713275324856695 4853596240069912987285043)
                ·
                  refine ⟨7280394360104869480927565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4853596240069912987285043 7280394360104869480927565)
                  ·
                    refine ⟨2730147885039326055347837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7280394360104869480927565 2730147885039326055347837)
                    ·
                      refine ⟨1023805456889747270755439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2730147885039326055347837 1023805456889747270755439)
                      ·
                        rfl

theorem cell23_1993854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1993854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993854 prefixEnd_1993854 := by exact prefixLift 1993854
  have htrace : WordTrace (prefixWord ++ tailWord_1993854) baseStart_1993854 baseEnd_1993854 := by
    simpa [prefixWord, tailWord_1993854, baseEnd_1993854] using wordTrace_append hprefix tailTrace_1993854
  have hstable : (prefixWord ++ tailWord_1993854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993854).length < 2 ^ (prefixWord ++ tailWord_1993854).sum := by decide
  have hdescent : baseEnd_1993854 < baseStart_1993854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993860 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_1993860 : Nat := 118140960795 + 1993860 * 2 ^ 59
def prefixEnd_1993860 : Nat := 4983230072969 + 3 ^ 40 * 1993860 * 2
def baseEnd_1993860 : Nat := 1023808537773674247280411

theorem tailTrace_1993860 : CollatzResearch.WordTrace tailWord_1993860 prefixEnd_1993860 1023808537773674247280411 := by
  unfold tailWord_1993860
  simp only [CollatzResearch.WordTrace]
  refine ⟨36361024278296609511297517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48481365704395479348396689 36361024278296609511297517)
  ·
    refine ⟨13635384104361228566736569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36361024278296609511297517 13635384104361228566736569)
    ·
      refine ⟨10226538078270921425052427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13635384104361228566736569 10226538078270921425052427)
      ·
        refine ⟨15339807117406382137578641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10226538078270921425052427 15339807117406382137578641)
        ·
          refine ⟨11504855338054786603183981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15339807117406382137578641 11504855338054786603183981)
          ·
            refine ⟨4314320751770544976193993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11504855338054786603183981 4314320751770544976193993)
            ·
              refine ⟨3235740563827908732145495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4314320751770544976193993 3235740563827908732145495)
              ·
                refine ⟨4853610845741863098218243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235740563827908732145495 4853610845741863098218243)
                ·
                  refine ⟨7280416268612794647327365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4853610845741863098218243 7280416268612794647327365)
                  ·
                    refine ⟨1365078050364898996373881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7280416268612794647327365 1365078050364898996373881)
                    ·
                      refine ⟨1023808537773674247280411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1365078050364898996373881 1023808537773674247280411)
                      ·
                        rfl

theorem cell23_1993860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_1993860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993860 prefixEnd_1993860 := by exact prefixLift 1993860
  have htrace : WordTrace (prefixWord ++ tailWord_1993860) baseStart_1993860 baseEnd_1993860 := by
    simpa [prefixWord, tailWord_1993860, baseEnd_1993860] using wordTrace_append hprefix tailTrace_1993860
  have hstable : (prefixWord ++ tailWord_1993860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993860).length < 2 ^ (prefixWord ++ tailWord_1993860).sum := by decide
  have hdescent : baseEnd_1993860 < baseStart_1993860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993866 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 7]
def baseStart_1993866 : Nat := 118140960795 + 1993866 * 2 ^ 59
def prefixEnd_1993866 : Nat := 4983230072969 + 3 ^ 40 * 1993866 * 2
def baseEnd_1993866 : Nat := 113756846517511247089487

theorem tailTrace_1993866 : CollatzResearch.WordTrace tailWord_1993866 prefixEnd_1993866 113756846517511247089487 := by
  unfold tailWord_1993866
  simp only [CollatzResearch.WordTrace]
  refine ⟨18180566848642870511828363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48481511596380988031542301 18180566848642870511828363)
  ·
    refine ⟨27270850272964305767742545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18180566848642870511828363 27270850272964305767742545)
    ·
      refine ⟨20453137704723229325806909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27270850272964305767742545 20453137704723229325806909)
      ·
        refine ⟨7669926639271210997177591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20453137704723229325806909 7669926639271210997177591)
        ·
          refine ⟨11504889958906816495766387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7669926639271210997177591 11504889958906816495766387)
          ·
            refine ⟨17257334938360224743649581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11504889958906816495766387 17257334938360224743649581)
            ·
              refine ⟨6471500601885084278868593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17257334938360224743649581 6471500601885084278868593)
              ·
                refine ⟨4853625451413813209151445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6471500601885084278868593 4853625451413813209151445)
                ·
                  refine ⟨113756846517511247089487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4853625451413813209151445 113756846517511247089487)
                  ·
                    rfl

theorem cell23_1993866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_1993866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993866 prefixEnd_1993866 := by exact prefixLift 1993866
  have htrace : WordTrace (prefixWord ++ tailWord_1993866) baseStart_1993866 baseEnd_1993866 := by
    simpa [prefixWord, tailWord_1993866, baseEnd_1993866] using wordTrace_append hprefix tailTrace_1993866
  have hstable : (prefixWord ++ tailWord_1993866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993866).length < 2 ^ (prefixWord ++ tailWord_1993866).sum := by decide
  have hdescent : baseEnd_1993866 < baseStart_1993866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993953 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_1993953 : Nat := 118140960795 + 1993953 * 2 ^ 59
def prefixEnd_1993953 : Nat := 4983230072969 + 3 ^ 40 * 1993953 * 2
def baseEnd_1993953 : Nat := 1023856291474542383417483

theorem tailTrace_1993953 : CollatzResearch.WordTrace tailWord_1993953 prefixEnd_1993953 1023856291474542383417483 := by
  unfold tailWord_1993953
  simp only [CollatzResearch.WordTrace]
  refine ⟨72725440545256295905730513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48483627030170863937153675 72725440545256295905730513)
  ·
    refine ⟨54544080408942221929297885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72725440545256295905730513 54544080408942221929297885)
    ·
      refine ⟨20454030153353333223486707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54544080408942221929297885 20454030153353333223486707)
      ·
        refine ⟨30681045230029999835230061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20454030153353333223486707 30681045230029999835230061)
        ·
          refine ⟨11505391961261249938211273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30681045230029999835230061 11505391961261249938211273)
          ·
            refine ⟨8629043970945937453658455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11505391961261249938211273 8629043970945937453658455)
            ·
              refine ⟨12943565956418906180487683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8629043970945937453658455 12943565956418906180487683)
              ·
                refine ⟨19415348934628359270731525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12943565956418906180487683 19415348934628359270731525)
                ·
                  refine ⟨3640377925242817363262161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19415348934628359270731525 3640377925242817363262161)
                  ·
                    refine ⟨2730283443932113022446621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3640377925242817363262161 2730283443932113022446621)
                    ·
                      refine ⟨1023856291474542383417483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2730283443932113022446621 1023856291474542383417483)
                      ·
                        rfl

theorem cell23_1993953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_1993953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993953 prefixEnd_1993953 := by exact prefixLift 1993953
  have htrace : WordTrace (prefixWord ++ tailWord_1993953) baseStart_1993953 baseEnd_1993953 := by
    simpa [prefixWord, tailWord_1993953, baseEnd_1993953] using wordTrace_append hprefix tailTrace_1993953
  have hstable : (prefixWord ++ tailWord_1993953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993953).length < 2 ^ (prefixWord ++ tailWord_1993953).sum := by decide
  have hdescent : baseEnd_1993953 < baseStart_1993953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993956 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 8]
def baseStart_1993956 : Nat := 118140960795 + 1993956 * 2 ^ 59
def prefixEnd_1993956 : Nat := 4983230072969 + 3 ^ 40 * 1993956 * 2
def baseEnd_1993956 : Nat := 113761981324056207964441

theorem tailTrace_1993956 : CollatzResearch.WordTrace tailWord_1993956 prefixEnd_1993956 113761981324056207964441 := by
  unfold tailWord_1993956
  simp only [CollatzResearch.WordTrace]
  refine ⟨36362774982122713709044861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48483699976163618278726481 36362774982122713709044861)
  ·
    refine ⟨13636040618296017640891823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36362774982122713709044861 13636040618296017640891823)
    ·
      refine ⟨20454060927444026461337735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13636040618296017640891823 20454060927444026461337735)
      ·
        refine ⟨30681091391166039692006603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20454060927444026461337735 30681091391166039692006603)
        ·
          refine ⟨46021637086749059538009905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30681091391166039692006603 46021637086749059538009905)
          ·
            refine ⟨34516227815061794653507429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46021637086749059538009905 34516227815061794653507429)
            ·
              refine ⟨6471792715324086497532643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34516227815061794653507429 6471792715324086497532643)
              ·
                refine ⟨9707689072986129746298965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6471792715324086497532643 9707689072986129746298965)
                ·
                  refine ⟨113761981324056207964441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9707689072986129746298965 113761981324056207964441)
                  ·
                    rfl

theorem cell23_1993956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_1993956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1993956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1993956 prefixEnd_1993956 := by exact prefixLift 1993956
  have htrace : WordTrace (prefixWord ++ tailWord_1993956) baseStart_1993956 baseEnd_1993956 := by
    simpa [prefixWord, tailWord_1993956, baseEnd_1993956] using wordTrace_append hprefix tailTrace_1993956
  have hstable : (prefixWord ++ tailWord_1993956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993956).length < 2 ^ (prefixWord ++ tailWord_1993956).sum := by decide
  have hdescent : baseEnd_1993956 < baseStart_1993956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994033 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 1, 6]
def baseStart_1994033 : Nat := 118140960795 + 1994033 * 2 ^ 59
def prefixEnd_1994033 : Nat := 4983230072969 + 3 ^ 40 * 1994033 * 2
def baseEnd_1994033 : Nat := 341299123308967356805705

theorem tailTrace_1994033 : CollatzResearch.WordTrace tailWord_1994033 prefixEnd_1994033 341299123308967356805705 := by
  unfold tailWord_1994033
  simp only [CollatzResearch.WordTrace]
  refine ⟨72728358384966469568642753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48485572256644313045761835 72728358384966469568642753)
  ·
    refine ⟨54546268788724852176482065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72728358384966469568642753 54546268788724852176482065)
    ·
      refine ⟨40909701591543639132361549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54546268788724852176482065 40909701591543639132361549)
      ·
        refine ⟨15341138096828864674635581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40909701591543639132361549 15341138096828864674635581)
        ·
          refine ⟨5752926786310824252988343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15341138096828864674635581 5752926786310824252988343)
          ·
            refine ⟨8629390179466236379482515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5752926786310824252988343 8629390179466236379482515)
            ·
              refine ⟨12944085269199354569223773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8629390179466236379482515 12944085269199354569223773)
              ·
                refine ⟨4854031975949757963458915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12944085269199354569223773 4854031975949757963458915)
                ·
                  refine ⟨7281047963924636945188373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854031975949757963458915 7281047963924636945188373)
                  ·
                    refine ⟨341299123308967356805705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7281047963924636945188373 341299123308967356805705)
                    ·
                      rfl

theorem cell23_1994033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_1994033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994033 prefixEnd_1994033 := by exact prefixLift 1994033
  have htrace : WordTrace (prefixWord ++ tailWord_1994033) baseStart_1994033 baseEnd_1994033 := by
    simpa [prefixWord, tailWord_1994033, baseEnd_1994033] using wordTrace_append hprefix tailTrace_1994033
  have hstable : (prefixWord ++ tailWord_1994033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994033).length < 2 ^ (prefixWord ++ tailWord_1994033).sum := by decide
  have hdescent : baseEnd_1994033 < baseStart_1994033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994073 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 3, 3, 3]
def baseStart_1994073 : Nat := 118140960795 + 1994073 * 2 ^ 59
def prefixEnd_1994073 : Nat := 4983230072969 + 3 ^ 40 * 1994073 * 2
def baseEnd_1994073 : Nat := 1023917909153081913916931

theorem tailTrace_1994073 : CollatzResearch.WordTrace tailWord_1994073 prefixEnd_1994073 1023917909153081913916931 := by
  unfold tailWord_1994073
  simp only [CollatzResearch.WordTrace]
  refine ⟨72729817304821556400098873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48486544869881037600065915 72729817304821556400098873)
  ·
    refine ⟨54547362978616167300074155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72729817304821556400098873 54547362978616167300074155)
    ·
      refine ⟨81821044467924250950111233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54547362978616167300074155 81821044467924250950111233)
      ·
        refine ⟨61365783350943188212583425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81821044467924250950111233 61365783350943188212583425)
        ·
          refine ⟨46024337513207391159437569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61365783350943188212583425 46024337513207391159437569)
          ·
            refine ⟨34518253134905543369578177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46024337513207391159437569 34518253134905543369578177)
            ·
              refine ⟨25888689851179157527183633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34518253134905543369578177 25888689851179157527183633)
              ·
                refine ⟨19416517388384368145387725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25888689851179157527183633 19416517388384368145387725)
                ·
                  refine ⟨7281194020644138054520397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19416517388384368145387725 7281194020644138054520397)
                  ·
                    refine ⟨2730447757741551770445149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7281194020644138054520397 2730447757741551770445149)
                    ·
                      refine ⟨1023917909153081913916931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2730447757741551770445149 1023917909153081913916931)
                      ·
                        rfl

theorem cell23_1994073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_1994073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994073 prefixEnd_1994073 := by exact prefixLift 1994073
  have htrace : WordTrace (prefixWord ++ tailWord_1994073) baseStart_1994073 baseEnd_1994073 := by
    simpa [prefixWord, tailWord_1994073, baseEnd_1994073] using wordTrace_append hprefix tailTrace_1994073
  have hstable : (prefixWord ++ tailWord_1994073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994073).length < 2 ^ (prefixWord ++ tailWord_1994073).sum := by decide
  have hdescent : baseEnd_1994073 < baseStart_1994073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994074 : List Nat := [3, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2]
def baseStart_1994074 : Nat := 118140960795 + 1994074 * 2 ^ 59
def prefixEnd_1994074 : Nat := 4983230072969 + 3 ^ 40 * 1994074 * 2
def baseEnd_1994074 : Nat := 1023918422633736410004427

theorem tailTrace_1994074 : CollatzResearch.WordTrace tailWord_1994074 prefixEnd_1994074 1023918422633736410004427 := by
  unfold tailWord_1994074
  simp only [CollatzResearch.WordTrace]
  refine ⟨18182463444454483392721319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48486569185211955713923517 18182463444454483392721319)
  ·
    refine ⟨27273695166681725089081979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18182463444454483392721319 27273695166681725089081979)
    ·
      refine ⟨40910542750022587633622969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27273695166681725089081979 40910542750022587633622969)
      ·
        refine ⟨30682907062516940725217227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40910542750022587633622969 30682907062516940725217227)
        ·
          refine ⟨46024360593775411087825841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30682907062516940725217227 46024360593775411087825841)
          ·
            refine ⟨34518270445331558315869381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46024360593775411087825841 34518270445331558315869381)
            ·
              refine ⟨6472175708499667184225509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34518270445331558315869381 6472175708499667184225509)
              ·
                refine ⟨1213532945343687597042283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6472175708499667184225509 1213532945343687597042283)
                ·
                  refine ⟨1820299418015531395563425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213532945343687597042283 1820299418015531395563425)
                  ·
                    refine ⟨1365224563511648546672569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1820299418015531395563425 1365224563511648546672569)
                    ·
                      refine ⟨1023918422633736410004427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1365224563511648546672569 1023918422633736410004427)
                      ·
                        rfl

theorem cell23_1994074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_1994074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994074 prefixEnd_1994074 := by exact prefixLift 1994074
  have htrace : WordTrace (prefixWord ++ tailWord_1994074) baseStart_1994074 baseEnd_1994074 := by
    simpa [prefixWord, tailWord_1994074, baseEnd_1994074] using wordTrace_append hprefix tailTrace_1994074
  have hstable : (prefixWord ++ tailWord_1994074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994074).length < 2 ^ (prefixWord ++ tailWord_1994074).sum := by decide
  have hdescent : baseEnd_1994074 < baseStart_1994074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994087 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_1994087 : Nat := 118140960795 + 1994087 * 2 ^ 59
def prefixEnd_1994087 : Nat := 4983230072969 + 3 ^ 40 * 1994087 * 2
def baseEnd_1994087 : Nat := 1023925097882244859141867

theorem tailTrace_1994087 : CollatzResearch.WordTrace tailWord_1994087 prefixEnd_1994087 1023925097882244859141867 := by
  unfold tailWord_1994087
  simp only [CollatzResearch.WordTrace]
  refine ⟨72730327926770836791108515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48486885284513891194072343 72730327926770836791108515)
  ·
    refine ⟨109095491890156255186662773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72730327926770836791108515 109095491890156255186662773)
    ·
      refine ⟨10227702364702148923749635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109095491890156255186662773 10227702364702148923749635)
      ·
        refine ⟨15341553547053223385624453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10227702364702148923749635 15341553547053223385624453)
        ·
          refine ⟨2876541290072479384804585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15341553547053223385624453 2876541290072479384804585)
          ·
            refine ⟨2157405967554359538603439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2876541290072479384804585 2157405967554359538603439)
            ·
              refine ⟨3236108951331539307905159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157405967554359538603439 3236108951331539307905159)
              ·
                refine ⟨4854163426997308961857739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3236108951331539307905159 4854163426997308961857739)
                ·
                  refine ⟨7281245140495963442786609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854163426997308961857739 7281245140495963442786609)
                  ·
                    refine ⟨5460933855371972582089957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7281245140495963442786609 5460933855371972582089957)
                    ·
                      refine ⟨1023925097882244859141867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5460933855371972582089957 1023925097882244859141867)
                      ·
                        rfl

theorem cell23_1994087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_1994087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994087 prefixEnd_1994087 := by exact prefixLift 1994087
  have htrace : WordTrace (prefixWord ++ tailWord_1994087) baseStart_1994087 baseEnd_1994087 := by
    simpa [prefixWord, tailWord_1994087, baseEnd_1994087] using wordTrace_append hprefix tailTrace_1994087
  have hstable : (prefixWord ++ tailWord_1994087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994087).length < 2 ^ (prefixWord ++ tailWord_1994087).sum := by decide
  have hdescent : baseEnd_1994087 < baseStart_1994087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994117 : List Nat := [1, 3, 1, 1, 3, 1, 4, 3, 1, 3, 2]
def baseStart_1994117 : Nat := 118140960795 + 1994117 * 2 ^ 59
def prefixEnd_1994117 : Nat := 4983230072969 + 3 ^ 40 * 1994117 * 2
def baseEnd_1994117 : Nat := 1023940502301879741766729

theorem tailTrace_1994117 : CollatzResearch.WordTrace tailWord_1994117 prefixEnd_1994117 1023940502301879741766729 := by
  unfold tailWord_1994117
  simp only [CollatzResearch.WordTrace]
  refine ⟨72731422116662151914700605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48487614744441434609800403 72731422116662151914700605)
  ·
    refine ⟨27274283293748306968012727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72731422116662151914700605 27274283293748306968012727)
    ·
      refine ⟨40911424940622460452019091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27274283293748306968012727 40911424940622460452019091)
      ·
        refine ⟨61367137410933690678028637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40911424940622460452019091 61367137410933690678028637)
        ·
          refine ⟨23012676529100134004260739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61367137410933690678028637 23012676529100134004260739)
          ·
            refine ⟨34519014793650201006391109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23012676529100134004260739 34519014793650201006391109)
            ·
              refine ⟨6472315273809412688698333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34519014793650201006391109 6472315273809412688698333)
              ·
                refine ⟨2427118227678529758261875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6472315273809412688698333 2427118227678529758261875)
                ·
                  refine ⟨3640677341517794637392813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427118227678529758261875 3640677341517794637392813)
                  ·
                    refine ⟨1365254003069172989022305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3640677341517794637392813 1365254003069172989022305)
                    ·
                      refine ⟨1023940502301879741766729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1365254003069172989022305 1023940502301879741766729)
                      ·
                        rfl

theorem cell23_1994117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 3, 2].length) (baseStart_1994117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994117 prefixEnd_1994117 := by exact prefixLift 1994117
  have htrace : WordTrace (prefixWord ++ tailWord_1994117) baseStart_1994117 baseEnd_1994117 := by
    simpa [prefixWord, tailWord_1994117, baseEnd_1994117] using wordTrace_append hprefix tailTrace_1994117
  have hstable : (prefixWord ++ tailWord_1994117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994117).length < 2 ^ (prefixWord ++ tailWord_1994117).sum := by decide
  have hdescent : baseEnd_1994117 < baseStart_1994117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994141 : List Nat := [1, 4, 2, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_1994141 : Nat := 118140960795 + 1994141 * 2 ^ 59
def prefixEnd_1994141 : Nat := 4983230072969 + 3 ^ 40 * 1994141 * 2
def baseEnd_1994141 : Nat := 1023952825837587647866619

theorem tailTrace_1994141 : CollatzResearch.WordTrace tailWord_1994141 prefixEnd_1994141 1023952825837587647866619 := by
  unfold tailWord_1994141
  simp only [CollatzResearch.WordTrace]
  refine ⟨72732297468575204013574277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48488198312383469342382851 72732297468575204013574277)
  ·
    refine ⟨13637305775357850752545177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72732297468575204013574277 13637305775357850752545177)
    ·
      refine ⟨10227979331518388064408883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13637305775357850752545177 10227979331518388064408883)
      ·
        refine ⟨15341968997277582096613325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10227979331518388064408883 15341968997277582096613325)
        ·
          refine ⟨5753238373979093286229997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15341968997277582096613325 5753238373979093286229997)
          ·
            refine ⟨2157464390242159982336249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5753238373979093286229997 2157464390242159982336249)
            ·
              refine ⟨1618098292681619986752187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2157464390242159982336249 1618098292681619986752187)
              ·
                refine ⟨2427147439022429980128281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618098292681619986752187 2427147439022429980128281)
                ·
                  refine ⟨1820360579266822485096211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2427147439022429980128281 1820360579266822485096211)
                  ·
                    refine ⟨2730540868900233727644317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1820360579266822485096211 2730540868900233727644317)
                    ·
                      refine ⟨1023952825837587647866619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2730540868900233727644317 1023952825837587647866619)
                      ·
                        rfl

theorem cell23_1994141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_1994141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994141 prefixEnd_1994141 := by exact prefixLift 1994141
  have htrace : WordTrace (prefixWord ++ tailWord_1994141) baseStart_1994141 baseEnd_1994141 := by
    simpa [prefixWord, tailWord_1994141, baseEnd_1994141] using wordTrace_append hprefix tailTrace_1994141
  have hstable : (prefixWord ++ tailWord_1994141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994141).length < 2 ^ (prefixWord ++ tailWord_1994141).sum := by decide
  have hdescent : baseEnd_1994141 < baseStart_1994141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994187 : List Nat := [1, 1, 1, 1, 3, 3, 6, 2, 5]
def baseStart_1994187 : Nat := 118140960795 + 1994187 * 2 ^ 59
def prefixEnd_1994187 : Nat := 4983230072969 + 3 ^ 40 * 1994187 * 2
def baseEnd_1994187 : Nat := 113775160660854940876823

theorem tailTrace_1994187 : CollatzResearch.WordTrace tailWord_1994187 prefixEnd_1994187 113775160660854940876823 := by
  unfold tailWord_1994187
  simp only [CollatzResearch.WordTrace]
  refine ⟨72733975226408553869748815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48489316817605702579832543 72733975226408553869748815)
  ·
    refine ⟨109100962839612830804623223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72733975226408553869748815 109100962839612830804623223)
    ·
      refine ⟨163651444259419246206934835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109100962839612830804623223 163651444259419246206934835)
      ·
        refine ⟨245477166389128869310402253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163651444259419246206934835 245477166389128869310402253)
        ·
          refine ⟨92053937395923325991400845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245477166389128869310402253 92053937395923325991400845)
          ·
            refine ⟨34520226523471247246775317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92053937395923325991400845 34520226523471247246775317)
            ·
              refine ⟨1618135618287714714692593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34520226523471247246775317 1618135618287714714692593)
              ·
                refine ⟨1213601713715786036019445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1618135618287714714692593 1213601713715786036019445)
                ·
                  refine ⟨113775160660854940876823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1213601713715786036019445 113775160660854940876823)
                  ·
                    rfl

theorem cell23_1994187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 5].length) (baseStart_1994187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994187 prefixEnd_1994187 := by exact prefixLift 1994187
  have htrace : WordTrace (prefixWord ++ tailWord_1994187) baseStart_1994187 baseEnd_1994187 := by
    simpa [prefixWord, tailWord_1994187, baseEnd_1994187] using wordTrace_append hprefix tailTrace_1994187
  have hstable : (prefixWord ++ tailWord_1994187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994187).length < 2 ^ (prefixWord ++ tailWord_1994187).sum := by decide
  have hdescent : baseEnd_1994187 < baseStart_1994187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994203 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 4]
def baseStart_1994203 : Nat := 118140960795 + 1994203 * 2 ^ 59
def prefixEnd_1994203 : Nat := 4983230072969 + 3 ^ 40 * 1994203 * 2
def baseEnd_1994203 : Nat := 1023984661638166405291333

theorem tailTrace_1994203 : CollatzResearch.WordTrace tailWord_1994203 prefixEnd_1994203 1023984661638166405291333 := by
  unfold tailWord_1994203
  simp only [CollatzResearch.WordTrace]
  refine ⟨72734558794350588602331263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48489705862900392401554175 72734558794350588602331263)
  ·
    refine ⟨109101838191525882903496895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72734558794350588602331263 109101838191525882903496895)
    ·
      refine ⟨163652757287288824355245343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109101838191525882903496895 163652757287288824355245343)
      ·
        refine ⟨245479135930933236532868015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163652757287288824355245343 245479135930933236532868015)
        ·
          refine ⟨368218703896399854799302023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245479135930933236532868015 368218703896399854799302023)
          ·
            refine ⟨552328055844599782198953035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368218703896399854799302023 552328055844599782198953035)
            ·
              refine ⟨828492083766899673298429553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552328055844599782198953035 828492083766899673298429553)
              ·
                refine ⟨621369062825174754973822165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828492083766899673298429553 621369062825174754973822165)
                ·
                  refine ⟨14563337409965033319698957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 621369062825174754973822165 14563337409965033319698957)
                  ·
                    refine ⟨5461251528736887494887109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14563337409965033319698957 5461251528736887494887109)
                    ·
                      refine ⟨1023984661638166405291333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5461251528736887494887109 1023984661638166405291333)
                      ·
                        rfl

theorem cell23_1994203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 4].length) (baseStart_1994203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994203 prefixEnd_1994203 := by exact prefixLift 1994203
  have htrace : WordTrace (prefixWord ++ tailWord_1994203) baseStart_1994203 baseEnd_1994203 := by
    simpa [prefixWord, tailWord_1994203, baseEnd_1994203] using wordTrace_append hprefix tailTrace_1994203
  have hstable : (prefixWord ++ tailWord_1994203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994203).length < 2 ^ (prefixWord ++ tailWord_1994203).sum := by decide
  have hdescent : baseEnd_1994203 < baseStart_1994203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994220 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 4]
def baseStart_1994220 : Nat := 118140960795 + 1994220 * 2 ^ 59
def prefixEnd_1994220 : Nat := 4983230072969 + 3 ^ 40 * 1994220 * 2
def baseEnd_1994220 : Nat := 1023993390809292838778755

theorem tailTrace_1994220 : CollatzResearch.WordTrace tailWord_1994220 prefixEnd_1994220 1023993390809292838778755 := by
  unfold tailWord_1994220
  simp only [CollatzResearch.WordTrace]
  refine ⟨36367589417644500252850057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48490119223526000337133409 36367589417644500252850057)
  ·
    refine ⟨27275692063233375189637543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36367589417644500252850057 27275692063233375189637543)
    ·
      refine ⟨40913538094850062784456315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27275692063233375189637543 40913538094850062784456315)
      ·
        refine ⟨61370307142275094176684473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40913538094850062784456315 61370307142275094176684473)
        ·
          refine ⟨46027730356706320632513355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61370307142275094176684473 46027730356706320632513355)
          ·
            refine ⟨69041595535059480948770033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46027730356706320632513355 69041595535059480948770033)
            ·
              refine ⟨51781196651294610711577525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69041595535059480948770033 51781196651294610711577525)
              ·
                refine ⟨4854487186058869754210393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51781196651294610711577525 4854487186058869754210393)
                ·
                  refine ⟨3640865389544152315657795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4854487186058869754210393 3640865389544152315657795)
                  ·
                    refine ⟨5461298084316228473486693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3640865389544152315657795 5461298084316228473486693)
                    ·
                      refine ⟨1023993390809292838778755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5461298084316228473486693 1023993390809292838778755)
                      ·
                        rfl

theorem cell23_1994220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_1994220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994220 prefixEnd_1994220 := by exact prefixLift 1994220
  have htrace : WordTrace (prefixWord ++ tailWord_1994220) baseStart_1994220 baseEnd_1994220 := by
    simpa [prefixWord, tailWord_1994220, baseEnd_1994220] using wordTrace_append hprefix tailTrace_1994220
  have hstable : (prefixWord ++ tailWord_1994220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994220).length < 2 ^ (prefixWord ++ tailWord_1994220).sum := by decide
  have hdescent : baseEnd_1994220 < baseStart_1994220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994237 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 2, 4, 2]
def baseStart_1994237 : Nat := 118140960795 + 1994237 * 2 ^ 59
def prefixEnd_1994237 : Nat := 4983230072969 + 3 ^ 40 * 1994237 * 2
def baseEnd_1994237 : Nat := 1024002119980419272266177

theorem tailTrace_1994237 : CollatzResearch.WordTrace tailWord_1994237 prefixEnd_1994237 1024002119980419272266177 := by
  unfold tailWord_1994237
  simp only [CollatzResearch.WordTrace]
  refine ⟨72735798876227412409068965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48490532584151608272712643 72735798876227412409068965)
  ·
    refine ⟨13637962289292639826700431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72735798876227412409068965 13637962289292639826700431)
    ·
      refine ⟨20456943433938959740050647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13637962289292639826700431 20456943433938959740050647)
      ·
        refine ⟨30685415150908439610075971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20456943433938959740050647 30685415150908439610075971)
        ·
          refine ⟨46028122726362659415113957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30685415150908439610075971 46028122726362659415113957)
          ·
            refine ⟨8630273011192998640333867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46028122726362659415113957 8630273011192998640333867)
            ·
              refine ⟨12945409516789497960500801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8630273011192998640333867 12945409516789497960500801)
              ·
                refine ⟨9709057137592123470375601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12945409516789497960500801 9709057137592123470375601)
                ·
                  refine ⟨7281792853194092602781701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9709057137592123470375601 7281792853194092602781701)
                  ·
                    refine ⟨1365336159973892363021569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7281792853194092602781701 1365336159973892363021569)
                    ·
                      refine ⟨1024002119980419272266177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1365336159973892363021569 1024002119980419272266177)
                      ·
                        rfl

theorem cell23_1994237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_1994237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994237 prefixEnd_1994237 := by exact prefixLift 1994237
  have htrace : WordTrace (prefixWord ++ tailWord_1994237) baseStart_1994237 baseEnd_1994237 := by
    simpa [prefixWord, tailWord_1994237, baseEnd_1994237] using wordTrace_append hprefix tailTrace_1994237
  have hstable : (prefixWord ++ tailWord_1994237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994237).length < 2 ^ (prefixWord ++ tailWord_1994237).sum := by decide
  have hdescent : baseEnd_1994237 < baseStart_1994237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994247 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 3, 4]
def baseStart_1994247 : Nat := 118140960795 + 1994247 * 2 ^ 59
def prefixEnd_1994247 : Nat := 4983230072969 + 3 ^ 40 * 1994247 * 2
def baseEnd_1994247 : Nat := 341335751595654744380377

theorem tailTrace_1994247 : CollatzResearch.WordTrace tailWord_1994247 prefixEnd_1994247 341335751595654744380377 := by
  unfold tailWord_1994247
  simp only [CollatzResearch.WordTrace]
  refine ⟨72736163606191184116932995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48490775737460789411288663 72736163606191184116932995)
  ·
    refine ⟨109104245409286776175399493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72736163606191184116932995 109104245409286776175399493)
    ·
      refine ⟨20457046014241270532887405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109104245409286776175399493 20457046014241270532887405)
      ·
        refine ⟨7671392255340476449832777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20457046014241270532887405 7671392255340476449832777)
        ·
          refine ⟨5753544191505357337374583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7671392255340476449832777 5753544191505357337374583)
          ·
            refine ⟨8630316287258036006061875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5753544191505357337374583 8630316287258036006061875)
            ·
              refine ⟨12945474430887054009092813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8630316287258036006061875 12945474430887054009092813)
              ·
                refine ⟨4854552911582645253409805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12945474430887054009092813 4854552911582645253409805)
                ·
                  refine ⟨1820457341843491970028677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4854552911582645253409805 1820457341843491970028677)
                  ·
                    refine ⟨341335751595654744380377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1820457341843491970028677 341335751595654744380377)
                    ·
                      rfl

theorem cell23_1994247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_1994247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994247 prefixEnd_1994247 := by exact prefixLift 1994247
  have htrace : WordTrace (prefixWord ++ tailWord_1994247) baseStart_1994247 baseEnd_1994247 := by
    simpa [prefixWord, tailWord_1994247, baseEnd_1994247] using wordTrace_append hprefix tailTrace_1994247
  have hstable : (prefixWord ++ tailWord_1994247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994247).length < 2 ^ (prefixWord ++ tailWord_1994247).sum := by decide
  have hdescent : baseEnd_1994247 < baseStart_1994247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994290 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_1994290 : Nat := 118140960795 + 1994290 * 2 ^ 59
def prefixEnd_1994290 : Nat := 4983230072969 + 3 ^ 40 * 1994290 * 2
def baseEnd_1994290 : Nat := 341343111485035854967811

theorem tailTrace_1994290 : CollatzResearch.WordTrace tailWord_1994290 prefixEnd_1994290 341343111485035854967811 := by
  unfold tailWord_1994290
  simp only [CollatzResearch.WordTrace]
  refine ⟨18184432986258850615187081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48491821296690268307165549 18184432986258850615187081)
  ·
    refine ⟨13638324739694137961390311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18184432986258850615187081 13638324739694137961390311)
    ·
      refine ⟨20457487109541206942085467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13638324739694137961390311 20457487109541206942085467)
      ·
        refine ⟨30686230664311810413128201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20457487109541206942085467 30686230664311810413128201)
        ·
          refine ⟨23014672998233857809846151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30686230664311810413128201 23014672998233857809846151)
          ·
            refine ⟨34522009497350786714769227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23014672998233857809846151 34522009497350786714769227)
            ·
              refine ⟨51783014246026180072153841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34522009497350786714769227 51783014246026180072153841)
              ·
                refine ⟨38837260684519635054115381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51783014246026180072153841 38837260684519635054115381)
                ·
                  refine ⟨3640993189173715786323317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38837260684519635054115381 3640993189173715786323317)
                  ·
                    refine ⟨341343111485035854967811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3640993189173715786323317 341343111485035854967811)
                    ·
                      rfl

theorem cell23_1994290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_1994290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994290 prefixEnd_1994290 := by exact prefixLift 1994290
  have htrace : WordTrace (prefixWord ++ tailWord_1994290) baseStart_1994290 baseEnd_1994290 := by
    simpa [prefixWord, tailWord_1994290, baseEnd_1994290] using wordTrace_append hprefix tailTrace_1994290
  have hstable : (prefixWord ++ tailWord_1994290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994290).length < 2 ^ (prefixWord ++ tailWord_1994290).sum := by decide
  have hdescent : baseEnd_1994290 < baseStart_1994290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994311 : List Nat := [1, 1, 4, 1, 6, 1, 2, 1, 6]
def baseStart_1994311 : Nat := 118140960795 + 1994311 * 2 ^ 59
def prefixEnd_1994311 : Nat := 4983230072969 + 3 ^ 40 * 1994311 * 2
def baseEnd_1994311 : Nat := 113782235283205775860093

theorem tailTrace_1994311 : CollatzResearch.WordTrace tailWord_1994311 prefixEnd_1994311 113782235283205775860093 := by
  unfold tailWord_1994311
  simp only [CollatzResearch.WordTrace]
  refine ⟨72738497877959323047262787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48492331918639548698175191 72738497877959323047262787)
  ·
    refine ⟨109107746816938984570894181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72738497877959323047262787 109107746816938984570894181)
    ·
      refine ⟨20457702528176059607042659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109107746816938984570894181 20457702528176059607042659)
      ·
        refine ⟨30686553792264089410563989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20457702528176059607042659 30686553792264089410563989)
        ·
          refine ⟨1438432209012379191120187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30686553792264089410563989 1438432209012379191120187)
          ·
            refine ⟨2157648313518568786680281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438432209012379191120187 2157648313518568786680281)
            ·
              refine ⟨1618236235138926590010211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2157648313518568786680281 1618236235138926590010211)
              ·
                refine ⟨2427354352708389885015317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618236235138926590010211 2427354352708389885015317)
                ·
                  refine ⟨113782235283205775860093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2427354352708389885015317 113782235283205775860093)
                  ·
                    rfl

theorem cell23_1994311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 6].length) (baseStart_1994311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994311 prefixEnd_1994311 := by exact prefixLift 1994311
  have htrace : WordTrace (prefixWord ++ tailWord_1994311) baseStart_1994311 baseEnd_1994311 := by
    simpa [prefixWord, tailWord_1994311, baseEnd_1994311] using wordTrace_append hprefix tailTrace_1994311
  have hstable : (prefixWord ++ tailWord_1994311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994311).length < 2 ^ (prefixWord ++ tailWord_1994311).sum := by decide
  have hdescent : baseEnd_1994311 < baseStart_1994311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994320 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 1, 6]
def baseStart_1994320 : Nat := 118140960795 + 1994320 * 2 ^ 59
def prefixEnd_1994320 : Nat := 4983230072969 + 3 ^ 40 * 1994320 * 2
def baseEnd_1994320 : Nat := 341348246291580815842765

theorem tailTrace_1994320 : CollatzResearch.WordTrace tailWord_1994320 prefixEnd_1994320 341348246291580815842765 := by
  unfold tailWord_1994320
  simp only [CollatzResearch.WordTrace]
  refine ⟨36369413067463358792170207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48492550756617811722893609 36369413067463358792170207)
  ·
    refine ⟨54554119601195038188255311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36369413067463358792170207 54554119601195038188255311)
    ·
      refine ⟨81831179401792557282382967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54554119601195038188255311 81831179401792557282382967)
      ·
        refine ⟨122746769102688835923574451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81831179401792557282382967 122746769102688835923574451)
        ·
          refine ⟨184120153654033253885361677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122746769102688835923574451 184120153654033253885361677)
          ·
            refine ⟨69045057620262470207010629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184120153654033253885361677 69045057620262470207010629)
            ·
              refine ⟨12945948303799213163814493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69045057620262470207010629 12945948303799213163814493)
              ·
                refine ⟨4854730613924704936430435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12945948303799213163814493 4854730613924704936430435)
                ·
                  refine ⟨7282095920887057404645653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854730613924704936430435 7282095920887057404645653)
                  ·
                    refine ⟨341348246291580815842765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7282095920887057404645653 341348246291580815842765)
                    ·
                      rfl

theorem cell23_1994320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 1, 6].length) (baseStart_1994320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994320 prefixEnd_1994320 := by exact prefixLift 1994320
  have htrace : WordTrace (prefixWord ++ tailWord_1994320) baseStart_1994320 baseEnd_1994320 := by
    simpa [prefixWord, tailWord_1994320, baseEnd_1994320] using wordTrace_append hprefix tailTrace_1994320
  have hstable : (prefixWord ++ tailWord_1994320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994320).length < 2 ^ (prefixWord ++ tailWord_1994320).sum := by decide
  have hdescent : baseEnd_1994320 < baseStart_1994320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994327 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 4]
def baseStart_1994327 : Nat := 118140960795 + 1994327 * 2 ^ 59
def prefixEnd_1994327 : Nat := 4983230072969 + 3 ^ 40 * 1994327 * 2
def baseEnd_1994327 : Nat := 1024048333239323920140763

theorem tailTrace_1994327 : CollatzResearch.WordTrace tailWord_1994327 prefixEnd_1994327 1024048333239323920140763 := by
  unfold tailWord_1994327
  simp only [CollatzResearch.WordTrace]
  refine ⟨72739081445901357779845235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48492720963934238519896823 72739081445901357779845235)
  ·
    refine ⟨109108622168852036669767853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72739081445901357779845235 109108622168852036669767853)
    ·
      refine ⟨40915733313319513751162945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109108622168852036669767853 40915733313319513751162945)
      ·
        refine ⟨30686799984989635313372209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40915733313319513751162945 30686799984989635313372209)
        ·
          refine ⟨23015099988742226485029157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30686799984989635313372209 23015099988742226485029157)
          ·
            refine ⟨4315331247889167465942967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23015099988742226485029157 4315331247889167465942967)
            ·
              refine ⟨6472996871833751198914451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4315331247889167465942967 6472996871833751198914451)
              ·
                refine ⟨9709495307750626798371677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6472996871833751198914451 9709495307750626798371677)
                ·
                  refine ⟨3641060740406485049389379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9709495307750626798371677 3641060740406485049389379)
                  ·
                    refine ⟨5461591110609727574084069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3641060740406485049389379 5461591110609727574084069)
                    ·
                      refine ⟨1024048333239323920140763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5461591110609727574084069 1024048333239323920140763)
                      ·
                        rfl

theorem cell23_1994327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_1994327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994327 prefixEnd_1994327 := by exact prefixLift 1994327
  have htrace : WordTrace (prefixWord ++ tailWord_1994327) baseStart_1994327 baseEnd_1994327 := by
    simpa [prefixWord, tailWord_1994327, baseEnd_1994327] using wordTrace_append hprefix tailTrace_1994327
  have hstable : (prefixWord ++ tailWord_1994327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994327).length < 2 ^ (prefixWord ++ tailWord_1994327).sum := by decide
  have hdescent : baseEnd_1994327 < baseStart_1994327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994330 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_1994330 : Nat := 118140960795 + 1994330 * 2 ^ 59
def prefixEnd_1994330 : Nat := 4983230072969 + 3 ^ 40 * 1994330 * 2
def baseEnd_1994330 : Nat := 1024049873681287408403249

theorem tailTrace_1994330 : CollatzResearch.WordTrace tailWord_1994330 prefixEnd_1994330 1024049873681287408403249 := by
  unfold tailWord_1994330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18184797716222622323051111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48492793909926992861469629 18184797716222622323051111)
  ·
    refine ⟨27277196574333933484576667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18184797716222622323051111 27277196574333933484576667)
    ·
      refine ⟨40915794861500900226865001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27277196574333933484576667 40915794861500900226865001)
      ·
        refine ⟨30686846146125675170148751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40915794861500900226865001 30686846146125675170148751)
        ·
          refine ⟨46030269219188512755223127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30686846146125675170148751 46030269219188512755223127)
          ·
            refine ⟨69045403828782769132834691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46030269219188512755223127 69045403828782769132834691)
            ·
              refine ⟨103568105743174153699252037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69045403828782769132834691 103568105743174153699252037)
              ·
                refine ⟨19419019826845153818609757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103568105743174153699252037 19419019826845153818609757)
                ·
                  refine ⟨7282132435066932681978659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19419019826845153818609757 7282132435066932681978659)
                  ·
                    refine ⟨10923198652600399022967989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7282132435066932681978659 10923198652600399022967989)
                    ·
                      refine ⟨1024049873681287408403249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10923198652600399022967989 1024049873681287408403249)
                      ·
                        rfl

theorem cell23_1994330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_1994330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994330 prefixEnd_1994330 := by exact prefixLift 1994330
  have htrace : WordTrace (prefixWord ++ tailWord_1994330) baseStart_1994330 baseEnd_1994330 := by
    simpa [prefixWord, tailWord_1994330, baseEnd_1994330] using wordTrace_append hprefix tailTrace_1994330
  have hstable : (prefixWord ++ tailWord_1994330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994330).length < 2 ^ (prefixWord ++ tailWord_1994330).sum := by decide
  have hdescent : baseEnd_1994330 < baseStart_1994330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994350 : List Nat := [4, 1, 2, 2, 14]
def baseStart_1994350 : Nat := 118140960795 + 1994350 * 2 ^ 59
def prefixEnd_1994350 : Nat := 4983230072969 + 3 ^ 40 * 1994350 * 2
def baseEnd_1994350 : Nat := 1404746424272122537933

theorem tailTrace_1994350 : CollatzResearch.WordTrace tailWord_1994350 prefixEnd_1994350 1404746424272122537933 := by
  unfold tailWord_1994350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9092490040602254088491563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48493280216545355138621669 9092490040602254088491563)
  ·
    refine ⟨13638735060903381132737345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9092490040602254088491563 13638735060903381132737345)
    ·
      refine ⟨10229051295677535849553009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13638735060903381132737345 10229051295677535849553009)
      ·
        refine ⟨7671788471758151887164757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10229051295677535849553009 7671788471758151887164757)
        ·
          refine ⟨1404746424272122537933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 7671788471758151887164757 1404746424272122537933)
          ·
            rfl

theorem cell23_1994350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 14].length) (baseStart_1994350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994350 prefixEnd_1994350 := by exact prefixLift 1994350
  have htrace : WordTrace (prefixWord ++ tailWord_1994350) baseStart_1994350 baseEnd_1994350 := by
    simpa [prefixWord, tailWord_1994350, baseEnd_1994350] using wordTrace_append hprefix tailTrace_1994350
  have hstable : (prefixWord ++ tailWord_1994350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994350).length < 2 ^ (prefixWord ++ tailWord_1994350).sum := by decide
  have hdescent : baseEnd_1994350 < baseStart_1994350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994354 : List Nat := [3, 2, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_1994354 : Nat := 118140960795 + 1994354 * 2 ^ 59
def prefixEnd_1994354 : Nat := 4983230072969 + 3 ^ 40 * 1994354 * 2
def baseEnd_1994354 : Nat := 341354065738998438167713

theorem tailTrace_1994354 : CollatzResearch.WordTrace tailWord_1994354 prefixEnd_1994354 341354065738998438167713 := by
  unfold tailWord_1994354
  simp only [CollatzResearch.WordTrace]
  refine ⟨18185016554200885347769529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48493377477869027594052077 18185016554200885347769529)
  ·
    refine ⟨13638762415650664010827147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18185016554200885347769529 13638762415650664010827147)
    ·
      refine ⟨20458143623475996016240721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13638762415650664010827147 20458143623475996016240721)
      ·
        refine ⟨15343607717606997012180541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20458143623475996016240721 15343607717606997012180541)
        ·
          refine ⟨5753852894102623879567703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15343607717606997012180541 5753852894102623879567703)
          ·
            refine ⟨8630779341153935819351555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5753852894102623879567703 8630779341153935819351555)
            ·
              refine ⟨12946169011730903729027333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8630779341153935819351555 12946169011730903729027333)
              ·
                refine ⟨2427406689699544449192625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12946169011730903729027333 2427406689699544449192625)
                ·
                  refine ⟨1820555017274658336894469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2427406689699544449192625 1820555017274658336894469)
                  ·
                    refine ⟨341354065738998438167713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1820555017274658336894469 341354065738998438167713)
                    ·
                      rfl

theorem cell23_1994354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_1994354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994354 prefixEnd_1994354 := by exact prefixLift 1994354
  have htrace : WordTrace (prefixWord ++ tailWord_1994354) baseStart_1994354 baseEnd_1994354 := by
    simpa [prefixWord, tailWord_1994354, baseEnd_1994354] using wordTrace_append hprefix tailTrace_1994354
  have hstable : (prefixWord ++ tailWord_1994354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994354).length < 2 ^ (prefixWord ++ tailWord_1994354).sum := by decide
  have hdescent : baseEnd_1994354 < baseStart_1994354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994377 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 1, 3, 3]
def baseStart_1994377 : Nat := 118140960795 + 1994377 * 2 ^ 59
def prefixEnd_1994377 : Nat := 4983230072969 + 3 ^ 40 * 1994377 * 2
def baseEnd_1994377 : Nat := 1024074007272048724515533

theorem tailTrace_1994377 : CollatzResearch.WordTrace tailWord_1994377 prefixEnd_1994377 1024074007272048724515533 := by
  unfold tailWord_1994377
  simp only [CollatzResearch.WordTrace]
  refine ⟨72740905095720216319165385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48493936730480144212776923 72740905095720216319165385)
  ·
    refine ⟨54555678821790162239374039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72740905095720216319165385 54555678821790162239374039)
    ·
      refine ⟨81833518232685243359061059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54555678821790162239374039 81833518232685243359061059)
      ·
        refine ⟨122750277349027865038591589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81833518232685243359061059 122750277349027865038591589)
        ·
          refine ⟨23015677002942724694735923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122750277349027865038591589 23015677002942724694735923)
          ·
            refine ⟨34523515504414087042103885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23015677002942724694735923 34523515504414087042103885)
            ·
              refine ⟨12946318314155282640788957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34523515504414087042103885 12946318314155282640788957)
              ·
                refine ⟨4854869367808230990295859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12946318314155282640788957 4854869367808230990295859)
                ·
                  refine ⟨7282304051712346485443789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854869367808230990295859 7282304051712346485443789)
                  ·
                    refine ⟨2730864019392129932041421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7282304051712346485443789 2730864019392129932041421)
                    ·
                      refine ⟨1024074007272048724515533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2730864019392129932041421 1024074007272048724515533)
                      ·
                        rfl

theorem cell23_1994377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 3, 3].length) (baseStart_1994377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994377 prefixEnd_1994377 := by exact prefixLift 1994377
  have htrace : WordTrace (prefixWord ++ tailWord_1994377) baseStart_1994377 baseEnd_1994377 := by
    simpa [prefixWord, tailWord_1994377, baseEnd_1994377] using wordTrace_append hprefix tailTrace_1994377
  have hstable : (prefixWord ++ tailWord_1994377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994377).length < 2 ^ (prefixWord ++ tailWord_1994377).sum := by decide
  have hdescent : baseEnd_1994377 < baseStart_1994377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994380 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 2, 7]
def baseStart_1994380 : Nat := 118140960795 + 1994380 * 2 ^ 59
def prefixEnd_1994380 : Nat := 4983230072969 + 3 ^ 40 * 1994380 * 2
def baseEnd_1994380 : Nat := 341358515904670737592673

theorem tailTrace_1994380 : CollatzResearch.WordTrace tailWord_1994380 prefixEnd_1994380 341358515904670737592673 := by
  unfold tailWord_1994380
  simp only [CollatzResearch.WordTrace]
  refine ⟨36370507257354673915762297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48494009676472898554349729 36370507257354673915762297)
  ·
    refine ⟨27277880443016005436821723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36370507257354673915762297 27277880443016005436821723)
    ·
      refine ⟨40916820664524008155232585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27277880443016005436821723 40916820664524008155232585)
      ·
        refine ⟨30687615498393006116424439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40916820664524008155232585 30687615498393006116424439)
        ·
          refine ⟨46031423247589509174636659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30687615498393006116424439 46031423247589509174636659)
          ·
            refine ⟨69047134871384263761954989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46031423247589509174636659 69047134871384263761954989)
            ·
              refine ⟨25892675576769098910733121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69047134871384263761954989 25892675576769098910733121)
              ·
                refine ⟨19419506682576824183049841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25892675576769098910733121 19419506682576824183049841)
                ·
                  refine ⟨14564630011932618137287381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19419506682576824183049841 14564630011932618137287381)
                  ·
                    refine ⟨341358515904670737592673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14564630011932618137287381 341358515904670737592673)
                    ·
                      rfl

theorem cell23_1994380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_1994380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994380 prefixEnd_1994380 := by exact prefixLift 1994380
  have htrace : WordTrace (prefixWord ++ tailWord_1994380) baseStart_1994380 baseEnd_1994380 := by
    simpa [prefixWord, tailWord_1994380, baseEnd_1994380] using wordTrace_append hprefix tailTrace_1994380
  have hstable : (prefixWord ++ tailWord_1994380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994380).length < 2 ^ (prefixWord ++ tailWord_1994380).sum := by decide
  have hdescent : baseEnd_1994380 < baseStart_1994380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994398 : List Nat := [4, 3, 1, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_1994398 : Nat := 118140960795 + 1994398 * 2 ^ 59
def prefixEnd_1994398 : Nat := 4983230072969 + 3 ^ 40 * 1994398 * 2
def baseEnd_1994398 : Nat := 1024084790365793142352937

theorem tailTrace_1994398 : CollatzResearch.WordTrace tailWord_1994398 prefixEnd_1994398 1024084790365793142352937 := by
  unfold tailWord_1994398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9092708878580517113209981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48494447352429424603786565 9092708878580517113209981)
  ·
    refine ⟨3409765829467693917453743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9092708878580517113209981 3409765829467693917453743)
    ·
      refine ⟨5114648744201540876180615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3409765829467693917453743 5114648744201540876180615)
      ·
        refine ⟨7671973116302311314270923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5114648744201540876180615 7671973116302311314270923)
        ·
          refine ⟨11507959674453466971406385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7671973116302311314270923 11507959674453466971406385)
          ·
            refine ⟨8630969755840100228554789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11507959674453466971406385 8630969755840100228554789)
            ·
              refine ⟨1618306829220018792854023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8630969755840100228554789 1618306829220018792854023)
              ·
                refine ⟨2427460243830028189281035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618306829220018792854023 2427460243830028189281035)
                ·
                  refine ⟨3641190365745042283921553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427460243830028189281035 3641190365745042283921553)
                  ·
                    refine ⟨2730892774308781712941165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3641190365745042283921553 2730892774308781712941165)
                    ·
                      refine ⟨1024084790365793142352937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2730892774308781712941165 1024084790365793142352937)
                      ·
                        rfl

theorem cell23_1994398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_1994398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994398 prefixEnd_1994398 := by exact prefixLift 1994398
  have htrace : WordTrace (prefixWord ++ tailWord_1994398) baseStart_1994398 baseEnd_1994398 := by
    simpa [prefixWord, tailWord_1994398, baseEnd_1994398] using wordTrace_append hprefix tailTrace_1994398
  have hstable : (prefixWord ++ tailWord_1994398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994398).length < 2 ^ (prefixWord ++ tailWord_1994398).sum := by decide
  have hdescent : baseEnd_1994398 < baseStart_1994398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994428 : List Nat := [2, 2, 2, 3, 1, 3, 3, 1, 2, 1, 3]
def baseStart_1994428 : Nat := 118140960795 + 1994428 * 2 ^ 59
def prefixEnd_1994428 : Nat := 4983230072969 + 3 ^ 40 * 1994428 * 2
def baseEnd_1994428 : Nat := 1024100194785428024977799

theorem tailTrace_1994428 : CollatzResearch.WordTrace tailWord_1994428 prefixEnd_1994428 1024100194785428024977799 := by
  unfold tailWord_1994428
  simp only [CollatzResearch.WordTrace]
  refine ⟨36371382609267726014635969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48495176812356968019514625 36371382609267726014635969)
  ·
    refine ⟨27278536956950794510976977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36371382609267726014635969 27278536956950794510976977)
    ·
      refine ⟨20458902717713095883232733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27278536956950794510976977 20458902717713095883232733)
      ·
        refine ⟨7672088519142410956212275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20458902717713095883232733 7672088519142410956212275)
        ·
          refine ⟨11508132778713616434318413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7672088519142410956212275 11508132778713616434318413)
          ·
            refine ⟨4315549792017606162869405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11508132778713616434318413 4315549792017606162869405)
            ·
              refine ⟨1618331172006602311076027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4315549792017606162869405 1618331172006602311076027)
              ·
                refine ⟨2427496758009903466614041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618331172006602311076027 2427496758009903466614041)
                ·
                  refine ⟨1820622568507427599960531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2427496758009903466614041 1820622568507427599960531)
                  ·
                    refine ⟨2730933852761141399940797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1820622568507427599960531 2730933852761141399940797)
                    ·
                      refine ⟨1024100194785428024977799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2730933852761141399940797 1024100194785428024977799)
                      ·
                        rfl

theorem cell23_1994428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_1994428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994428 prefixEnd_1994428 := by exact prefixLift 1994428
  have htrace : WordTrace (prefixWord ++ tailWord_1994428) baseStart_1994428 baseEnd_1994428 := by
    simpa [prefixWord, tailWord_1994428, baseEnd_1994428] using wordTrace_append hprefix tailTrace_1994428
  have hstable : (prefixWord ++ tailWord_1994428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994428).length < 2 ^ (prefixWord ++ tailWord_1994428).sum := by decide
  have hdescent : baseEnd_1994428 < baseStart_1994428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994474 : List Nat := [3, 1, 3, 1, 1, 1, 2, 6, 5]
def baseStart_1994474 : Nat := 118140960795 + 1994474 * 2 ^ 59
def prefixEnd_1994474 : Nat := 4983230072969 + 3 ^ 40 * 1994474 * 2
def baseEnd_1994474 : Nat := 113791534988392760555843

theorem tailTrace_1994474 : CollatzResearch.WordTrace tailWord_1994474 prefixEnd_1994474 113791534988392760555843 := by
  unfold tailWord_1994474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18186110744092200471361619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48496295317579201256964317 18186110744092200471361619)
  ·
    refine ⟨27279166116138300707042429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18186110744092200471361619 27279166116138300707042429)
    ·
      refine ⟨10229687293551862765140911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27279166116138300707042429 10229687293551862765140911)
      ·
        refine ⟨15344530940327794147711367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10229687293551862765140911 15344530940327794147711367)
        ·
          refine ⟨23016796410491691221567051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15344530940327794147711367 23016796410491691221567051)
          ·
            refine ⟨34525194615737536832350577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23016796410491691221567051 34525194615737536832350577)
            ·
              refine ⟨25893895961803152624262933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34525194615737536832350577 25893895961803152624262933)
              ·
                refine ⟨1213776373209522779262325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25893895961803152624262933 1213776373209522779262325)
                ·
                  refine ⟨113791534988392760555843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1213776373209522779262325 113791534988392760555843)
                  ·
                    rfl

theorem cell23_1994474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 5].length) (baseStart_1994474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994474 prefixEnd_1994474 := by exact prefixLift 1994474
  have htrace : WordTrace (prefixWord ++ tailWord_1994474) baseStart_1994474 baseEnd_1994474 := by
    simpa [prefixWord, tailWord_1994474, baseEnd_1994474] using wordTrace_append hprefix tailTrace_1994474
  have hstable : (prefixWord ++ tailWord_1994474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994474).length < 2 ^ (prefixWord ++ tailWord_1994474).sum := by decide
  have hdescent : baseEnd_1994474 < baseStart_1994474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994504 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 2, 5]
def baseStart_1994504 : Nat := 118140960795 + 1994504 * 2 ^ 59
def prefixEnd_1994504 : Nat := 4983230072969 + 3 ^ 40 * 1994504 * 2
def baseEnd_1994504 : Nat := 341379739771723242542483

theorem tailTrace_1994504 : CollatzResearch.WordTrace tailWord_1994504 prefixEnd_1994504 341379739771723242542483 := by
  unfold tailWord_1994504
  simp only [CollatzResearch.WordTrace]
  refine ⟨36372768583130058504519283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48497024777506744672692377 36372768583130058504519283)
  ·
    refine ⟨54559152874695087756778925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36372768583130058504519283 54559152874695087756778925)
    ·
      refine ⟨20459682328010657908792097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54559152874695087756778925 20459682328010657908792097)
      ·
        refine ⟨15344761746007993431594073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20459682328010657908792097 15344761746007993431594073)
        ·
          refine ⟨11508571309505995073695555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15344761746007993431594073 11508571309505995073695555)
          ·
            refine ⟨17262856964258992610543333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11508571309505995073695555 17262856964258992610543333)
            ·
              refine ⟨3236785680798561114476875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17262856964258992610543333 3236785680798561114476875)
              ·
                refine ⟨4855178521197841671715313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3236785680798561114476875 4855178521197841671715313)
                ·
                  refine ⟨3641383890898381253786485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4855178521197841671715313 3641383890898381253786485)
                  ·
                    refine ⟨341379739771723242542483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3641383890898381253786485 341379739771723242542483)
                    ·
                      rfl

theorem cell23_1994504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_1994504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994504 prefixEnd_1994504 := by exact prefixLift 1994504
  have htrace : WordTrace (prefixWord ++ tailWord_1994504) baseStart_1994504 baseEnd_1994504 := by
    simpa [prefixWord, tailWord_1994504, baseEnd_1994504] using wordTrace_append hprefix tailTrace_1994504
  have hstable : (prefixWord ++ tailWord_1994504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994504).length < 2 ^ (prefixWord ++ tailWord_1994504).sum := by decide
  have hdescent : baseEnd_1994504 < baseStart_1994504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994507 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 4]
def baseStart_1994507 : Nat := 118140960795 + 1994507 * 2 ^ 59
def prefixEnd_1994507 : Nat := 4983230072969 + 3 ^ 40 * 1994507 * 2
def baseEnd_1994507 : Nat := 1024140759757133215889935

theorem tailTrace_1994507 : CollatzResearch.WordTrace tailWord_1994507 prefixEnd_1994507 1024140759757133215889935 := by
  unfold tailWord_1994507
  simp only [CollatzResearch.WordTrace]
  refine ⟨72745646585249248521397775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48497097723499499014265183 72745646585249248521397775)
  ·
    refine ⟨109118469877873872782096663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72745646585249248521397775 109118469877873872782096663)
    ·
      refine ⟨163677704816810809173144995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109118469877873872782096663 163677704816810809173144995)
      ·
        refine ⟨245516557225216213759717493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163677704816810809173144995 245516557225216213759717493)
        ·
          refine ⟨23017177239864020039973515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245516557225216213759717493 23017177239864020039973515)
          ·
            refine ⟨34525765859796030059960273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23017177239864020039973515 34525765859796030059960273)
            ·
              refine ⟨25894324394847022544970205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34525765859796030059960273 25894324394847022544970205)
              ·
                refine ⟨9710371648067633454363827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25894324394847022544970205 9710371648067633454363827)
                ·
                  refine ⟨14565557472101450181545741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9710371648067633454363827 14565557472101450181545741)
                  ·
                    refine ⟨5462084052038043818079653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14565557472101450181545741 5462084052038043818079653)
                    ·
                      refine ⟨1024140759757133215889935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5462084052038043818079653 1024140759757133215889935)
                      ·
                        rfl

theorem cell23_1994507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 4].length) (baseStart_1994507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994507 prefixEnd_1994507 := by exact prefixLift 1994507
  have htrace : WordTrace (prefixWord ++ tailWord_1994507) baseStart_1994507 baseEnd_1994507 := by
    simpa [prefixWord, tailWord_1994507, baseEnd_1994507] using wordTrace_append hprefix tailTrace_1994507
  have hstable : (prefixWord ++ tailWord_1994507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994507).length < 2 ^ (prefixWord ++ tailWord_1994507).sum := by decide
  have hdescent : baseEnd_1994507 < baseStart_1994507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994524 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1994524 : Nat := 118140960795 + 1994524 * 2 ^ 59
def prefixEnd_1994524 : Nat := 4983230072969 + 3 ^ 40 * 1994524 * 2
def baseEnd_1994524 : Nat := 1024149488928259649377357

theorem tailTrace_1994524 : CollatzResearch.WordTrace tailWord_1994524 prefixEnd_1994524 1024149488928259649377357 := by
  unfold tailWord_1994524
  simp only [CollatzResearch.WordTrace]
  refine ⟨36373133313093830212383313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48497511084125106949844417 36373133313093830212383313)
  ·
    refine ⟨27279849984820372659287485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36373133313093830212383313 27279849984820372659287485)
    ·
      refine ⟨10229943744307639747232807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27279849984820372659287485 10229943744307639747232807)
      ·
        refine ⟨15344915616461459620849211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10229943744307639747232807 15344915616461459620849211)
        ·
          refine ⟨23017373424692189431273817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15344915616461459620849211 23017373424692189431273817)
          ·
            refine ⟨17263030068519142073455363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23017373424692189431273817 17263030068519142073455363)
            ·
              refine ⟨25894545102778713110183045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17263030068519142073455363 25894545102778713110183045)
              ·
                refine ⟨4855227206771008708159321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25894545102778713110183045 4855227206771008708159321)
                ·
                  refine ⟨3641420405078256531119491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4855227206771008708159321 3641420405078256531119491)
                  ·
                    refine ⟨5462130607617384796679237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3641420405078256531119491 5462130607617384796679237)
                    ·
                      refine ⟨1024149488928259649377357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5462130607617384796679237 1024149488928259649377357)
                      ·
                        rfl

theorem cell23_1994524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1994524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994524 prefixEnd_1994524 := by exact prefixLift 1994524
  have htrace : WordTrace (prefixWord ++ tailWord_1994524) baseStart_1994524 baseEnd_1994524 := by
    simpa [prefixWord, tailWord_1994524, baseEnd_1994524] using wordTrace_append hprefix tailTrace_1994524
  have hstable : (prefixWord ++ tailWord_1994524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994524).length < 2 ^ (prefixWord ++ tailWord_1994524).sum := by decide
  have hdescent : baseEnd_1994524 < baseStart_1994524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994527 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 5]
def baseStart_1994527 : Nat := 118140960795 + 1994527 * 2 ^ 59
def prefixEnd_1994527 : Nat := 4983230072969 + 3 ^ 40 * 1994527 * 2
def baseEnd_1994527 : Nat := 1024151029370223137639843

theorem tailTrace_1994527 : CollatzResearch.WordTrace tailWord_1994527 prefixEnd_1994527 1024151029370223137639843 := by
  unfold tailWord_1994527
  simp only [CollatzResearch.WordTrace]
  refine ⟨72746376045176791937125835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48497584030117861291417223 72746376045176791937125835)
  ·
    refine ⟨109119564067765187905688753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72746376045176791937125835 109119564067765187905688753)
    ·
      refine ⟨81839673050823890929266565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109119564067765187905688753 81839673050823890929266565)
      ·
        refine ⟨15344938697029479549237481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81839673050823890929266565 15344938697029479549237481)
        ·
          refine ⟨11508704022772109661928111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15344938697029479549237481 11508704022772109661928111)
          ·
            refine ⟨17263056034158164492892167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11508704022772109661928111 17263056034158164492892167)
            ·
              refine ⟨25894584051237246739338251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17263056034158164492892167 25894584051237246739338251)
              ·
                refine ⟨38841876076855870109007377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25894584051237246739338251 38841876076855870109007377)
                ·
                  refine ⟨29131407057641902581755533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38841876076855870109007377 29131407057641902581755533)
                  ·
                    refine ⟨10924277646615713468158325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29131407057641902581755533 10924277646615713468158325)
                    ·
                      refine ⟨1024151029370223137639843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10924277646615713468158325 1024151029370223137639843)
                      ·
                        rfl

theorem cell23_1994527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_1994527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994527 prefixEnd_1994527 := by exact prefixLift 1994527
  have htrace : WordTrace (prefixWord ++ tailWord_1994527) baseStart_1994527 baseEnd_1994527 := by
    simpa [prefixWord, tailWord_1994527, baseEnd_1994527] using wordTrace_append hprefix tailTrace_1994527
  have hstable : (prefixWord ++ tailWord_1994527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994527).length < 2 ^ (prefixWord ++ tailWord_1994527).sum := by decide
  have hdescent : baseEnd_1994527 < baseStart_1994527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994558 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_1994558 : Nat := 118140960795 + 1994558 * 2 ^ 59
def prefixEnd_1994558 : Nat := 4983230072969 + 3 ^ 40 * 1994558 * 2
def baseEnd_1994558 : Nat := 1024166947270512516352201

theorem tailTrace_1994558 : CollatzResearch.WordTrace tailWord_1994558 prefixEnd_1994558 1024166947270512516352201 := by
  unfold tailWord_1994558
  simp only [CollatzResearch.WordTrace]
  refine ⟨9093438338508060528938041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48498337805376322821002885 9093438338508060528938041)
  ·
    refine ⟨6820078753881045396703531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9093438338508060528938041 6820078753881045396703531)
    ·
      refine ⟨10230118130821568095055297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6820078753881045396703531 10230118130821568095055297)
      ·
        refine ⟨7672588598116176071291473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10230118130821568095055297 7672588598116176071291473)
        ·
          refine ⟨5754441448587132053468605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7672588598116176071291473 5754441448587132053468605)
          ·
            refine ⟨2157915543220174520050727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5754441448587132053468605 2157915543220174520050727)
            ·
              refine ⟨3236873314830261780076091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157915543220174520050727 3236873314830261780076091)
              ·
                refine ⟨4855309972245392670114137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3236873314830261780076091 4855309972245392670114137)
                ·
                  refine ⟨3641482479184044502585603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4855309972245392670114137 3641482479184044502585603)
                  ·
                    refine ⟨5462223718776066753878405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3641482479184044502585603 5462223718776066753878405)
                    ·
                      refine ⟨1024166947270512516352201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5462223718776066753878405 1024166947270512516352201)
                      ·
                        rfl

theorem cell23_1994558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_1994558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994558 prefixEnd_1994558 := by exact prefixLift 1994558
  have htrace : WordTrace (prefixWord ++ tailWord_1994558) baseStart_1994558 baseEnd_1994558 := by
    simpa [prefixWord, tailWord_1994558, baseEnd_1994558] using wordTrace_append hprefix tailTrace_1994558
  have hstable : (prefixWord ++ tailWord_1994558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994558).length < 2 ^ (prefixWord ++ tailWord_1994558).sum := by decide
  have hdescent : baseEnd_1994558 < baseStart_1994558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994568 : List Nat := [2, 1, 3, 1, 1, 5, 2, 3, 1, 4]
def baseStart_1994568 : Nat := 118140960795 + 1994568 * 2 ^ 59
def prefixEnd_1994568 : Nat := 4983230072969 + 3 ^ 40 * 1994568 * 2
def baseEnd_1994568 : Nat := 341390694025685825742385

theorem tailTrace_1994568 : CollatzResearch.WordTrace tailWord_1994568 prefixEnd_1994568 341390694025685825742385 := by
  unfold tailWord_1994568
  simp only [CollatzResearch.WordTrace]
  refine ⟨36373935719014127969684179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48498580958685503959578905 36373935719014127969684179)
  ·
    refine ⟨54560903578521191954526269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36373935719014127969684179 54560903578521191954526269)
    ·
      refine ⟨20460338841945446982947351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54560903578521191954526269 20460338841945446982947351)
      ·
        refine ⟨30690508262918170474421027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20460338841945446982947351 30690508262918170474421027)
        ·
          refine ⟨46035762394377255711631541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30690508262918170474421027 46035762394377255711631541)
          ·
            refine ⟨4315852724472867722965457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46035762394377255711631541 4315852724472867722965457)
            ·
              refine ⟨3236889543354650792224093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4315852724472867722965457 3236889543354650792224093)
              ·
                refine ⟨1213833578757994047084035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3236889543354650792224093 1213833578757994047084035)
                ·
                  refine ⟨1820750368136991070626053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213833578757994047084035 1820750368136991070626053)
                  ·
                    refine ⟨341390694025685825742385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1820750368136991070626053 341390694025685825742385)
                    ·
                      rfl

theorem cell23_1994568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_1994568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994568 prefixEnd_1994568 := by exact prefixLift 1994568
  have htrace : WordTrace (prefixWord ++ tailWord_1994568) baseStart_1994568 baseEnd_1994568 := by
    simpa [prefixWord, tailWord_1994568, baseEnd_1994568] using wordTrace_append hprefix tailTrace_1994568
  have hstable : (prefixWord ++ tailWord_1994568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994568).length < 2 ^ (prefixWord ++ tailWord_1994568).sum := by decide
  have hdescent : baseEnd_1994568 < baseStart_1994568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994581 : List Nat := [1, 3, 2, 2, 2, 4, 1, 2, 6]
def baseStart_1994581 : Nat := 118140960795 + 1994581 * 2 ^ 59
def prefixEnd_1994581 : Nat := 4983230072969 + 3 ^ 40 * 1994581 * 2
def baseEnd_1994581 : Nat := 113797639702840658484955

theorem tailTrace_1994581 : CollatzResearch.WordTrace tailWord_1994581 prefixEnd_1994581 113797639702840658484955 := by
  unfold tailWord_1994581
  simp only [CollatzResearch.WordTrace]
  refine ⟨72748345586981159159591597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48498897057987439439727731 72748345586981159159591597)
  ·
    refine ⟨27280629595117934684846849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72748345586981159159591597 27280629595117934684846849)
    ·
      refine ⟨20460472196338451013635137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27280629595117934684846849 20460472196338451013635137)
      ·
        refine ⟨15345354147253838260226353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20460472196338451013635137 15345354147253838260226353)
        ·
          refine ⟨11509015610440378695169765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15345354147253838260226353 11509015610440378695169765)
          ·
            refine ⟨2157940426957571005344331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11509015610440378695169765 2157940426957571005344331)
            ·
              refine ⟨3236910640436356508016497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157940426957571005344331 3236910640436356508016497)
              ·
                refine ⟨2427682980327267381012373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3236910640436356508016497 2427682980327267381012373)
                ·
                  refine ⟨113797639702840658484955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2427682980327267381012373 113797639702840658484955)
                  ·
                    rfl

theorem cell23_1994581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 6].length) (baseStart_1994581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994581 prefixEnd_1994581 := by exact prefixLift 1994581
  have htrace : WordTrace (prefixWord ++ tailWord_1994581) baseStart_1994581 baseEnd_1994581 := by
    simpa [prefixWord, tailWord_1994581, baseEnd_1994581] using wordTrace_append hprefix tailTrace_1994581
  have hstable : (prefixWord ++ tailWord_1994581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994581).length < 2 ^ (prefixWord ++ tailWord_1994581).sum := by decide
  have hdescent : baseEnd_1994581 < baseStart_1994581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994591 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 3, 1, 3]
def baseStart_1994591 : Nat := 118140960795 + 1994591 * 2 ^ 59
def prefixEnd_1994591 : Nat := 4983230072969 + 3 ^ 40 * 1994591 * 2
def baseEnd_1994591 : Nat := 1024183892132110887239549

theorem tailTrace_1994591 : CollatzResearch.WordTrace tailWord_1994591 prefixEnd_1994591 1024183892132110887239549 := by
  unfold tailWord_1994591
  simp only [CollatzResearch.WordTrace]
  refine ⟨72748710316944930867455627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48499140211296620578303751 72748710316944930867455627)
  ·
    refine ⟨109123065475417396301183441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72748710316944930867455627 109123065475417396301183441)
    ·
      refine ⟨81842299106563047225887581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109123065475417396301183441 81842299106563047225887581)
      ·
        refine ⟨30690862164961142709707843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81842299106563047225887581 30690862164961142709707843)
        ·
          refine ⟨46036293247441714064561765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30690862164961142709707843 46036293247441714064561765)
          ·
            refine ⟨8631804983895321387105331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46036293247441714064561765 8631804983895321387105331)
            ·
              refine ⟨12947707475842982080657997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8631804983895321387105331 12947707475842982080657997)
              ·
                refine ⟨4855390303441118280246749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12947707475842982080657997 4855390303441118280246749)
                ·
                  refine ⟨1820771363790419355092531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4855390303441118280246749 1820771363790419355092531)
                  ·
                    refine ⟨2731157045685629032638797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1820771363790419355092531 2731157045685629032638797)
                    ·
                      refine ⟨1024183892132110887239549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2731157045685629032638797 1024183892132110887239549)
                      ·
                        rfl

theorem cell23_1994591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_1994591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994591 prefixEnd_1994591 := by exact prefixLift 1994591
  have htrace : WordTrace (prefixWord ++ tailWord_1994591) baseStart_1994591 baseEnd_1994591 := by
    simpa [prefixWord, tailWord_1994591, baseEnd_1994591] using wordTrace_append hprefix tailTrace_1994591
  have hstable : (prefixWord ++ tailWord_1994591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994591).length < 2 ^ (prefixWord ++ tailWord_1994591).sum := by decide
  have hdescent : baseEnd_1994591 < baseStart_1994591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994624 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 6, 4]
def baseStart_1994624 : Nat := 118140960795 + 1994624 * 2 ^ 59
def prefixEnd_1994624 : Nat := 4983230072969 + 3 ^ 40 * 1994624 * 2
def baseEnd_1994624 : Nat := 341400278997903086042299

theorem tailTrace_1994624 : CollatzResearch.WordTrace tailWord_1994624 prefixEnd_1994624 341400278997903086042299 := by
  unfold tailWord_1994624
  simp only [CollatzResearch.WordTrace]
  refine ⟨36374956962912688751703463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48499942617216918335604617 36374956962912688751703463)
  ·
    refine ⟨54562435444369033127555195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36374956962912688751703463 54562435444369033127555195)
    ·
      refine ⟨81843653166553549691332793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54562435444369033127555195 81843653166553549691332793)
      ·
        refine ⟨61382739874915162268499595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81843653166553549691332793 61382739874915162268499595)
        ·
          refine ⟨92074109812372743402749393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61382739874915162268499595 92074109812372743402749393)
          ·
            refine ⟨69055582359279557552062045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92074109812372743402749393 69055582359279557552062045)
            ·
              refine ⟨25895843384729834082023267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69055582359279557552062045 25895843384729834082023267)
              ·
                refine ⟨38843765077094751123034901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25895843384729834082023267 38843765077094751123034901)
                ·
                  refine ⟨1820801487988816458892261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38843765077094751123034901 1820801487988816458892261)
                  ·
                    refine ⟨341400278997903086042299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1820801487988816458892261 341400278997903086042299)
                    ·
                      rfl

theorem cell23_1994624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6, 4].length) (baseStart_1994624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994624 prefixEnd_1994624 := by exact prefixLift 1994624
  have htrace : WordTrace (prefixWord ++ tailWord_1994624) baseStart_1994624 baseEnd_1994624 := by
    simpa [prefixWord, tailWord_1994624, baseEnd_1994624] using wordTrace_append hprefix tailTrace_1994624
  have hstable : (prefixWord ++ tailWord_1994624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994624).length < 2 ^ (prefixWord ++ tailWord_1994624).sum := by decide
  have hdescent : baseEnd_1994624 < baseStart_1994624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994681 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 1, 3, 3]
def baseStart_1994681 : Nat := 118140960795 + 1994681 * 2 ^ 59
def prefixEnd_1994681 : Nat := 4983230072969 + 3 ^ 40 * 1994681 * 2
def baseEnd_1994681 : Nat := 1024230105391015535114135

theorem tailTrace_1994681 : CollatzResearch.WordTrace tailWord_1994681 prefixEnd_1994681 1024230105391015535114135 := by
  unfold tailWord_1994681
  simp only [CollatzResearch.WordTrace]
  refine ⟨72751992886618876238231897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48501328591079250825487931 72751992886618876238231897)
  ·
    refine ⟨54563994664964157178673923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72751992886618876238231897 54563994664964157178673923)
    ·
      refine ⟨81845991997446235768010885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54563994664964157178673923 81845991997446235768010885)
      ·
        refine ⟨15346123499521169206502041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81845991997446235768010885 15346123499521169206502041)
        ·
          refine ⟨11509592624640876904876531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15346123499521169206502041 11509592624640876904876531)
          ·
            refine ⟨17264388936961315357314797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11509592624640876904876531 17264388936961315357314797)
            ·
              refine ⟨6474145851360493258993049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17264388936961315357314797 6474145851360493258993049)
              ·
                refine ⟨4855609388520369944244787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6474145851360493258993049 4855609388520369944244787)
                ·
                  refine ⟨7283414082780554916367181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4855609388520369944244787 7283414082780554916367181)
                  ·
                    refine ⟨2731280281042708093637693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7283414082780554916367181 2731280281042708093637693)
                    ·
                      refine ⟨1024230105391015535114135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2731280281042708093637693 1024230105391015535114135)
                      ·
                        rfl

theorem cell23_1994681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_1994681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994681 prefixEnd_1994681 := by exact prefixLift 1994681
  have htrace : WordTrace (prefixWord ++ tailWord_1994681) baseStart_1994681 baseEnd_1994681 := by
    simpa [prefixWord, tailWord_1994681, baseEnd_1994681] using wordTrace_append hprefix tailTrace_1994681
  have hstable : (prefixWord ++ tailWord_1994681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994681).length < 2 ^ (prefixWord ++ tailWord_1994681).sum := by decide
  have hdescent : baseEnd_1994681 < baseStart_1994681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994685 : List Nat := [1, 4, 1, 2, 3, 2, 3, 1, 1, 2, 3]
def baseStart_1994685 : Nat := 118140960795 + 1994685 * 2 ^ 59
def prefixEnd_1994685 : Nat := 4983230072969 + 3 ^ 40 * 1994685 * 2
def baseEnd_1994685 : Nat := 1024232159313633519464117

theorem tailTrace_1994685 : CollatzResearch.WordTrace tailWord_1994685 prefixEnd_1994685 1024232159313633519464117 := by
  unfold tailWord_1994685
  simp only [CollatzResearch.WordTrace]
  refine ⟨72752138778604384921377509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48501425852402923280918339 72752138778604384921377509)
  ·
    refine ⟨13641026020988322172758283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72752138778604384921377509 13641026020988322172758283)
    ·
      refine ⟨20461539031482483259137425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13641026020988322172758283 20461539031482483259137425)
      ·
        refine ⟨15346154273611862444353069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20461539031482483259137425 15346154273611862444353069)
        ·
          refine ⟨5754807852604448416632401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15346154273611862444353069 5754807852604448416632401)
          ·
            refine ⟨4316105889453336312474301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5754807852604448416632401 4316105889453336312474301)
            ·
              refine ⟨1618539708545001117177863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4316105889453336312474301 1618539708545001117177863)
              ·
                refine ⟨2427809562817501675766795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618539708545001117177863 2427809562817501675766795)
                ·
                  refine ⟨3641714344226252513650193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427809562817501675766795 3641714344226252513650193)
                  ·
                    refine ⟨2731285758169689385237645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3641714344226252513650193 2731285758169689385237645)
                    ·
                      refine ⟨1024232159313633519464117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2731285758169689385237645 1024232159313633519464117)
                      ·
                        rfl

theorem cell23_1994685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_1994685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994685 prefixEnd_1994685 := by exact prefixLift 1994685
  have htrace : WordTrace (prefixWord ++ tailWord_1994685) baseStart_1994685 baseEnd_1994685 := by
    simpa [prefixWord, tailWord_1994685, baseEnd_1994685] using wordTrace_append hprefix tailTrace_1994685
  have hstable : (prefixWord ++ tailWord_1994685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994685).length < 2 ^ (prefixWord ++ tailWord_1994685).sum := by decide
  have hdescent : baseEnd_1994685 < baseStart_1994685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994691 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 7, 3, 2]
def baseStart_1994691 : Nat := 118140960795 + 1994691 * 2 ^ 59
def prefixEnd_1994691 : Nat := 4983230072969 + 3 ^ 40 * 1994691 * 2
def baseEnd_1994691 : Nat := 1024235240197560495989089

theorem tailTrace_1994691 : CollatzResearch.WordTrace tailWord_1994691 prefixEnd_1994691 1024235240197560495989089 := by
  unfold tailWord_1994691
  simp only [CollatzResearch.WordTrace]
  refine ⟨72752357616582647946095927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48501571744388431964063951 72752357616582647946095927)
  ·
    refine ⟨109128536424873971919143891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72752357616582647946095927 109128536424873971919143891)
    ·
      refine ⟨163692804637310957878715837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109128536424873971919143891 163692804637310957878715837)
      ·
        refine ⟨61384801738991609204518439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163692804637310957878715837 61384801738991609204518439)
        ·
          refine ⟨92077202608487413806777659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61384801738991609204518439 92077202608487413806777659)
          ·
            refine ⟨138115803912731120710166489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92077202608487413806777659 138115803912731120710166489)
            ·
              refine ⟨103586852934548340532624867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138115803912731120710166489 103586852934548340532624867)
              ·
                refine ⟨155380279401822510798937301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103586852934548340532624867 155380279401822510798937301)
                ·
                  refine ⟨3641725298480215096850093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 155380279401822510798937301 3641725298480215096850093)
                  ·
                    refine ⟨1365646986930080661318785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3641725298480215096850093 1365646986930080661318785)
                    ·
                      refine ⟨1024235240197560495989089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1365646986930080661318785 1024235240197560495989089)
                      ·
                        rfl

theorem cell23_1994691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 3, 2].length) (baseStart_1994691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994691 prefixEnd_1994691 := by exact prefixLift 1994691
  have htrace : WordTrace (prefixWord ++ tailWord_1994691) baseStart_1994691 baseEnd_1994691 := by
    simpa [prefixWord, tailWord_1994691, baseEnd_1994691] using wordTrace_append hprefix tailTrace_1994691
  have hstable : (prefixWord ++ tailWord_1994691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994691).length < 2 ^ (prefixWord ++ tailWord_1994691).sum := by decide
  have hdescent : baseEnd_1994691 < baseStart_1994691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994698 : List Nat := [3, 1, 2, 1, 2, 1, 3, 4, 2, 1, 3]
def baseStart_1994698 : Nat := 118140960795 + 1994698 * 2 ^ 59
def prefixEnd_1994698 : Nat := 4983230072969 + 3 ^ 40 * 1994698 * 2
def baseEnd_1994698 : Nat := 1024238834562141968601557

theorem tailTrace_1994698 : CollatzResearch.WordTrace tailWord_1994698 prefixEnd_1994698 1024238834562141968601557 := by
  unfold tailWord_1994698
  simp only [CollatzResearch.WordTrace]
  refine ⟨18188153231889322035400187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48501741951704858761067165 18188153231889322035400187)
  ·
    refine ⟨27282229847833983053100281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18188153231889322035400187 27282229847833983053100281)
    ·
      refine ⟨20461672385875487289825211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27282229847833983053100281 20461672385875487289825211)
      ·
        refine ⟨30692508578813230934737817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20461672385875487289825211 30692508578813230934737817)
        ·
          refine ⟨23019381434109923201053363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30692508578813230934737817 23019381434109923201053363)
          ·
            refine ⟨34529072151164884801580045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23019381434109923201053363 34529072151164884801580045)
            ·
              refine ⟨12948402056686831800592517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34529072151164884801580045 12948402056686831800592517)
              ·
                refine ⟨2427825385628780962611097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12948402056686831800592517 2427825385628780962611097)
                ·
                  refine ⟨1820869039221585721958323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2427825385628780962611097 1820869039221585721958323)
                  ·
                    refine ⟨2731303558832378582937485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1820869039221585721958323 2731303558832378582937485)
                    ·
                      refine ⟨1024238834562141968601557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2731303558832378582937485 1024238834562141968601557)
                      ·
                        rfl

theorem cell23_1994698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_1994698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994698 prefixEnd_1994698 := by exact prefixLift 1994698
  have htrace : WordTrace (prefixWord ++ tailWord_1994698) baseStart_1994698 baseEnd_1994698 := by
    simpa [prefixWord, tailWord_1994698, baseEnd_1994698] using wordTrace_append hprefix tailTrace_1994698
  have hstable : (prefixWord ++ tailWord_1994698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994698).length < 2 ^ (prefixWord ++ tailWord_1994698).sum := by decide
  have hdescent : baseEnd_1994698 < baseStart_1994698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994704 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 4]
def baseStart_1994704 : Nat := 118140960795 + 1994704 * 2 ^ 59
def prefixEnd_1994704 : Nat := 4983230072969 + 3 ^ 40 * 1994704 * 2
def baseEnd_1994704 : Nat := 1024241915446068945126529

theorem tailTrace_1994704 : CollatzResearch.WordTrace tailWord_1994704 prefixEnd_1994704 1024241915446068945126529 := by
  unfold tailWord_1994704
  simp only [CollatzResearch.WordTrace]
  refine ⟨36376415882767775583159583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48501887843690367444212777 36376415882767775583159583)
  ·
    refine ⟨54564623824151663374739375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36376415882767775583159583 54564623824151663374739375)
    ·
      refine ⟨81846935736227495062109063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54564623824151663374739375 81846935736227495062109063)
      ·
        refine ⟨122770403604341242593163595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81846935736227495062109063 122770403604341242593163595)
        ·
          refine ⟨184155605406511863889745393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122770403604341242593163595 184155605406511863889745393)
          ·
            refine ⟨138116704054883897917309045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184155605406511863889745393 138116704054883897917309045)
            ·
              refine ⟨12948441005145365429747723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138116704054883897917309045 12948441005145365429747723)
              ·
                refine ⟨19422661507718048144621585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12948441005145365429747723 19422661507718048144621585)
                ·
                  refine ⟨14566996130788536108466189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19422661507718048144621585 14566996130788536108466189)
                  ·
                    refine ⟨5462623549045701040674821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14566996130788536108466189 5462623549045701040674821)
                    ·
                      refine ⟨1024241915446068945126529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5462623549045701040674821 1024241915446068945126529)
                      ·
                        rfl

theorem cell23_1994704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_1994704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994704 prefixEnd_1994704 := by exact prefixLift 1994704
  have htrace : WordTrace (prefixWord ++ tailWord_1994704) baseStart_1994704 baseEnd_1994704 := by
    simpa [prefixWord, tailWord_1994704, baseEnd_1994704] using wordTrace_append hprefix tailTrace_1994704
  have hstable : (prefixWord ++ tailWord_1994704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994704).length < 2 ^ (prefixWord ++ tailWord_1994704).sum := by decide
  have hdescent : baseEnd_1994704 < baseStart_1994704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994708 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_1994708 : Nat := 118140960795 + 1994708 * 2 ^ 59
def prefixEnd_1994708 : Nat := 4983230072969 + 3 ^ 40 * 1994708 * 2
def baseEnd_1994708 : Nat := 1024243969368686929476511

theorem tailTrace_1994708 : CollatzResearch.WordTrace tailWord_1994708 prefixEnd_1994708 1024243969368686929476511 := by
  unfold tailWord_1994708
  simp only [CollatzResearch.WordTrace]
  refine ⟨36376488828760529924732389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48501985105014039899643185 36376488828760529924732389)
  ·
    refine ⟨6820591655392599360887323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36376488828760529924732389 6820591655392599360887323)
    ·
      refine ⟨10230887483088899041330985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6820591655392599360887323 10230887483088899041330985)
      ·
        refine ⟨7673165612316674280998239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10230887483088899041330985 7673165612316674280998239)
        ·
          refine ⟨11509748418475011421497359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7673165612316674280998239 11509748418475011421497359)
          ·
            refine ⟨17264622627712517132246039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11509748418475011421497359 17264622627712517132246039)
            ·
              refine ⟨25896933941568775698369059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17264622627712517132246039 25896933941568775698369059)
              ·
                refine ⟨38845400912353163547553589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25896933941568775698369059 38845400912353163547553589)
                ·
                  refine ⟨3641756335533109082583149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38845400912353163547553589 3641756335533109082583149)
                  ·
                    refine ⟨1365658625824915905968681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3641756335533109082583149 1365658625824915905968681)
                    ·
                      refine ⟨1024243969368686929476511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1365658625824915905968681 1024243969368686929476511)
                      ·
                        rfl

theorem cell23_1994708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_1994708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994708 prefixEnd_1994708 := by exact prefixLift 1994708
  have htrace : WordTrace (prefixWord ++ tailWord_1994708) baseStart_1994708 baseEnd_1994708 := by
    simpa [prefixWord, tailWord_1994708, baseEnd_1994708] using wordTrace_append hprefix tailTrace_1994708
  have hstable : (prefixWord ++ tailWord_1994708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994708).length < 2 ^ (prefixWord ++ tailWord_1994708).sum := by decide
  have hdescent : baseEnd_1994708 < baseStart_1994708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994742 : List Nat := [5, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_1994742 : Nat := 118140960795 + 1994742 * 2 ^ 59
def prefixEnd_1994742 : Nat := 4983230072969 + 3 ^ 40 * 1994742 * 2
def baseEnd_1994742 : Nat := 1024261427710939796451355

theorem tailTrace_1994742 : CollatzResearch.WordTrace tailWord_1994742 prefixEnd_1994742 1024261427710939796451355 := by
  unfold tailWord_1994742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4547138608712367728512655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48502811826265255770801653 4547138608712367728512655)
  ·
    refine ⟨6820707913068551592768983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4547138608712367728512655 6820707913068551592768983)
    ·
      refine ⟨10231061869602827389153475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6820707913068551592768983 10231061869602827389153475)
      ·
        refine ⟨15346592804404241083730213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10231061869602827389153475 15346592804404241083730213)
        ·
          refine ⟨2877486150825795203199415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15346592804404241083730213 2877486150825795203199415)
          ·
            refine ⟨4316229226238692804799123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2877486150825795203199415 4316229226238692804799123)
            ·
              refine ⟨6474343839358039207198685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316229226238692804799123 6474343839358039207198685)
              ·
                refine ⟨2427878939759264702699507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6474343839358039207198685 2427878939759264702699507)
                ·
                  refine ⟨3641818409638897054049261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427878939759264702699507 3641818409638897054049261)
                  ·
                    refine ⟨1365681903614586395268473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3641818409638897054049261 1365681903614586395268473)
                    ·
                      refine ⟨1024261427710939796451355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1365681903614586395268473 1024261427710939796451355)
                      ·
                        rfl

theorem cell23_1994742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_1994742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994742 prefixEnd_1994742 := by exact prefixLift 1994742
  have htrace : WordTrace (prefixWord ++ tailWord_1994742) baseStart_1994742 baseEnd_1994742 := by
    simpa [prefixWord, tailWord_1994742, baseEnd_1994742] using wordTrace_append hprefix tailTrace_1994742
  have hstable : (prefixWord ++ tailWord_1994742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994742).length < 2 ^ (prefixWord ++ tailWord_1994742).sum := by decide
  have hdescent : baseEnd_1994742 < baseStart_1994742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994771 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 3]
def baseStart_1994771 : Nat := 118140960795 + 1994771 * 2 ^ 59
def prefixEnd_1994771 : Nat := 4983230072969 + 3 ^ 40 * 1994771 * 2
def baseEnd_1994771 : Nat := 1024276318649920182988721

theorem tailTrace_1994771 : CollatzResearch.WordTrace tailWord_1994771 prefixEnd_1994771 1024276318649920182988721 := by
  unfold tailWord_1994771
  simp only [CollatzResearch.WordTrace]
  refine ⟨72755275456292821609008167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48503516970861881072672111 72755275456292821609008167)
  ·
    refine ⟨109132913184439232413512251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72755275456292821609008167 109132913184439232413512251)
    ·
      refine ⟨163699369776658848620268377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109132913184439232413512251 163699369776658848620268377)
      ·
        refine ⟨122774527332494136465201283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163699369776658848620268377 122774527332494136465201283)
        ·
          refine ⟨184161790998741204697801925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122774527332494136465201283 184161790998741204697801925)
          ·
            refine ⟨34530335812263975880837861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184161790998741204697801925 34530335812263975880837861)
            ·
              refine ⟨6474437964799495477657099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34530335812263975880837861 6474437964799495477657099)
              ·
                refine ⟨9711656947199243216485649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6474437964799495477657099 9711656947199243216485649)
                ·
                  refine ⟨7283742710399432412364237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9711656947199243216485649 7283742710399432412364237)
                  ·
                    refine ⟨2731403516399787154636589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7283742710399432412364237 2731403516399787154636589)
                    ·
                      refine ⟨1024276318649920182988721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2731403516399787154636589 1024276318649920182988721)
                      ·
                        rfl

theorem cell23_1994771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 3].length) (baseStart_1994771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994771 prefixEnd_1994771 := by exact prefixLift 1994771
  have htrace : WordTrace (prefixWord ++ tailWord_1994771) baseStart_1994771 baseEnd_1994771 := by
    simpa [prefixWord, tailWord_1994771, baseEnd_1994771] using wordTrace_append hprefix tailTrace_1994771
  have hstable : (prefixWord ++ tailWord_1994771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994771).length < 2 ^ (prefixWord ++ tailWord_1994771).sum := by decide
  have hdescent : baseEnd_1994771 < baseStart_1994771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994808 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 2, 5]
def baseStart_1994808 : Nat := 118140960795 + 1994808 * 2 ^ 59
def prefixEnd_1994808 : Nat := 4983230072969 + 3 ^ 40 * 1994808 * 2
def baseEnd_1994808 : Nat := 341431772478045512742017

theorem tailTrace_1994808 : CollatzResearch.WordTrace tailWord_1994808 prefixEnd_1994808 341431772478045512742017 := by
  unfold tailWord_1994808
  simp only [CollatzResearch.WordTrace]
  refine ⟨36378312478579388464052539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48504416638105851285403385 36378312478579388464052539)
  ·
    refine ⟨54567468717869082696078809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36378312478579388464052539 54567468717869082696078809)
    ·
      refine ⟨40925601538401812022059107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54567468717869082696078809 40925601538401812022059107)
      ·
        refine ⟨61388402307602718033088661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40925601538401812022059107 61388402307602718033088661)
        ·
          refine ⟨2877581358168877407801031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61388402307602718033088661 2877581358168877407801031)
          ·
            refine ⟨4316372037253316111701547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2877581358168877407801031 4316372037253316111701547)
            ·
              refine ⟨6474558055879974167552321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316372037253316111701547 6474558055879974167552321)
              ·
                refine ⟨4855918541909980625664241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6474558055879974167552321 4855918541909980625664241)
                ·
                  refine ⟨3641938906432485469248181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4855918541909980625664241 3641938906432485469248181)
                  ·
                    refine ⟨341431772478045512742017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3641938906432485469248181 341431772478045512742017)
                    ·
                      rfl

theorem cell23_1994808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_1994808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994808 prefixEnd_1994808 := by exact prefixLift 1994808
  have htrace : WordTrace (prefixWord ++ tailWord_1994808) baseStart_1994808 baseEnd_1994808 := by
    simpa [prefixWord, tailWord_1994808, baseEnd_1994808] using wordTrace_append hprefix tailTrace_1994808
  have hstable : (prefixWord ++ tailWord_1994808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994808).length < 2 ^ (prefixWord ++ tailWord_1994808).sum := by decide
  have hdescent : baseEnd_1994808 < baseStart_1994808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994811 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 4]
def baseStart_1994811 : Nat := 118140960795 + 1994811 * 2 ^ 59
def prefixEnd_1994811 : Nat := 4983230072969 + 3 ^ 40 * 1994811 * 2
def baseEnd_1994811 : Nat := 1024296857876100026488537

theorem tailTrace_1994811 : CollatzResearch.WordTrace tailWord_1994811 prefixEnd_1994811 1024296857876100026488537 := by
  unfold tailWord_1994811
  simp only [CollatzResearch.WordTrace]
  refine ⟨72756734376147908440464287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48504489584098605626976191 72756734376147908440464287)
  ·
    refine ⟨109135101564221862660696431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72756734376147908440464287 109135101564221862660696431)
    ·
      refine ⟨163702652346332793991044647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109135101564221862660696431 163702652346332793991044647)
      ·
        refine ⟨245553978519499190986566971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163702652346332793991044647 245553978519499190986566971)
        ·
          refine ⟨368330967779248786479850457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245553978519499190986566971 368330967779248786479850457)
          ·
            refine ⟨276248225834436589859887843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368330967779248786479850457 276248225834436589859887843)
            ·
              refine ⟨414372338751654884789831765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276248225834436589859887843 414372338751654884789831765)
              ·
                refine ⟨4855925844745955681130841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 414372338751654884789831765 4855925844745955681130841)
                ·
                  refine ⟨3641944383559466760848131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4855925844745955681130841 3641944383559466760848131)
                  ·
                    refine ⟨5462916575339200141272197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3641944383559466760848131 5462916575339200141272197)
                    ·
                      refine ⟨1024296857876100026488537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5462916575339200141272197 1024296857876100026488537)
                      ·
                        rfl

theorem cell23_1994811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 4].length) (baseStart_1994811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994811 prefixEnd_1994811 := by exact prefixLift 1994811
  have htrace : WordTrace (prefixWord ++ tailWord_1994811) baseStart_1994811 baseEnd_1994811 := by
    simpa [prefixWord, tailWord_1994811, baseEnd_1994811] using wordTrace_append hprefix tailTrace_1994811
  have hstable : (prefixWord ++ tailWord_1994811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994811).length < 2 ^ (prefixWord ++ tailWord_1994811).sum := by decide
  have hdescent : baseEnd_1994811 < baseStart_1994811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994828 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 2, 4, 2]
def baseStart_1994828 : Nat := 118140960795 + 1994828 * 2 ^ 59
def prefixEnd_1994828 : Nat := 4983230072969 + 3 ^ 40 * 1994828 * 2
def baseEnd_1994828 : Nat := 1024305587047226459975959

theorem tailTrace_1994828 : CollatzResearch.WordTrace tailWord_1994828 prefixEnd_1994828 1024305587047226459975959 := by
  unfold tailWord_1994828
  simp only [CollatzResearch.WordTrace]
  refine ⟨36378677208543160171916569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48504902944724213562555425 36378677208543160171916569)
  ·
    refine ⟨27284007906407370128937427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36378677208543160171916569 27284007906407370128937427)
    ·
      refine ⟨40926011859611055193406141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27284007906407370128937427 40926011859611055193406141)
      ·
        refine ⟨15347254447354145697527303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40926011859611055193406141 15347254447354145697527303)
        ·
          refine ⟨23020881671031218546290955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15347254447354145697527303 23020881671031218546290955)
          ·
            refine ⟨34531322506546827819436433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23020881671031218546290955 34531322506546827819436433)
            ·
              refine ⟨25898491879910120864577325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34531322506546827819436433 25898491879910120864577325)
              ·
                refine ⟨9711934454966295324216497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25898491879910120864577325 9711934454966295324216497)
                ·
                  refine ⟨7283950841224721493162373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9711934454966295324216497 7283950841224721493162373)
                  ·
                    refine ⟨1365740782729635279967945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7283950841224721493162373 1365740782729635279967945)
                    ·
                      refine ⟨1024305587047226459975959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1365740782729635279967945 1024305587047226459975959)
                      ·
                        rfl

theorem cell23_1994828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_1994828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994828 prefixEnd_1994828 := by exact prefixLift 1994828
  have htrace : WordTrace (prefixWord ++ tailWord_1994828) baseStart_1994828 baseEnd_1994828 := by
    simpa [prefixWord, tailWord_1994828, baseEnd_1994828] using wordTrace_append hprefix tailTrace_1994828
  have hstable : (prefixWord ++ tailWord_1994828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994828).length < 2 ^ (prefixWord ++ tailWord_1994828).sum := by decide
  have hdescent : baseEnd_1994828 < baseStart_1994828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994845 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1994845 : Nat := 118140960795 + 1994845 * 2 ^ 59
def prefixEnd_1994845 : Nat := 4983230072969 + 3 ^ 40 * 1994845 * 2
def baseEnd_1994845 : Nat := 1024314316218352893463381

theorem tailTrace_1994845 : CollatzResearch.WordTrace tailWord_1994845 prefixEnd_1994845 1024314316218352893463381 := by
  unfold tailWord_1994845
  simp only [CollatzResearch.WordTrace]
  refine ⟨72757974458024732247201989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48505316305349821498134659 72757974458024732247201989)
  ·
    refine ⟨13642120210879637296350373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72757974458024732247201989 13642120210879637296350373)
    ·
      refine ⟨2557897539539931993065695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13642120210879637296350373 2557897539539931993065695)
      ·
        refine ⟨3836846309309897989598543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2557897539539931993065695 3836846309309897989598543)
        ·
          refine ⟨5755269463964846984397815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3836846309309897989598543 5755269463964846984397815)
          ·
            refine ⟨8632904195947270476596723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5755269463964846984397815 8632904195947270476596723)
            ·
              refine ⟨12949356293920905714895085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8632904195947270476596723 12949356293920905714895085)
              ·
                refine ⟨4856008610220339643085657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12949356293920905714895085 4856008610220339643085657)
                ·
                  refine ⟨3642006457665254732314243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4856008610220339643085657 3642006457665254732314243)
                  ·
                    refine ⟨5463009686497882098471365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3642006457665254732314243 5463009686497882098471365)
                    ·
                      refine ⟨1024314316218352893463381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5463009686497882098471365 1024314316218352893463381)
                      ·
                        rfl

theorem cell23_1994845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1994845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994845 prefixEnd_1994845 := by exact prefixLift 1994845
  have htrace : WordTrace (prefixWord ++ tailWord_1994845) baseStart_1994845 baseEnd_1994845 := by
    simpa [prefixWord, tailWord_1994845, baseEnd_1994845] using wordTrace_append hprefix tailTrace_1994845
  have hstable : (prefixWord ++ tailWord_1994845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994845).length < 2 ^ (prefixWord ++ tailWord_1994845).sum := by decide
  have hdescent : baseEnd_1994845 < baseStart_1994845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994848 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 3]
def baseStart_1994848 : Nat := 118140960795 + 1994848 * 2 ^ 59
def prefixEnd_1994848 : Nat := 4983230072969 + 3 ^ 40 * 1994848 * 2
def baseEnd_1994848 : Nat := 1024315856660316381725867

theorem tailTrace_1994848 : CollatzResearch.WordTrace tailWord_1994848 prefixEnd_1994848 1024315856660316381725867 := by
  unfold tailWord_1994848
  simp only [CollatzResearch.WordTrace]
  refine ⟨36379041938506931879780599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48505389251342575839707465 36379041938506931879780599)
  ·
    refine ⟨54568562907760397819670899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36379041938506931879780599 54568562907760397819670899)
    ·
      refine ⟨81852844361640596729506349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54568562907760397819670899 81852844361640596729506349)
      ·
        refine ⟨30694816635615223773564881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81852844361640596729506349 30694816635615223773564881)
        ·
          refine ⟨23021112476711417830173661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30694816635615223773564881 23021112476711417830173661)
          ·
            refine ⟨8632917178766781686315123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23021112476711417830173661 8632917178766781686315123)
            ·
              refine ⟨12949375768150172529472685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8632917178766781686315123 12949375768150172529472685)
              ·
                refine ⟨4856015913056314698552257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12949375768150172529472685 4856015913056314698552257)
                ·
                  refine ⟨3642011934792236023914193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4856015913056314698552257 3642011934792236023914193)
                  ·
                    refine ⟨2731508951094177017935645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3642011934792236023914193 2731508951094177017935645)
                    ·
                      refine ⟨1024315856660316381725867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2731508951094177017935645 1024315856660316381725867)
                      ·
                        rfl

theorem cell23_1994848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_1994848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994848 prefixEnd_1994848 := by exact prefixLift 1994848
  have htrace : WordTrace (prefixWord ++ tailWord_1994848) baseStart_1994848 baseEnd_1994848 := by
    simpa [prefixWord, tailWord_1994848, baseEnd_1994848] using wordTrace_append hprefix tailTrace_1994848
  have hstable : (prefixWord ++ tailWord_1994848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994848).length < 2 ^ (prefixWord ++ tailWord_1994848).sum := by decide
  have hdescent : baseEnd_1994848 < baseStart_1994848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994855 : List Nat := [1, 1, 5, 1, 1, 2, 2, 5, 1, 4]
def baseStart_1994855 : Nat := 118140960795 + 1994855 * 2 ^ 59
def prefixEnd_1994855 : Nat := 4983230072969 + 3 ^ 40 * 1994855 * 2
def baseEnd_1994855 : Nat := 341439817008299284779445

theorem tailTrace_1994855 : CollatzResearch.WordTrace tailWord_1994855 prefixEnd_1994855 341439817008299284779445 := by
  unfold tailWord_1994855
  simp only [CollatzResearch.WordTrace]
  refine ⟨72758339187988503955066019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48505559458659002636710679 72758339187988503955066019)
  ·
    refine ⟨109137508781982755932599029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72758339187988503955066019 109137508781982755932599029)
    ·
      refine ⟨10231641448310883368681159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109137508781982755932599029 10231641448310883368681159)
      ·
        refine ⟨15347462172466325053021739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10231641448310883368681159 15347462172466325053021739)
        ·
          refine ⟨23021193258699487579532609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15347462172466325053021739 23021193258699487579532609)
          ·
            refine ⟨17265894944024615684649457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23021193258699487579532609 17265894944024615684649457)
            ·
              refine ⟨12949421208018461763487093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17265894944024615684649457 12949421208018461763487093)
              ·
                refine ⟨1214008238251730790326915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12949421208018461763487093 1214008238251730790326915)
                ·
                  refine ⟨1821012357377596185490373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1214008238251730790326915 1821012357377596185490373)
                  ·
                    refine ⟨341439817008299284779445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1821012357377596185490373 341439817008299284779445)
                    ·
                      rfl

theorem cell23_1994855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_1994855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994855 prefixEnd_1994855 := by exact prefixLift 1994855
  have htrace : WordTrace (prefixWord ++ tailWord_1994855) baseStart_1994855 baseEnd_1994855 := by
    simpa [prefixWord, tailWord_1994855, baseEnd_1994855] using wordTrace_append hprefix tailTrace_1994855
  have hstable : (prefixWord ++ tailWord_1994855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994855).length < 2 ^ (prefixWord ++ tailWord_1994855).sum := by decide
  have hdescent : baseEnd_1994855 < baseStart_1994855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994898 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1994898 : Nat := 118140960795 + 1994898 * 2 ^ 59
def prefixEnd_1994898 : Nat := 4983230072969 + 3 ^ 40 * 1994898 * 2
def baseEnd_1994898 : Nat := 341447176897680395366879

theorem tailTrace_1994898 : CollatzResearch.WordTrace tailWord_1994898 prefixEnd_1994898 341447176897680395366879 := by
  unfold tailWord_1994898
  simp only [CollatzResearch.WordTrace]
  refine ⟨18189976881708180574720337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48506605017888481532587565 18189976881708180574720337)
  ·
    refine ⟨13642482661281135431040253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18189976881708180574720337 13642482661281135431040253)
    ·
      refine ⟨5115930997980425786640095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13642482661281135431040253 5115930997980425786640095)
      ·
        refine ⟨7673896496970638679960143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5115930997980425786640095 7673896496970638679960143)
        ·
          refine ⟨11510844745455958019940215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7673896496970638679960143 11510844745455958019940215)
          ·
            refine ⟨17266267118183937029910323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11510844745455958019940215 17266267118183937029910323)
            ·
              refine ⟨25899400677275905544865485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17266267118183937029910323 25899400677275905544865485)
              ·
                refine ⟨9712275253978464579324557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25899400677275905544865485 9712275253978464579324557)
                ·
                  refine ⟨3642103220241924217246709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9712275253978464579324557 3642103220241924217246709)
                  ·
                    refine ⟨341447176897680395366879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3642103220241924217246709 341447176897680395366879)
                    ·
                      rfl

theorem cell23_1994898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1994898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994898 prefixEnd_1994898 := by exact prefixLift 1994898
  have htrace : WordTrace (prefixWord ++ tailWord_1994898) baseStart_1994898 baseEnd_1994898 := by
    simpa [prefixWord, tailWord_1994898, baseEnd_1994898] using wordTrace_append hprefix tailTrace_1994898
  have hstable : (prefixWord ++ tailWord_1994898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994898).length < 2 ^ (prefixWord ++ tailWord_1994898).sum := by decide
  have hdescent : baseEnd_1994898 < baseStart_1994898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994912 : List Nat := [2, 1, 1, 4, 2, 2, 1, 5, 1, 1, 3]
def baseStart_1994912 : Nat := 118140960795 + 1994912 * 2 ^ 59
def prefixEnd_1994912 : Nat := 4983230072969 + 3 ^ 40 * 1994912 * 2
def baseEnd_1994912 : Nat := 1024348719422204131325573

theorem tailTrace_1994912 : CollatzResearch.WordTrace tailWord_1994912 prefixEnd_1994912 1024348719422204131325573 := by
  unfold tailWord_1994912
  simp only [CollatzResearch.WordTrace]
  refine ⟨36380209074391001344945495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48506945432521335126593993 36380209074391001344945495)
  ·
    refine ⟨54570313611586502017418243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36380209074391001344945495 54570313611586502017418243)
    ·
      refine ⟨81855470417379753026127365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54570313611586502017418243 81855470417379753026127365)
      ·
        refine ⟨15347900703258703692398881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81855470417379753026127365 15347900703258703692398881)
        ·
          refine ⟨11510925527444027769299161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15347900703258703692398881 11510925527444027769299161)
          ·
            refine ⟨8633194145583020826974371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11510925527444027769299161 8633194145583020826974371)
            ·
              refine ⟨12949791218374531240461557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8633194145583020826974371 12949791218374531240461557)
              ·
                refine ⟨1214042926722612303793271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12949791218374531240461557 1214042926722612303793271)
                ·
                  refine ⟨1821064390083918455689907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1214042926722612303793271 1821064390083918455689907)
                  ·
                    refine ⟨2731596585125877683534861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1821064390083918455689907 2731596585125877683534861)
                    ·
                      refine ⟨1024348719422204131325573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2731596585125877683534861 1024348719422204131325573)
                      ·
                        rfl

theorem cell23_1994912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_1994912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994912 prefixEnd_1994912 := by exact prefixLift 1994912
  have htrace : WordTrace (prefixWord ++ tailWord_1994912) baseStart_1994912 baseEnd_1994912 := by
    simpa [prefixWord, tailWord_1994912, baseEnd_1994912] using wordTrace_append hprefix tailTrace_1994912
  have hstable : (prefixWord ++ tailWord_1994912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994912).length < 2 ^ (prefixWord ++ tailWord_1994912).sum := by decide
  have hdescent : baseEnd_1994912 < baseStart_1994912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994931 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 6]
def baseStart_1994931 : Nat := 118140960795 + 1994931 * 2 ^ 59
def prefixEnd_1994931 : Nat := 4983230072969 + 3 ^ 40 * 1994931 * 2
def baseEnd_1994931 : Nat := 1024358475554639556987985

theorem tailTrace_1994931 : CollatzResearch.WordTrace tailWord_1994931 prefixEnd_1994931 1024358475554639556987985 := by
  unfold tailWord_1994931
  simp only [CollatzResearch.WordTrace]
  refine ⟨72761111135713168934832647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48507407423808779289888431 72761111135713168934832647)
  ·
    refine ⟨109141666703569753402248971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72761111135713168934832647 109141666703569753402248971)
    ·
      refine ⟨163712500055354630103373457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109141666703569753402248971 163712500055354630103373457)
      ·
        refine ⟨122784375041515972577530093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163712500055354630103373457 122784375041515972577530093)
        ·
          refine ⟨46044140640568489716573785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122784375041515972577530093 46044140640568489716573785)
          ·
            refine ⟨34533105480426367287430339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46044140640568489716573785 34533105480426367287430339)
            ·
              refine ⟨51799658220639550931145509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34533105480426367287430339 51799658220639550931145509)
              ·
                refine ⟨9712435916369915799589783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51799658220639550931145509 9712435916369915799589783)
                ·
                  refine ⟨14568653874554873699384675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9712435916369915799589783 14568653874554873699384675)
                  ·
                    refine ⟨21852980811832310549077013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14568653874554873699384675 21852980811832310549077013)
                    ·
                      refine ⟨1024358475554639556987985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21852980811832310549077013 1024358475554639556987985)
                      ·
                        rfl

theorem cell23_1994931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_1994931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994931 prefixEnd_1994931 := by exact prefixLift 1994931
  have htrace : WordTrace (prefixWord ++ tailWord_1994931) baseStart_1994931 baseEnd_1994931 := by
    simpa [prefixWord, tailWord_1994931, baseEnd_1994931] using wordTrace_append hprefix tailTrace_1994931
  have hstable : (prefixWord ++ tailWord_1994931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994931).length < 2 ^ (prefixWord ++ tailWord_1994931).sum := by decide
  have hdescent : baseEnd_1994931 < baseStart_1994931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994938 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3]
def baseStart_1994938 : Nat := 118140960795 + 1994938 * 2 ^ 59
def prefixEnd_1994938 : Nat := 4983230072969 + 3 ^ 40 * 1994938 * 2
def baseEnd_1994938 : Nat := 1024362069919221029600453

theorem tailTrace_1994938 : CollatzResearch.WordTrace tailWord_1994938 prefixEnd_1994938 1024362069919221029600453 := by
  unfold tailWord_1994938
  simp only [CollatzResearch.WordTrace]
  refine ⟨18190341611671952282584367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48507577631125206086891645 18190341611671952282584367)
  ·
    refine ⟨27285512417507928423876551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18190341611671952282584367 27285512417507928423876551)
    ·
      refine ⟨40928268626261892635814827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27285512417507928423876551 40928268626261892635814827)
      ·
        refine ⟨61392402939392838953722241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40928268626261892635814827 61392402939392838953722241)
        ·
          refine ⟨46044302204544629215291681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61392402939392838953722241 46044302204544629215291681)
          ·
            refine ⟨34533226653408471911468761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46044302204544629215291681 34533226653408471911468761)
            ·
              refine ⟨25899919990056353933601571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34533226653408471911468761 25899919990056353933601571)
              ·
                refine ⟨38849879985084530900402357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25899919990056353933601571 38849879985084530900402357)
                ·
                  refine ⟨3642176248601674771912721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38849879985084530900402357 3642176248601674771912721)
                  ·
                    refine ⟨2731632186451256078934541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3642176248601674771912721 2731632186451256078934541)
                    ·
                      refine ⟨1024362069919221029600453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2731632186451256078934541 1024362069919221029600453)
                      ·
                        rfl

theorem cell23_1994938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_1994938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994938 prefixEnd_1994938 := by exact prefixLift 1994938
  have htrace : WordTrace (prefixWord ++ tailWord_1994938) baseStart_1994938 baseEnd_1994938 := by
    simpa [prefixWord, tailWord_1994938, baseEnd_1994938] using wordTrace_append hprefix tailTrace_1994938
  have hstable : (prefixWord ++ tailWord_1994938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994938).length < 2 ^ (prefixWord ++ tailWord_1994938).sum := by decide
  have hdescent : baseEnd_1994938 < baseStart_1994938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994941 : List Nat := [1, 4, 1, 2, 1, 1, 1, 12]
def baseStart_1994941 : Nat := 118140960795 + 1994941 * 2 ^ 59
def prefixEnd_1994941 : Nat := 4983230072969 + 3 ^ 40 * 1994941 * 2
def baseEnd_1994941 : Nat := 37939392976340167328257

theorem tailTrace_1994941 : CollatzResearch.WordTrace tailWord_1994941 prefixEnd_1994941 37939392976340167328257 := by
  unfold tailWord_1994941
  simp only [CollatzResearch.WordTrace]
  refine ⟨72761475865676940642696677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48507650577117960428464451 72761475865676940642696677)
  ·
    refine ⟨13642776724814426370505627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72761475865676940642696677 13642776724814426370505627)
    ·
      refine ⟨20464165087221639555758441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13642776724814426370505627 20464165087221639555758441)
      ·
        refine ⟨15348123815416229666818831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20464165087221639555758441 15348123815416229666818831)
        ·
          refine ⟨23022185723124344500228247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15348123815416229666818831 23022185723124344500228247)
          ·
            refine ⟨34533278584686516750342371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23022185723124344500228247 34533278584686516750342371)
            ·
              refine ⟨51799917877029775125513557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34533278584686516750342371 51799917877029775125513557)
              ·
                refine ⟨37939392976340167328257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 51799917877029775125513557 37939392976340167328257)
                ·
                  rfl

theorem cell23_1994941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 12].length) (baseStart_1994941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994941 prefixEnd_1994941 := by exact prefixLift 1994941
  have htrace : WordTrace (prefixWord ++ tailWord_1994941) baseStart_1994941 baseEnd_1994941 := by
    simpa [prefixWord, tailWord_1994941, baseEnd_1994941] using wordTrace_append hprefix tailTrace_1994941
  have hstable : (prefixWord ++ tailWord_1994941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994941).length < 2 ^ (prefixWord ++ tailWord_1994941).sum := by decide
  have hdescent : baseEnd_1994941 < baseStart_1994941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994955 : List Nat := [1, 1, 1, 1, 3, 2, 6, 2, 1, 2, 3]
def baseStart_1994955 : Nat := 118140960795 + 1994955 * 2 ^ 59
def prefixEnd_1994955 : Nat := 4983230072969 + 3 ^ 40 * 1994955 * 2
def baseEnd_1994955 : Nat := 1024370799090347463087875

theorem tailTrace_1994955 : CollatzResearch.WordTrace tailWord_1994955 prefixEnd_1994955 1024370799090347463087875 := by
  unfold tailWord_1994955
  simp only [CollatzResearch.WordTrace]
  refine ⟨72761986487626221033706319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48507990991750814022470879 72761986487626221033706319)
  ·
    refine ⟨109142979731439331550559479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72761986487626221033706319 109142979731439331550559479)
    ·
      refine ⟨163714469597158997325839219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109142979731439331550559479 163714469597158997325839219)
      ·
        refine ⟨245571704395738495988758829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163714469597158997325839219 245571704395738495988758829)
        ·
          refine ⟨92089389148401935995784561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245571704395738495988758829 92089389148401935995784561)
          ·
            refine ⟨69067041861301451996838421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92089389148401935995784561 69067041861301451996838421)
            ·
              refine ⟨3237517587248505562351801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69067041861301451996838421 3237517587248505562351801)
              ·
                refine ⟨2428138190436379171763851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3237517587248505562351801 2428138190436379171763851)
                ·
                  refine ⟨3642207285654568757645777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2428138190436379171763851 3642207285654568757645777)
                  ·
                    refine ⟨2731655464240926568234333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3642207285654568757645777 2731655464240926568234333)
                    ·
                      refine ⟨1024370799090347463087875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2731655464240926568234333 1024370799090347463087875)
                      ·
                        rfl

theorem cell23_1994955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 2, 3].length) (baseStart_1994955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994955 prefixEnd_1994955 := by exact prefixLift 1994955
  have htrace : WordTrace (prefixWord ++ tailWord_1994955) baseStart_1994955 baseEnd_1994955 := by
    simpa [prefixWord, tailWord_1994955, baseEnd_1994955] using wordTrace_append hprefix tailTrace_1994955
  have hstable : (prefixWord ++ tailWord_1994955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994955).length < 2 ^ (prefixWord ++ tailWord_1994955).sum := by decide
  have hdescent : baseEnd_1994955 < baseStart_1994955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994958 : List Nat := [4, 1, 1, 1, 4, 2, 1, 9]
def baseStart_1994958 : Nat := 118140960795 + 1994958 * 2 ^ 59
def prefixEnd_1994958 : Nat := 4983230072969 + 3 ^ 40 * 1994958 * 2
def baseEnd_1994958 : Nat := 37939716278974479679643

theorem tailTrace_1994958 : CollatzResearch.WordTrace tailWord_1994958 prefixEnd_1994958 37939716278974479679643 := by
  unfold tailWord_1994958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9095261988326919068258191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48508063937743568364043685 9095261988326919068258191)
  ·
    refine ⟨13642892982490378602387287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9095261988326919068258191 13642892982490378602387287)
    ·
      refine ⟨20464339473735567903580931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13642892982490378602387287 20464339473735567903580931)
      ·
        refine ⟨30696509210603351855371397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20464339473735567903580931 30696509210603351855371397)
        ·
          refine ⟨5755595476988128472882137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30696509210603351855371397 5755595476988128472882137)
          ·
            refine ⟨4316696607741096354661603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5755595476988128472882137 4316696607741096354661603)
            ·
              refine ⟨6475044911611644531992405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316696607741096354661603 6475044911611644531992405)
              ·
                refine ⟨37939716278974479679643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6475044911611644531992405 37939716278974479679643)
                ·
                  rfl

theorem cell23_1994958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_1994958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994958 prefixEnd_1994958 := by exact prefixLift 1994958
  have htrace : WordTrace (prefixWord ++ tailWord_1994958) baseStart_1994958 baseEnd_1994958 := by
    simpa [prefixWord, tailWord_1994958, baseEnd_1994958] using wordTrace_append hprefix tailTrace_1994958
  have hstable : (prefixWord ++ tailWord_1994958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994958).length < 2 ^ (prefixWord ++ tailWord_1994958).sum := by decide
  have hdescent : baseEnd_1994958 < baseStart_1994958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994969 : List Nat := [1, 2, 1, 2, 3, 1, 5, 3, 1, 2, 2]
def baseStart_1994969 : Nat := 118140960795 + 1994969 * 2 ^ 59
def prefixEnd_1994969 : Nat := 4983230072969 + 3 ^ 40 * 1994969 * 2
def baseEnd_1994969 : Nat := 1024377987819510408312811

theorem tailTrace_1994969 : CollatzResearch.WordTrace tailWord_1994969 prefixEnd_1994969 1024377987819510408312811 := by
  unfold tailWord_1994969
  simp only [CollatzResearch.WordTrace]
  refine ⟨72762497109575501424715961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48508331406383667616477307 72762497109575501424715961)
  ·
    refine ⟨54571872832181626068536971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72762497109575501424715961 54571872832181626068536971)
    ·
      refine ⟨81857809248272439102805457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54571872832181626068536971 81857809248272439102805457)
      ·
        refine ⟨61393356936204329327104093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81857809248272439102805457 61393356936204329327104093)
        ·
          refine ⟨23022508851076623497664035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61393356936204329327104093 23022508851076623497664035)
          ·
            refine ⟨34533763276614935246496053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23022508851076623497664035 34533763276614935246496053)
            ·
              refine ⟨3237540307182650179359005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34533763276614935246496053 3237540307182650179359005)
              ·
                refine ⟨1214077615193493817259627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3237540307182650179359005 1214077615193493817259627)
                ·
                  refine ⟨1821116422790240725889441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1214077615193493817259627 1821116422790240725889441)
                  ·
                    refine ⟨1365837317092680544417081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1821116422790240725889441 1365837317092680544417081)
                    ·
                      refine ⟨1024377987819510408312811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1365837317092680544417081 1024377987819510408312811)
                      ·
                        rfl

theorem cell23_1994969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 1, 2, 2].length) (baseStart_1994969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994969 prefixEnd_1994969 := by exact prefixLift 1994969
  have htrace : WordTrace (prefixWord ++ tailWord_1994969) baseStart_1994969 baseEnd_1994969 := by
    simpa [prefixWord, tailWord_1994969, baseEnd_1994969] using wordTrace_append hprefix tailTrace_1994969
  have hstable : (prefixWord ++ tailWord_1994969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994969).length < 2 ^ (prefixWord ++ tailWord_1994969).sum := by decide
  have hdescent : baseEnd_1994969 < baseStart_1994969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994986 : List Nat := [3, 1, 3, 1, 1, 2, 5, 2, 1, 2, 2]
def baseStart_1994986 : Nat := 118140960795 + 1994986 * 2 ^ 59
def prefixEnd_1994986 : Nat := 4983230072969 + 3 ^ 40 * 1994986 * 2
def baseEnd_1994986 : Nat := 1024386716990636841800233

theorem tailTrace_1994986 : CollatzResearch.WordTrace tailWord_1994986 prefixEnd_1994986 1024386716990636841800233 := by
  unfold tailWord_1994986
  simp only [CollatzResearch.WordTrace]
  refine ⟨18190779287628478332021203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48508744767009275552056541 18190779287628478332021203)
  ·
    refine ⟨27286168931442717498031805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18190779287628478332021203 27286168931442717498031805)
    ·
      refine ⟨10232313349291019061761927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27286168931442717498031805 10232313349291019061761927)
      ·
        refine ⟨15348470023936528592642891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10232313349291019061761927 15348470023936528592642891)
        ·
          refine ⟨23022705035904792888964337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15348470023936528592642891 23022705035904792888964337)
          ·
            refine ⟨17267028776928594666723253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23022705035904792888964337 17267028776928594666723253)
            ·
              refine ⟨1618783947837055750005305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17267028776928594666723253 1618783947837055750005305)
              ·
                refine ⟨1214087960877791812503979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1618783947837055750005305 1214087960877791812503979)
                ·
                  refine ⟨1821131941316687718755969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1214087960877791812503979 1821131941316687718755969)
                  ·
                    refine ⟨1365848955987515789066977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1821131941316687718755969 1365848955987515789066977)
                    ·
                      refine ⟨1024386716990636841800233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1365848955987515789066977 1024386716990636841800233)
                      ·
                        rfl

theorem cell23_1994986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_1994986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994986 prefixEnd_1994986 := by exact prefixLift 1994986
  have htrace : WordTrace (prefixWord ++ tailWord_1994986) baseStart_1994986 baseEnd_1994986 := by
    simpa [prefixWord, tailWord_1994986, baseEnd_1994986] using wordTrace_append hprefix tailTrace_1994986
  have hstable : (prefixWord ++ tailWord_1994986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994986).length < 2 ^ (prefixWord ++ tailWord_1994986).sum := by decide
  have hdescent : baseEnd_1994986 < baseStart_1994986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994995 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 3, 3, 2]
def baseStart_1994995 : Nat := 118140960795 + 1994995 * 2 ^ 59
def prefixEnd_1994995 : Nat := 4983230072969 + 3 ^ 40 * 1994995 * 2
def baseEnd_1994995 : Nat := 1024391338316527306587691

theorem tailTrace_1994995 : CollatzResearch.WordTrace tailWord_1994995 prefixEnd_1994995 1024391338316527306587691 := by
  unfold tailWord_1994995
  simp only [CollatzResearch.WordTrace]
  refine ⟨72763445407481307865162439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48508963604987538576774959 72763445407481307865162439)
  ·
    refine ⟨109145168111221961797743659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72763445407481307865162439 109145168111221961797743659)
    ·
      refine ⟨163717752166832942696615489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109145168111221961797743659 163717752166832942696615489)
      ·
        refine ⟨122788314125124707022461617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163717752166832942696615489 122788314125124707022461617)
        ·
          refine ⟨92091235593843530266846213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122788314125124707022461617 92091235593843530266846213)
          ·
            refine ⟨17267106673845661925033665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92091235593843530266846213 17267106673845661925033665)
            ·
              refine ⟨12950330005384246443775249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17267106673845661925033665 12950330005384246443775249)
              ·
                refine ⟨9712747504038184832831437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12950330005384246443775249 9712747504038184832831437)
                ·
                  refine ⟨3642280314014319312311789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9712747504038184832831437 3642280314014319312311789)
                  ·
                    refine ⟨1365855117755369742116921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3642280314014319312311789 1365855117755369742116921)
                    ·
                      refine ⟨1024391338316527306587691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1365855117755369742116921 1024391338316527306587691)
                      ·
                        rfl

theorem cell23_1994995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 3, 2].length) (baseStart_1994995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1994995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1994995 prefixEnd_1994995 := by exact prefixLift 1994995
  have htrace : WordTrace (prefixWord ++ tailWord_1994995) baseStart_1994995 baseEnd_1994995 := by
    simpa [prefixWord, tailWord_1994995, baseEnd_1994995] using wordTrace_append hprefix tailTrace_1994995
  have hstable : (prefixWord ++ tailWord_1994995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994995).length < 2 ^ (prefixWord ++ tailWord_1994995).sum := by decide
  have hdescent : baseEnd_1994995 < baseStart_1994995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995002 : List Nat := [3, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3]
def baseStart_1995002 : Nat := 118140960795 + 1995002 * 2 ^ 59
def prefixEnd_1995002 : Nat := 4983230072969 + 3 ^ 40 * 1995002 * 2
def baseEnd_1995002 : Nat := 1024394932681108779200159

theorem tailTrace_1995002 : CollatzResearch.WordTrace tailWord_1995002 prefixEnd_1995002 1024394932681108779200159 := by
  unfold tailWord_1995002
  simp only [CollatzResearch.WordTrace]
  refine ⟨18190925179613987015166815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48509133812303965373778173 18190925179613987015166815)
  ·
    refine ⟨27286387769420980522750223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18190925179613987015166815 27286387769420980522750223)
    ·
      refine ⟨40929581654131470784125335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27286387769420980522750223 40929581654131470784125335)
      ·
        refine ⟨61394372481197206176188003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40929581654131470784125335 61394372481197206176188003)
        ·
          refine ⟨92091558721795809264282005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61394372481197206176188003 92091558721795809264282005)
          ·
            refine ⟨4316791815084178559263219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92091558721795809264282005 4316791815084178559263219)
            ·
              refine ⟨6475187722626267838894829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316791815084178559263219 6475187722626267838894829)
              ·
                refine ⟨2428195395984850439585561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6475187722626267838894829 2428195395984850439585561)
                ·
                  refine ⟨1821146546988637829689171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2428195395984850439585561 1821146546988637829689171)
                  ·
                    refine ⟨2731719820482956744533757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1821146546988637829689171 2731719820482956744533757)
                    ·
                      refine ⟨1024394932681108779200159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2731719820482956744533757 1024394932681108779200159)
                      ·
                        rfl

theorem cell23_1995002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_1995002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995002 prefixEnd_1995002 := by exact prefixLift 1995002
  have htrace : WordTrace (prefixWord ++ tailWord_1995002) baseStart_1995002 baseEnd_1995002 := by
    simpa [prefixWord, tailWord_1995002, baseEnd_1995002] using wordTrace_append hprefix tailTrace_1995002
  have hstable : (prefixWord ++ tailWord_1995002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995002).length < 2 ^ (prefixWord ++ tailWord_1995002).sum := by decide
  have hdescent : baseEnd_1995002 < baseStart_1995002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995025 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 3, 4, 2]
def baseStart_1995025 : Nat := 118140960795 + 1995025 * 2 ^ 59
def prefixEnd_1995025 : Nat := 4983230072969 + 3 ^ 40 * 1995025 * 2
def baseEnd_1995025 : Nat := 1024406742736162189212553

theorem tailTrace_1995025 : CollatzResearch.WordTrace tailWord_1995025 prefixEnd_1995025 1024406742736162189212553 := by
  unfold tailWord_1995025
  simp only [CollatzResearch.WordTrace]
  refine ⟨72764539597372622988754529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48509693064915081992503019 72764539597372622988754529)
  ·
    refine ⟨54573404698029467241565897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72764539597372622988754529 54573404698029467241565897)
    ·
      refine ⟨40930053523522100431174423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54573404698029467241565897 40930053523522100431174423)
      ·
        refine ⟨61395080285283150646761635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40930053523522100431174423 61395080285283150646761635)
        ·
          refine ⟨92092620427924725970142453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61395080285283150646761635 92092620427924725970142453)
          ·
            refine ⟨8633683165117943059700855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92092620427924725970142453 8633683165117943059700855)
            ·
              refine ⟨12950524747676914589551283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8633683165117943059700855 12950524747676914589551283)
              ·
                refine ⟨19425787121515371884326925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12950524747676914589551283 19425787121515371884326925)
                ·
                  refine ⟨7284670170568264456622597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19425787121515371884326925 7284670170568264456622597)
                  ·
                    refine ⟨1365875656981549585616737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7284670170568264456622597 1365875656981549585616737)
                    ·
                      refine ⟨1024406742736162189212553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1365875656981549585616737 1024406742736162189212553)
                      ·
                        rfl

theorem cell23_1995025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 4, 2].length) (baseStart_1995025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995025 prefixEnd_1995025 := by exact prefixLift 1995025
  have htrace : WordTrace (prefixWord ++ tailWord_1995025) baseStart_1995025 baseEnd_1995025 := by
    simpa [prefixWord, tailWord_1995025, baseEnd_1995025] using wordTrace_append hprefix tailTrace_1995025
  have hstable : (prefixWord ++ tailWord_1995025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995025).length < 2 ^ (prefixWord ++ tailWord_1995025).sum := by decide
  have hdescent : baseEnd_1995025 < baseStart_1995025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995065 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 7]
def baseStart_1995065 : Nat := 118140960795 + 1995065 * 2 ^ 59
def prefixEnd_1995065 : Nat := 4983230072969 + 3 ^ 40 * 1995065 * 2
def baseEnd_1995065 : Nat := 113825253551371336968041

theorem tailTrace_1995065 : CollatzResearch.WordTrace tailWord_1995065 prefixEnd_1995065 113825253551371336968041 := by
  unfold tailWord_1995065
  simp only [CollatzResearch.WordTrace]
  refine ⟨72765998517227709820210649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48510665678151806546807099 72765998517227709820210649)
  ·
    refine ⟨54574498887920782365157987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72765998517227709820210649 54574498887920782365157987)
    ·
      refine ⟨81861748331881173547736981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54574498887920782365157987 81861748331881173547736981)
      ·
        refine ⟨3837269453056930010050171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81861748331881173547736981 3837269453056930010050171)
        ·
          refine ⟨5755904179585395015075257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3837269453056930010050171 5755904179585395015075257)
          ·
            refine ⟨4316928134689046261306443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5755904179585395015075257 4316928134689046261306443)
            ·
              refine ⟨6475392202033569391959665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316928134689046261306443 6475392202033569391959665)
              ·
                refine ⟨4856544151525177043969749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6475392202033569391959665 4856544151525177043969749)
                ·
                  refine ⟨113825253551371336968041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4856544151525177043969749 113825253551371336968041)
                  ·
                    rfl

theorem cell23_1995065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 7].length) (baseStart_1995065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995065 prefixEnd_1995065 := by exact prefixLift 1995065
  have htrace : WordTrace (prefixWord ++ tailWord_1995065) baseStart_1995065 baseEnd_1995065 := by
    simpa [prefixWord, tailWord_1995065, baseEnd_1995065] using wordTrace_append hprefix tailTrace_1995065
  have hstable : (prefixWord ++ tailWord_1995065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995065).length < 2 ^ (prefixWord ++ tailWord_1995065).sum := by decide
  have hdescent : baseEnd_1995065 < baseStart_1995065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995093 : List Nat := [1, 3, 2, 2, 5, 1, 1, 2, 2, 2, 2]
def baseStart_1995093 : Nat := 118140960795 + 1995093 * 2 ^ 59
def prefixEnd_1995093 : Nat := 4983230072969 + 3 ^ 40 * 1995093 * 2
def baseEnd_1995093 : Nat := 1024441659420667923162241

theorem tailTrace_1995093 : CollatzResearch.WordTrace tailWord_1995093 prefixEnd_1995093 1024441659420667923162241 := by
  unfold tailWord_1995093
  simp only [CollatzResearch.WordTrace]
  refine ⟨72767019761126270602229933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48511346507417513734819955 72767019761126270602229933)
  ·
    refine ⟨27287632410422351475836225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72767019761126270602229933 27287632410422351475836225)
    ·
      refine ⟨20465724307816763606877169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27287632410422351475836225 20465724307816763606877169)
      ·
        refine ⟨15349293230862572705157877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20465724307816763606877169 15349293230862572705157877)
        ·
          refine ⟨1438996240393366191108551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15349293230862572705157877 1438996240393366191108551)
          ·
            refine ⟨2158494360590049286662827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438996240393366191108551 2158494360590049286662827)
            ·
              refine ⟨3237741540885073929994241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158494360590049286662827 3237741540885073929994241)
              ·
                refine ⟨2428306155663805447495681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3237741540885073929994241 2428306155663805447495681)
                ·
                  refine ⟨1821229616747854085621761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2428306155663805447495681 1821229616747854085621761)
                  ·
                    refine ⟨1365922212560890564216321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1821229616747854085621761 1365922212560890564216321)
                    ·
                      refine ⟨1024441659420667923162241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1365922212560890564216321 1024441659420667923162241)
                      ·
                        rfl

theorem cell23_1995093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_1995093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995093 prefixEnd_1995093 := by exact prefixLift 1995093
  have htrace : WordTrace (prefixWord ++ tailWord_1995093) baseStart_1995093 baseEnd_1995093 := by
    simpa [prefixWord, tailWord_1995093, baseEnd_1995093] using wordTrace_append hprefix tailTrace_1995093
  have hstable : (prefixWord ++ tailWord_1995093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995093).length < 2 ^ (prefixWord ++ tailWord_1995093).sum := by decide
  have hdescent : baseEnd_1995093 < baseStart_1995093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995172 : List Nat := [2, 3, 1, 2, 1, 1, 6, 1, 6]
def baseStart_1995172 : Nat := 118140960795 + 1995172 * 2 ^ 59
def prefixEnd_1995172 : Nat := 4983230072969 + 3 ^ 40 * 1995172 * 2
def baseEnd_1995172 : Nat := 113831358265819234897153

theorem tailTrace_1995172 : CollatzResearch.WordTrace tailWord_1995172 prefixEnd_1995172 113831358265819234897153 := by
  unfold tailWord_1995172
  simp only [CollatzResearch.WordTrace]
  refine ⟨36384950563920033547177885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48513267418560044729570513 36384950563920033547177885)
  ·
    refine ⟨13644356461470012580191707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36384950563920033547177885 13644356461470012580191707)
    ·
      refine ⟨20466534692205018870287561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13644356461470012580191707 20466534692205018870287561)
      ·
        refine ⟨15349901019153764152715671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20466534692205018870287561 15349901019153764152715671)
        ·
          refine ⟨23024851528730646229073507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15349901019153764152715671 23024851528730646229073507)
          ·
            refine ⟨34537277293095969343610261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23024851528730646229073507 34537277293095969343610261)
            ·
              refine ⟨1618934873113873562981731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34537277293095969343610261 1618934873113873562981731)
              ·
                refine ⟨2428402309670810344472597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618934873113873562981731 2428402309670810344472597)
                ·
                  refine ⟨113831358265819234897153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2428402309670810344472597 113831358265819234897153)
                  ·
                    rfl

theorem cell23_1995172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_1995172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995172 prefixEnd_1995172 := by exact prefixLift 1995172
  have htrace : WordTrace (prefixWord ++ tailWord_1995172) baseStart_1995172 baseEnd_1995172 := by
    simpa [prefixWord, tailWord_1995172, baseEnd_1995172] using wordTrace_append hprefix tailTrace_1995172
  have hstable : (prefixWord ++ tailWord_1995172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995172).length < 2 ^ (prefixWord ++ tailWord_1995172).sum := by decide
  have hdescent : baseEnd_1995172 < baseStart_1995172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995225 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 3, 1, 5]
def baseStart_1995225 : Nat := 118140960795 + 1995225 * 2 ^ 59
def prefixEnd_1995225 : Nat := 4983230072969 + 3 ^ 40 * 1995225 * 2
def baseEnd_1995225 : Nat := 1024509438867061406711633

theorem tailTrace_1995225 : CollatzResearch.WordTrace tailWord_1995225 prefixEnd_1995225 1024509438867061406711633 := by
  unfold tailWord_1995225
  simp only [CollatzResearch.WordTrace]
  refine ⟨72771834196648057146035129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48514556131098704764023419 72771834196648057146035129)
  ·
    refine ⟨54578875647486042859526347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72771834196648057146035129 54578875647486042859526347)
    ·
      refine ⟨81868313471229064289289521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54578875647486042859526347 81868313471229064289289521)
      ·
        refine ⟨61401235103421798216967141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81868313471229064289289521 61401235103421798216967141)
        ·
          refine ⟨11512731581891587165681339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61401235103421798216967141 11512731581891587165681339)
          ·
            refine ⟨17269097372837380748522009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11512731581891587165681339 17269097372837380748522009)
            ·
              refine ⟨12951823029628035561391507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17269097372837380748522009 12951823029628035561391507)
              ·
                refine ⟨19427734544442053342087261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12951823029628035561391507 19427734544442053342087261)
                ·
                  refine ⟨7285400454165770003282723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19427734544442053342087261 7285400454165770003282723)
                  ·
                    refine ⟨10928100681248655004924085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7285400454165770003282723 10928100681248655004924085)
                    ·
                      refine ⟨1024509438867061406711633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10928100681248655004924085 1024509438867061406711633)
                      ·
                        rfl

theorem cell23_1995225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_1995225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995225 prefixEnd_1995225 := by exact prefixLift 1995225
  have htrace : WordTrace (prefixWord ++ tailWord_1995225) baseStart_1995225 baseEnd_1995225 := by
    simpa [prefixWord, tailWord_1995225, baseEnd_1995225] using wordTrace_append hprefix tailTrace_1995225
  have hstable : (prefixWord ++ tailWord_1995225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995225).length < 2 ^ (prefixWord ++ tailWord_1995225).sum := by decide
  have hdescent : baseEnd_1995225 < baseStart_1995225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995232 : List Nat := [2, 1, 1, 3, 1, 1, 3, 5, 2, 4]
def baseStart_1995232 : Nat := 118140960795 + 1995232 * 2 ^ 59
def prefixEnd_1995232 : Nat := 4983230072969 + 3 ^ 40 * 1995232 * 2
def baseEnd_1995232 : Nat := 341504344410547626441367

theorem tailTrace_1995232 : CollatzResearch.WordTrace tailWord_1995232 prefixEnd_1995232 341504344410547626441367 := by
  unfold tailWord_1995232
  simp only [CollatzResearch.WordTrace]
  refine ⟨36386044753811348670769975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48514726338415131561026633 36386044753811348670769975)
  ·
    refine ⟨54579067130717023006154963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36386044753811348670769975 54579067130717023006154963)
    ·
      refine ⟨81868600696075534509232445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54579067130717023006154963 81868600696075534509232445)
      ·
        refine ⟨30700725261028325440962167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81868600696075534509232445 30700725261028325440962167)
        ·
          refine ⟨46051087891542488161443251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30700725261028325440962167 46051087891542488161443251)
          ·
            refine ⟨69076631837313732242164877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46051087891542488161443251 69076631837313732242164877)
            ·
              refine ⟨25903736938992649590811829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69076631837313732242164877 25903736938992649590811829)
              ·
                refine ⟨2428475338030560899138609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25903736938992649590811829 2428475338030560899138609)
                ·
                  refine ⟨1821356503522920674353957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2428475338030560899138609 1821356503522920674353957)
                  ·
                    refine ⟨341504344410547626441367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1821356503522920674353957 341504344410547626441367)
                    ·
                      rfl

theorem cell23_1995232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 2, 4].length) (baseStart_1995232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995232 prefixEnd_1995232 := by exact prefixLift 1995232
  have htrace : WordTrace (prefixWord ++ tailWord_1995232) baseStart_1995232 baseEnd_1995232 := by
    simpa [prefixWord, tailWord_1995232, baseEnd_1995232] using wordTrace_append hprefix tailTrace_1995232
  have hstable : (prefixWord ++ tailWord_1995232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995232).length < 2 ^ (prefixWord ++ tailWord_1995232).sum := by decide
  have hdescent : baseEnd_1995232 < baseStart_1995232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995253 : List Nat := [1, 3, 5, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1995253 : Nat := 118140960795 + 1995253 * 2 ^ 59
def prefixEnd_1995253 : Nat := 4983230072969 + 3 ^ 40 * 1995253 * 2
def baseEnd_1995253 : Nat := 341507938775129099053835

theorem tailTrace_1995253 : CollatzResearch.WordTrace tailWord_1995253 prefixEnd_1995253 341507938775129099053835 := by
  unfold tailWord_1995253
  simp only [CollatzResearch.WordTrace]
  refine ⟨72772855440546617928054413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48515236960364411952036275 72772855440546617928054413)
  ·
    refine ⟨27289820790204981723020405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72772855440546617928054413 27289820790204981723020405)
    ·
      refine ⟨2558420699081717036533163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27289820790204981723020405 2558420699081717036533163)
      ·
        refine ⟨3837631048622575554799745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2558420699081717036533163 3837631048622575554799745)
        ·
          refine ⟨2878223286466931666099809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3837631048622575554799745 2878223286466931666099809)
          ·
            refine ⟨2158667464850198749574857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2878223286466931666099809 2158667464850198749574857)
            ·
              refine ⟨1619000598637649062181143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2158667464850198749574857 1619000598637649062181143)
              ·
                refine ⟨2428500897956473593271715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1619000598637649062181143 2428500897956473593271715)
                ·
                  refine ⟨3642751346934710389907573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2428500897956473593271715 3642751346934710389907573)
                  ·
                    refine ⟨341507938775129099053835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3642751346934710389907573 341507938775129099053835)
                    ·
                      rfl

theorem cell23_1995253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1995253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995253 prefixEnd_1995253 := by exact prefixLift 1995253
  have htrace : WordTrace (prefixWord ++ tailWord_1995253) baseStart_1995253 baseEnd_1995253 := by
    simpa [prefixWord, tailWord_1995253, baseEnd_1995253] using wordTrace_append hprefix tailTrace_1995253
  have hstable : (prefixWord ++ tailWord_1995253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995253).length < 2 ^ (prefixWord ++ tailWord_1995253).sum := by decide
  have hdescent : baseEnd_1995253 < baseStart_1995253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995255 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 3]
def baseStart_1995255 : Nat := 118140960795 + 1995255 * 2 ^ 59
def prefixEnd_1995255 : Nat := 4983230072969 + 3 ^ 40 * 1995255 * 2
def baseEnd_1995255 : Nat := 1024524843286696289336495

theorem tailTrace_1995255 : CollatzResearch.WordTrace tailWord_1995255 prefixEnd_1995255 1024524843286696289336495 := by
  unfold tailWord_1995255
  simp only [CollatzResearch.WordTrace]
  refine ⟨72772928386539372269627219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48515285591026248179751479 72772928386539372269627219)
  ·
    refine ⟨109159392579809058404440829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72772928386539372269627219 109159392579809058404440829)
    ·
      refine ⟨40934772217428396901665311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109159392579809058404440829 40934772217428396901665311)
      ·
        refine ⟨61402158326142595352497967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40934772217428396901665311 61402158326142595352497967)
        ·
          refine ⟨92103237489213893028746951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61402158326142595352497967 92103237489213893028746951)
          ·
            refine ⟨138154856233820839543120427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92103237489213893028746951 138154856233820839543120427)
            ·
              refine ⟨207232284350731259314680641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138154856233820839543120427 207232284350731259314680641)
              ·
                refine ⟨155424213263048444486010481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207232284350731259314680641 155424213263048444486010481)
                ·
                  refine ⟨116568159947286333364507861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155424213263048444486010481 116568159947286333364507861)
                  ·
                    refine ⟨2732066248764523438230653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 116568159947286333364507861 2732066248764523438230653)
                    ·
                      refine ⟨1024524843286696289336495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2732066248764523438230653 1024524843286696289336495)
                      ·
                        rfl

theorem cell23_1995255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_1995255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995255 prefixEnd_1995255 := by exact prefixLift 1995255
  have htrace : WordTrace (prefixWord ++ tailWord_1995255) baseStart_1995255 baseEnd_1995255 := by
    simpa [prefixWord, tailWord_1995255, baseEnd_1995255] using wordTrace_append hprefix tailTrace_1995255
  have hstable : (prefixWord ++ tailWord_1995255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995255).length < 2 ^ (prefixWord ++ tailWord_1995255).sum := by decide
  have hdescent : baseEnd_1995255 < baseStart_1995255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995266 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1995266 : Nat := 118140960795 + 1995266 * 2 ^ 59
def prefixEnd_1995266 : Nat := 4983230072969 + 3 ^ 40 * 1995266 * 2
def baseEnd_1995266 : Nat := 341510163857965248766315

theorem tailTrace_1995266 : CollatzResearch.WordTrace tailWord_1995266 prefixEnd_1995266 341510163857965248766315 := by
  unfold tailWord_1995266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18193332397374880287069413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48515553059666347432185101 18193332397374880287069413)
  ·
    refine ⟨3411249824507790053825515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18193332397374880287069413 3411249824507790053825515)
    ·
      refine ⟨5116874736761685080738273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3411249824507790053825515 5116874736761685080738273)
      ·
        refine ⟨3837656052571263810553705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5116874736761685080738273 3837656052571263810553705)
        ·
          refine ⟨2878242039428447857915279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3837656052571263810553705 2878242039428447857915279)
          ·
            refine ⟨4317363059142671786872919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2878242039428447857915279 4317363059142671786872919)
            ·
              refine ⟨6476044588714007680309379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4317363059142671786872919 6476044588714007680309379)
              ·
                refine ⟨9714066883071011520464069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6476044588714007680309379 9714066883071011520464069)
                ·
                  refine ⟨1821387540575814660087013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9714066883071011520464069 1821387540575814660087013)
                  ·
                    refine ⟨341510163857965248766315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1821387540575814660087013 341510163857965248766315)
                    ·
                      rfl

theorem cell23_1995266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1995266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995266 prefixEnd_1995266 := by exact prefixLift 1995266
  have htrace : WordTrace (prefixWord ++ tailWord_1995266) baseStart_1995266 baseEnd_1995266 := by
    simpa [prefixWord, tailWord_1995266, baseEnd_1995266] using wordTrace_append hprefix tailTrace_1995266
  have hstable : (prefixWord ++ tailWord_1995266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995266).length < 2 ^ (prefixWord ++ tailWord_1995266).sum := by decide
  have hdescent : baseEnd_1995266 < baseStart_1995266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995296 : List Nat := [2, 1, 1, 6, 3, 1, 2, 7]
def baseStart_1995296 : Nat := 118140960795 + 1995296 * 2 ^ 59
def prefixEnd_1995296 : Nat := 4983230072969 + 3 ^ 40 * 1995296 * 2
def baseEnd_1995296 : Nat := 37946144296056689960141

theorem tailTrace_1995296 : CollatzResearch.WordTrace tailWord_1995296 prefixEnd_1995296 37946144296056689960141 := by
  unfold tailWord_1995296
  simp only [CollatzResearch.WordTrace]
  refine ⟨36387211889695418135934871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48516282519593890847913161 36387211889695418135934871)
  ·
    refine ⟨54580817834543127203902307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36387211889695418135934871 54580817834543127203902307)
    ·
      refine ⟨81871226751814690805853461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54580817834543127203902307 81871226751814690805853461)
      ·
        refine ⟨3837713753991313631524381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81871226751814690805853461 3837713753991313631524381)
        ·
          refine ⟨1439142657746742611821643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3837713753991313631524381 1439142657746742611821643)
          ·
            refine ⟨2158713986620113917732465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439142657746742611821643 2158713986620113917732465)
            ·
              refine ⟨1619035489965085438299349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2158713986620113917732465 1619035489965085438299349)
              ·
                refine ⟨37946144296056689960141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1619035489965085438299349 37946144296056689960141)
                ·
                  rfl

theorem cell23_1995296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 7].length) (baseStart_1995296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995296 prefixEnd_1995296 := by exact prefixLift 1995296
  have htrace : WordTrace (prefixWord ++ tailWord_1995296) baseStart_1995296 baseEnd_1995296 := by
    simpa [prefixWord, tailWord_1995296, baseEnd_1995296] using wordTrace_append hprefix tailTrace_1995296
  have hstable : (prefixWord ++ tailWord_1995296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995296).length < 2 ^ (prefixWord ++ tailWord_1995296).sum := by decide
  have hdescent : baseEnd_1995296 < baseStart_1995296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995342 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_1995342 : Nat := 118140960795 + 1995342 * 2 ^ 59
def prefixEnd_1995342 : Nat := 4983230072969 + 3 ^ 40 * 1995342 * 2
def baseEnd_1995342 : Nat := 1024569516103637448948595

theorem tailTrace_1995342 : CollatzResearch.WordTrace tailWord_1995342 prefixEnd_1995342 1024569516103637448948595 := by
  unfold tailWord_1995342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9097012692153023266005535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48517401024816124085362853 9097012692153023266005535)
  ·
    refine ⟨13645519038229534899008303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9097012692153023266005535 13645519038229534899008303)
    ·
      refine ⟨20468278557344302348512455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13645519038229534899008303 20468278557344302348512455)
      ·
        refine ⟨30702417836016453522768683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20468278557344302348512455 30702417836016453522768683)
        ·
          refine ⟨46053626754024680284153025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30702417836016453522768683 46053626754024680284153025)
          ·
            refine ⟨34540220065518510213114769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46053626754024680284153025 34540220065518510213114769)
            ·
              refine ⟨25905165049138882659836077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34540220065518510213114769 25905165049138882659836077)
              ·
                refine ⟨9714436893427080997438529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25905165049138882659836077 9714436893427080997438529)
                ·
                  refine ⟨7285827670070310748078897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9714436893427080997438529 7285827670070310748078897)
                  ·
                    refine ⟨5464370752552733061059173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7285827670070310748078897 5464370752552733061059173)
                    ·
                      refine ⟨1024569516103637448948595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5464370752552733061059173 1024569516103637448948595)
                      ·
                        rfl

theorem cell23_1995342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_1995342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995342 prefixEnd_1995342 := by exact prefixLift 1995342
  have htrace : WordTrace (prefixWord ++ tailWord_1995342) baseStart_1995342 baseEnd_1995342 := by
    simpa [prefixWord, tailWord_1995342, baseEnd_1995342] using wordTrace_append hprefix tailTrace_1995342
  have hstable : (prefixWord ++ tailWord_1995342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995342).length < 2 ^ (prefixWord ++ tailWord_1995342).sum := by decide
  have hdescent : baseEnd_1995342 < baseStart_1995342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995392 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 5]
def baseStart_1995392 : Nat := 118140960795 + 1995392 * 2 ^ 59
def prefixEnd_1995392 : Nat := 4983230072969 + 3 ^ 40 * 1995392 * 2
def baseEnd_1995392 : Nat := 1024595190136362253323365

theorem tailTrace_1995392 : CollatzResearch.WordTrace tailWord_1995392 prefixEnd_1995392 1024595190136362253323365 := by
  unfold tailWord_1995392
  simp only [CollatzResearch.WordTrace]
  refine ⟨36388962593521522333682215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48518616791362029778242953 36388962593521522333682215)
  ·
    refine ⟨54583443890282283500523323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36388962593521522333682215 54583443890282283500523323)
    ·
      refine ⟨81875165835423425250784985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54583443890282283500523323 81875165835423425250784985)
      ·
        refine ⟨61406374376567568938088739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81875165835423425250784985 61406374376567568938088739)
        ·
          refine ⟨92109561564851353407133109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61406374376567568938088739 92109561564851353407133109)
          ·
            refine ⟨8635271396704814381918729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92109561564851353407133109 8635271396704814381918729)
            ·
              refine ⟨6476453547528610786439047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8635271396704814381918729 6476453547528610786439047)
              ·
                refine ⟨9714680321292916179658571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6476453547528610786439047 9714680321292916179658571)
                ·
                  refine ⟨14572020481939374269487857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9714680321292916179658571 14572020481939374269487857)
                  ·
                    refine ⟨10929015361454530702115893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14572020481939374269487857 10929015361454530702115893)
                    ·
                      refine ⟨1024595190136362253323365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10929015361454530702115893 1024595190136362253323365)
                      ·
                        rfl

theorem cell23_1995392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_1995392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995392 prefixEnd_1995392 := by exact prefixLift 1995392
  have htrace : WordTrace (prefixWord ++ tailWord_1995392) baseStart_1995392 baseEnd_1995392 := by
    simpa [prefixWord, tailWord_1995392, baseEnd_1995392] using wordTrace_append hprefix tailTrace_1995392
  have hstable : (prefixWord ++ tailWord_1995392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995392).length < 2 ^ (prefixWord ++ tailWord_1995392).sum := by decide
  have hdescent : baseEnd_1995392 < baseStart_1995392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995472 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 7, 5]
def baseStart_1995472 : Nat := 118140960795 + 1995472 * 2 ^ 59
def prefixEnd_1995472 : Nat := 4983230072969 + 3 ^ 40 * 1995472 * 2
def baseEnd_1995472 : Nat := 341545422862907313440999

theorem tailTrace_1995472 : CollatzResearch.WordTrace tailWord_1995472 prefixEnd_1995472 341545422862907313440999 := by
  unfold tailWord_1995472
  simp only [CollatzResearch.WordTrace]
  refine ⟨36390421513376609165138335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48520562017835478886851113 36390421513376609165138335)
  ·
    refine ⟨54585632270064913747707503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36390421513376609165138335 54585632270064913747707503)
    ·
      refine ⟨81878448405097370621561255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54585632270064913747707503 81878448405097370621561255)
      ·
        refine ⟨122817672607646055932341883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81878448405097370621561255 122817672607646055932341883)
        ·
          refine ⟨184226508911469083898512825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122817672607646055932341883 184226508911469083898512825)
          ·
            refine ⟨138169881683601812923884619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184226508911469083898512825 138169881683601812923884619)
            ·
              refine ⟨207254822525402719385826929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138169881683601812923884619 207254822525402719385826929)
              ·
                refine ⟨155441116894052039539370197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207254822525402719385826929 155441116894052039539370197)
                ·
                  refine ⟨3643151177204344676703989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 155441116894052039539370197 3643151177204344676703989)
                  ·
                    refine ⟨341545422862907313440999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3643151177204344676703989 341545422862907313440999)
                    ·
                      rfl

theorem cell23_1995472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 7, 5].length) (baseStart_1995472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995472 prefixEnd_1995472 := by exact prefixLift 1995472
  have htrace : WordTrace (prefixWord ++ tailWord_1995472) baseStart_1995472 baseEnd_1995472 := by
    simpa [prefixWord, tailWord_1995472, baseEnd_1995472] using wordTrace_append hprefix tailTrace_1995472
  have hstable : (prefixWord ++ tailWord_1995472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995472).length < 2 ^ (prefixWord ++ tailWord_1995472).sum := by decide
  have hdescent : baseEnd_1995472 < baseStart_1995472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995503 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 3, 1, 3]
def baseStart_1995503 : Nat := 118140960795 + 1995503 * 2 ^ 59
def prefixEnd_1995503 : Nat := 4983230072969 + 3 ^ 40 * 1995503 * 2
def baseEnd_1995503 : Nat := 1024652186489011319035355

theorem tailTrace_1995503 : CollatzResearch.WordTrace tailWord_1995503 prefixEnd_1995503 1024652186489011319035355 := by
  unfold tailWord_1995503
  simp only [CollatzResearch.WordTrace]
  refine ⟨72781973689640910624655163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48521315793093940416436775 72781973689640910624655163)
  ·
    refine ⟨109172960534461365936982745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72781973689640910624655163 109172960534461365936982745)
    ·
      refine ⟨81879720400846024452737059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109172960534461365936982745 81879720400846024452737059)
      ·
        refine ⟨122819580601269036679105589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81879720400846024452737059 122819580601269036679105589)
        ·
          refine ⟨11514335681368972188666149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122819580601269036679105589 11514335681368972188666149)
          ·
            refine ⟨2158937940256682285374903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11514335681368972188666149 2158937940256682285374903)
            ·
              refine ⟨3238406910385023428062355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158937940256682285374903 3238406910385023428062355)
              ·
                refine ⟨4857610365577535142093533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238406910385023428062355 4857610365577535142093533)
                ·
                  refine ⟨1821603887091575678285075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4857610365577535142093533 1821603887091575678285075)
                  ·
                    refine ⟨2732405830637363517427613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1821603887091575678285075 2732405830637363517427613)
                    ·
                      refine ⟨1024652186489011319035355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2732405830637363517427613 1024652186489011319035355)
                      ·
                        rfl

theorem cell23_1995503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 1, 3].length) (baseStart_1995503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995503 prefixEnd_1995503 := by exact prefixLift 1995503
  have htrace : WordTrace (prefixWord ++ tailWord_1995503) baseStart_1995503 baseEnd_1995503 := by
    simpa [prefixWord, tailWord_1995503, baseEnd_1995503] using wordTrace_append hprefix tailTrace_1995503
  have hstable : (prefixWord ++ tailWord_1995503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995503).length < 2 ^ (prefixWord ++ tailWord_1995503).sum := by decide
  have hdescent : baseEnd_1995503 < baseStart_1995503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995539 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 4]
def baseStart_1995539 : Nat := 118140960795 + 1995539 * 2 ^ 59
def prefixEnd_1995539 : Nat := 4983230072969 + 3 ^ 40 * 1995539 * 2
def baseEnd_1995539 : Nat := 1024670671792573178185189

theorem tailTrace_1995539 : CollatzResearch.WordTrace tailWord_1995539 prefixEnd_1995539 1024670671792573178185189 := by
  unfold tailWord_1995539
  simp only [CollatzResearch.WordTrace]
  refine ⟨72783286717510488772965671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48522191145006992515310447 72783286717510488772965671)
  ·
    refine ⟨109174930076265733159448507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72783286717510488772965671 109174930076265733159448507)
    ·
      refine ⟨163762395114398599739172761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109174930076265733159448507 163762395114398599739172761)
      ·
        refine ⟨122821796335798949804379571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163762395114398599739172761 122821796335798949804379571)
        ·
          refine ⟨184232694503698424706569357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122821796335798949804379571 184232694503698424706569357)
          ·
            refine ⟨69087260438886909264963509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184232694503698424706569357 69087260438886909264963509)
            ·
              refine ⟨6476930666145647743590329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69087260438886909264963509 6476930666145647743590329)
              ·
                refine ⟨4857697999609235807692747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6476930666145647743590329 4857697999609235807692747)
                ·
                  refine ⟨7286546999413853711539121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4857697999609235807692747 7286546999413853711539121)
                  ·
                    refine ⟨5464910249560390283654341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7286546999413853711539121 5464910249560390283654341)
                    ·
                      refine ⟨1024670671792573178185189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5464910249560390283654341 1024670671792573178185189)
                      ·
                        rfl

theorem cell23_1995539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_1995539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995539 prefixEnd_1995539 := by exact prefixLift 1995539
  have htrace : WordTrace (prefixWord ++ tailWord_1995539) baseStart_1995539 baseEnd_1995539 := by
    simpa [prefixWord, tailWord_1995539, baseEnd_1995539] using wordTrace_append hprefix tailTrace_1995539
  have hstable : (prefixWord ++ tailWord_1995539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995539).length < 2 ^ (prefixWord ++ tailWord_1995539).sum := by decide
  have hdescent : baseEnd_1995539 < baseStart_1995539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995549 : List Nat := [1, 4, 2, 4, 12]
def baseStart_1995549 : Nat := 118140960795 + 1995549 * 2 ^ 59
def prefixEnd_1995549 : Nat := 4983230072969 + 3 ^ 40 * 1995549 * 2
def baseEnd_1995549 : Nat := 1405590955554345869767

theorem tailTrace_1995549 : CollatzResearch.WordTrace tailWord_1995549 prefixEnd_1995549 1405590955554345869767 := by
  unfold tailWord_1995549
  simp only [CollatzResearch.WordTrace]
  refine ⟨72783651447474260480829701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48522434298316173653886467 72783651447474260480829701)
  ·
    refine ⟨13646934646401423840155569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72783651447474260480829701 13646934646401423840155569)
    ·
      refine ⟨10235200984801067880116677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13646934646401423840155569 10235200984801067880116677)
      ·
        refine ⟨1919100184650200227521877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10235200984801067880116677 1919100184650200227521877)
        ·
          refine ⟨1405590955554345869767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1919100184650200227521877 1405590955554345869767)
          ·
            rfl

theorem cell23_1995549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 12].length) (baseStart_1995549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995549 prefixEnd_1995549 := by exact prefixLift 1995549
  have htrace : WordTrace (prefixWord ++ tailWord_1995549) baseStart_1995549 baseEnd_1995549 := by
    simpa [prefixWord, tailWord_1995549, baseEnd_1995549] using wordTrace_append hprefix tailTrace_1995549
  have hstable : (prefixWord ++ tailWord_1995549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995549).length < 2 ^ (prefixWord ++ tailWord_1995549).sum := by decide
  have hdescent : baseEnd_1995549 < baseStart_1995549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995566 : List Nat := [4, 1, 3, 2, 1, 1, 3, 8]
def baseStart_1995566 : Nat := 118140960795 + 1995566 * 2 ^ 59
def prefixEnd_1995566 : Nat := 4983230072969 + 3 ^ 40 * 1995566 * 2
def baseEnd_1995566 : Nat := 37951279102601650835095

theorem tailTrace_1995566 : CollatzResearch.WordTrace tailWord_1995566 prefixEnd_1995566 37951279102601650835095 := by
  unfold tailWord_1995566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9098033936051584048024819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48522847658941781589465701 9098033936051584048024819)
  ·
    refine ⟨13647050904077376072037229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9098033936051584048024819 13647050904077376072037229)
    ·
      refine ⟨5117644089029016027013961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13647050904077376072037229 5117644089029016027013961)
      ·
        refine ⟨3838233066771762020260471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5117644089029016027013961 3838233066771762020260471)
        ·
          refine ⟨5757349600157643030390707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3838233066771762020260471 5757349600157643030390707)
          ·
            refine ⟨8636024400236464545586061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5757349600157643030390707 8636024400236464545586061)
            ·
              refine ⟨3238509150088674204594773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8636024400236464545586061 3238509150088674204594773)
              ·
                refine ⟨37951279102601650835095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3238509150088674204594773 37951279102601650835095)
                ·
                  rfl

theorem cell23_1995566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_1995566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995566 prefixEnd_1995566 := by exact prefixLift 1995566
  have htrace : WordTrace (prefixWord ++ tailWord_1995566) baseStart_1995566 baseEnd_1995566 := by
    simpa [prefixWord, tailWord_1995566, baseEnd_1995566] using wordTrace_append hprefix tailTrace_1995566
  have hstable : (prefixWord ++ tailWord_1995566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995566).length < 2 ^ (prefixWord ++ tailWord_1995566).sum := by decide
  have hdescent : baseEnd_1995566 < baseStart_1995566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995576 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 1, 3, 3]
def baseStart_1995576 : Nat := 118140960795 + 1995576 * 2 ^ 59
def prefixEnd_1995576 : Nat := 4983230072969 + 3 ^ 40 * 1995576 * 2
def baseEnd_1995576 : Nat := 1024689670576789533422519

theorem tailTrace_1995576 : CollatzResearch.WordTrace tailWord_1995576 prefixEnd_1995576 1024689670576789533422519 := by
  unfold tailWord_1995576
  simp only [CollatzResearch.WordTrace]
  refine ⟨36392318109188222046031291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48523090812250962728041721 36392318109188222046031291)
  ·
    refine ⟨54588477163782333069046937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36392318109188222046031291 54588477163782333069046937)
    ·
      refine ⟨40941357872836749801785203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54588477163782333069046937 40941357872836749801785203)
      ·
        refine ⟨61412036809255124702677805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40941357872836749801785203 61412036809255124702677805)
        ·
          refine ⟨23029513803470671763504177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61412036809255124702677805 23029513803470671763504177)
          ·
            refine ⟨17272135352603003822628133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23029513803470671763504177 17272135352603003822628133)
            ·
              refine ⟨3238525378613063216742775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17272135352603003822628133 3238525378613063216742775)
              ·
                refine ⟨4857788067919594825114163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238525378613063216742775 4857788067919594825114163)
                ·
                  refine ⟨7286682101879392237671245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4857788067919594825114163 7286682101879392237671245)
                  ·
                    refine ⟨2732505788204772089126717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7286682101879392237671245 2732505788204772089126717)
                    ·
                      refine ⟨1024689670576789533422519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2732505788204772089126717 1024689670576789533422519)
                      ·
                        rfl

theorem cell23_1995576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_1995576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995576 prefixEnd_1995576 := by exact prefixLift 1995576
  have htrace : WordTrace (prefixWord ++ tailWord_1995576) baseStart_1995576 baseEnd_1995576 := by
    simpa [prefixWord, tailWord_1995576, baseEnd_1995576] using wordTrace_append hprefix tailTrace_1995576
  have hstable : (prefixWord ++ tailWord_1995576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995576).length < 2 ^ (prefixWord ++ tailWord_1995576).sum := by decide
  have hdescent : baseEnd_1995576 < baseStart_1995576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995609 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 2, 6]
def baseStart_1995609 : Nat := 118140960795 + 1995609 * 2 ^ 59
def prefixEnd_1995609 : Nat := 4983230072969 + 3 ^ 40 * 1995609 * 2
def baseEnd_1995609 : Nat := 341568871812795968103289

theorem tailTrace_1995609 : CollatzResearch.WordTrace tailWord_1995609 prefixEnd_1995609 341568871812795968103289 := by
  unfold tailWord_1995609
  simp only [CollatzResearch.WordTrace]
  refine ⟨72785839827256890728013881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48523893218171260485342587 72785839827256890728013881)
  ·
    refine ⟨54589379870442668046010411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72785839827256890728013881 54589379870442668046010411)
    ·
      refine ⟨81884069805664002069015617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54589379870442668046010411 81884069805664002069015617)
      ·
        refine ⟨61413052354248001551761713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81884069805664002069015617 61413052354248001551761713)
        ·
          refine ⟨46059789265686001163821285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61413052354248001551761713 46059789265686001163821285)
          ·
            refine ⟨8636210487316125218216491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46059789265686001163821285 8636210487316125218216491)
            ·
              refine ⟨12954315730974187827324737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8636210487316125218216491 12954315730974187827324737)
              ·
                refine ⟨9715736798230640870493553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12954315730974187827324737 9715736798230640870493553)
                ·
                  refine ⟨7286802598672980652870165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9715736798230640870493553 7286802598672980652870165)
                  ·
                    refine ⟨341568871812795968103289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7286802598672980652870165 341568871812795968103289)
                    ·
                      rfl

theorem cell23_1995609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 6].length) (baseStart_1995609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995609 prefixEnd_1995609 := by exact prefixLift 1995609
  have htrace : WordTrace (prefixWord ++ tailWord_1995609) baseStart_1995609 baseEnd_1995609 := by
    simpa [prefixWord, tailWord_1995609, baseEnd_1995609] using wordTrace_append hprefix tailTrace_1995609
  have hstable : (prefixWord ++ tailWord_1995609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995609).length < 2 ^ (prefixWord ++ tailWord_1995609).sum := by decide
  have hdescent : baseEnd_1995609 < baseStart_1995609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995610 : List Nat := [3, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3]
def baseStart_1995610 : Nat := 118140960795 + 1995610 * 2 ^ 59
def prefixEnd_1995610 : Nat := 4983230072969 + 3 ^ 40 * 1995610 * 2
def baseEnd_1995610 : Nat := 1024707128919042400397363

theorem tailTrace_1995610 : CollatzResearch.WordTrace tailWord_1995610 prefixEnd_1995610 1024707128919042400397363 := by
  unfold tailWord_1995610
  simp only [CollatzResearch.WordTrace]
  refine ⟨18196469075063316974700071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48523917533502178599200189 18196469075063316974700071)
  ·
    refine ⟨27294703612594975462050107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18196469075063316974700071 27294703612594975462050107)
    ·
      refine ⟨40942055418892463193075161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27294703612594975462050107 40942055418892463193075161)
      ·
        refine ⟨30706541564169347394806371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40942055418892463193075161 30706541564169347394806371)
        ·
          refine ⟨46059812346254021092209557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30706541564169347394806371 46059812346254021092209557)
          ·
            refine ⟨2159053703730657238697323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46059812346254021092209557 2159053703730657238697323)
            ·
              refine ⟨3238580555595985858045985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159053703730657238697323 3238580555595985858045985)
              ·
                refine ⟨2428935416696989393534489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3238580555595985858045985 2428935416696989393534489)
                ·
                  refine ⟨1821701562522742045150867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2428935416696989393534489 1821701562522742045150867)
                  ·
                    refine ⟨2732552343784113067726301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1821701562522742045150867 2732552343784113067726301)
                    ·
                      refine ⟨1024707128919042400397363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2732552343784113067726301 1024707128919042400397363)
                      ·
                        rfl

theorem cell23_1995610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_1995610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995610 prefixEnd_1995610 := by exact prefixLift 1995610
  have htrace : WordTrace (prefixWord ++ tailWord_1995610) baseStart_1995610 baseEnd_1995610 := by
    simpa [prefixWord, tailWord_1995610, baseEnd_1995610] using wordTrace_append hprefix tailTrace_1995610
  have hstable : (prefixWord ++ tailWord_1995610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995610).length < 2 ^ (prefixWord ++ tailWord_1995610).sum := by decide
  have hdescent : baseEnd_1995610 < baseStart_1995610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995633 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 1, 4, 2]
def baseStart_1995633 : Nat := 118140960795 + 1995633 * 2 ^ 59
def prefixEnd_1995633 : Nat := 4983230072969 + 3 ^ 40 * 1995633 * 2
def baseEnd_1995633 : Nat := 1024718938974095810409757

theorem tailTrace_1995633 : CollatzResearch.WordTrace tailWord_1995633 prefixEnd_1995633 1024718938974095810409757 := by
  unfold tailWord_1995633
  simp only [CollatzResearch.WordTrace]
  refine ⟨72786715179169942826887553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48524476786113295217925035 72786715179169942826887553)
  ·
    refine ⟨54590036384377457120165665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72786715179169942826887553 54590036384377457120165665)
    ·
      refine ⟨40942527288283092840124249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54590036384377457120165665 40942527288283092840124249)
      ·
        refine ⟨30706895466212319630093187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40942527288283092840124249 30706895466212319630093187)
        ·
          refine ⟨46060343199318479445139781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30706895466212319630093187 46060343199318479445139781)
          ·
            refine ⟨8636314349872214895963709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46060343199318479445139781 8636314349872214895963709)
            ·
              refine ⟨3238617881202080585986391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8636314349872214895963709 3238617881202080585986391)
              ·
                refine ⟨4857926821803120878979587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238617881202080585986391 4857926821803120878979587)
                ·
                  refine ⟨7286890232704681318469381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4857926821803120878979587 7286890232704681318469381)
                  ·
                    refine ⟨1366291918632127747213009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7286890232704681318469381 1366291918632127747213009)
                    ·
                      refine ⟨1024718938974095810409757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1366291918632127747213009 1024718938974095810409757)
                      ·
                        rfl

theorem cell23_1995633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_1995633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995633 prefixEnd_1995633 := by exact prefixLift 1995633
  have htrace : WordTrace (prefixWord ++ tailWord_1995633) baseStart_1995633 baseEnd_1995633 := by
    simpa [prefixWord, tailWord_1995633, baseEnd_1995633] using wordTrace_append hprefix tailTrace_1995633
  have hstable : (prefixWord ++ tailWord_1995633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995633).length < 2 ^ (prefixWord ++ tailWord_1995633).sum := by decide
  have hdescent : baseEnd_1995633 < baseStart_1995633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995773 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 7, 1, 3]
def baseStart_1995773 : Nat := 118140960795 + 1995773 * 2 ^ 59
def prefixEnd_1995773 : Nat := 4983230072969 + 3 ^ 40 * 1995773 * 2
def baseEnd_1995773 : Nat := 1024790826265725262659113

theorem tailTrace_1995773 : CollatzResearch.WordTrace tailWord_1995773 prefixEnd_1995773 1024790826265725262659113 := by
  unfold tailWord_1995773
  simp only [CollatzResearch.WordTrace]
  refine ⟨72791821398662746736983973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48527880932441831157989315 72791821398662746736983973)
  ·
    refine ⟨13648466512249265013184495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72791821398662746736983973 13648466512249265013184495)
    ·
      refine ⟨20472699768373897519776743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13648466512249265013184495 20472699768373897519776743)
      ·
        refine ⟨30709049652560846279665115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20472699768373897519776743 30709049652560846279665115)
        ·
          refine ⟨46063574478841269419497673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30709049652560846279665115 46063574478841269419497673)
          ·
            refine ⟨34547680859130952064623255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46063574478841269419497673 34547680859130952064623255)
            ·
              refine ⟨51821521288696428096934883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34547680859130952064623255 51821521288696428096934883)
              ·
                refine ⟨77732281933044642145402325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51821521288696428096934883 77732281933044642145402325)
                ·
                  refine ⟨1821850357805733800282867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 77732281933044642145402325 1821850357805733800282867)
                  ·
                    refine ⟨2732775536708600700424301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1821850357805733800282867 2732775536708600700424301)
                    ·
                      refine ⟨1024790826265725262659113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2732775536708600700424301 1024790826265725262659113)
                      ·
                        rfl

theorem cell23_1995773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_1995773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995773 prefixEnd_1995773 := by exact prefixLift 1995773
  have htrace : WordTrace (prefixWord ++ tailWord_1995773) baseStart_1995773 baseEnd_1995773 := by
    simpa [prefixWord, tailWord_1995773, baseEnd_1995773] using wordTrace_append hprefix tailTrace_1995773
  have hstable : (prefixWord ++ tailWord_1995773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995773).length < 2 ^ (prefixWord ++ tailWord_1995773).sum := by decide
  have hdescent : baseEnd_1995773 < baseStart_1995773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995790 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3]
def baseStart_1995790 : Nat := 118140960795 + 1995790 * 2 ^ 59
def prefixEnd_1995790 : Nat := 4983230072969 + 3 ^ 40 * 1995790 * 2
def baseEnd_1995790 : Nat := 1024799555436851696146535

theorem tailTrace_1995790 : CollatzResearch.WordTrace tailWord_1995790 prefixEnd_1995790 1024799555436851696146535 := by
  unfold tailWord_1995790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9099055179950144830044103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48528294293067439093568549 9099055179950144830044103)
  ·
    refine ⟨13648582769925217245066155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9099055179950144830044103 13648582769925217245066155)
    ·
      refine ⟨20472874154887825867599233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13648582769925217245066155 20472874154887825867599233)
      ·
        refine ⟨15354655616165869400699425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20472874154887825867599233 15354655616165869400699425)
        ·
          refine ⟨11515991712124402050524569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15354655616165869400699425 11515991712124402050524569)
          ·
            refine ⟨8636993784093301537893427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11515991712124402050524569 8636993784093301537893427)
            ·
              refine ⟨12955490676139952306840141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8636993784093301537893427 12955490676139952306840141)
              ·
                refine ⟨4858309003552482115065053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12955490676139952306840141 4858309003552482115065053)
                ·
                  refine ⟨1821865876332180793149395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4858309003552482115065053 1821865876332180793149395)
                  ·
                    refine ⟨2732798814498271189724093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1821865876332180793149395 2732798814498271189724093)
                    ·
                      refine ⟨1024799555436851696146535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2732798814498271189724093 1024799555436851696146535)
                      ·
                        rfl

theorem cell23_1995790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_1995790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995790 prefixEnd_1995790 := by exact prefixLift 1995790
  have htrace : WordTrace (prefixWord ++ tailWord_1995790) baseStart_1995790 baseEnd_1995790 := by
    simpa [prefixWord, tailWord_1995790, baseEnd_1995790] using wordTrace_append hprefix tailTrace_1995790
  have hstable : (prefixWord ++ tailWord_1995790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995790).length < 2 ^ (prefixWord ++ tailWord_1995790).sum := by decide
  have hdescent : baseEnd_1995790 < baseStart_1995790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995810 : List Nat := [3, 3, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_1995810 : Nat := 118140960795 + 1995810 * 2 ^ 59
def prefixEnd_1995810 : Nat := 4983230072969 + 3 ^ 40 * 1995810 * 2
def baseEnd_1995810 : Nat := 341603275016647205965481

theorem tailTrace_1995810 : CollatzResearch.WordTrace tailWord_1995810 prefixEnd_1995810 341603275016647205965481 := by
  unfold tailWord_1995810
  simp only [CollatzResearch.WordTrace]
  refine ⟨18198292724882175514020221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48528780599685801370720589 18198292724882175514020221)
  ·
    refine ⟨6824359771830815817757583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18198292724882175514020221 6824359771830815817757583)
    ·
      refine ⟨10236539657746223726636375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6824359771830815817757583 10236539657746223726636375)
      ·
        refine ⟨15354809486619335589954563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10236539657746223726636375 15354809486619335589954563)
        ·
          refine ⟨23032214229929003384931845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15354809486619335589954563 23032214229929003384931845)
          ·
            refine ⟨4318540168111688134674721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23032214229929003384931845 4318540168111688134674721)
            ·
              refine ⟨3238905126083766101006041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4318540168111688134674721 3238905126083766101006041)
              ·
                refine ⟨2429178844562824575754531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3238905126083766101006041 2429178844562824575754531)
                ·
                  refine ⟨3643768266844236863631797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429178844562824575754531 3643768266844236863631797)
                  ·
                    refine ⟨341603275016647205965481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3643768266844236863631797 341603275016647205965481)
                    ·
                      rfl

theorem cell23_1995810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_1995810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995810 prefixEnd_1995810 := by exact prefixLift 1995810
  have htrace : WordTrace (prefixWord ++ tailWord_1995810) baseStart_1995810 baseEnd_1995810 := by
    simpa [prefixWord, tailWord_1995810, baseEnd_1995810] using wordTrace_append hprefix tailTrace_1995810
  have hstable : (prefixWord ++ tailWord_1995810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995810).length < 2 ^ (prefixWord ++ tailWord_1995810).sum := by decide
  have hdescent : baseEnd_1995810 < baseStart_1995810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995813 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 2, 6, 2]
def baseStart_1995813 : Nat := 118140960795 + 1995813 * 2 ^ 59
def prefixEnd_1995813 : Nat := 4983230072969 + 3 ^ 40 * 1995813 * 2
def baseEnd_1995813 : Nat := 1024811365491905106158929

theorem tailTrace_1995813 : CollatzResearch.WordTrace tailWord_1995813 prefixEnd_1995813 1024811365491905106158929 := by
  unfold tailWord_1995813
  simp only [CollatzResearch.WordTrace]
  refine ⟨72793280318517833568440093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48528853545678555712293395 72793280318517833568440093)
  ·
    refine ⟨27297480119444187588165035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72793280318517833568440093 27297480119444187588165035)
    ·
      refine ⟨40946220179166281382247553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27297480119444187588165035 40946220179166281382247553)
      ·
        refine ⟨30709665134374711036685665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40946220179166281382247553 30709665134374711036685665)
        ·
          refine ⟨23032248850781033277514249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30709665134374711036685665 23032248850781033277514249)
          ·
            refine ⟨17274186638085774958135687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23032248850781033277514249 17274186638085774958135687)
            ·
              refine ⟨25911279957128662437203531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17274186638085774958135687 25911279957128662437203531)
              ·
                refine ⟨38866919935692993655805297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25911279957128662437203531 38866919935692993655805297)
                ·
                  refine ⟨29150189951769745241853973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38866919935692993655805297 29150189951769745241853973)
                  ·
                    refine ⟨1366415153989206808211905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29150189951769745241853973 1366415153989206808211905)
                    ·
                      refine ⟨1024811365491905106158929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1366415153989206808211905 1024811365491905106158929)
                      ·
                        rfl

theorem cell23_1995813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_1995813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995813 prefixEnd_1995813 := by exact prefixLift 1995813
  have htrace : WordTrace (prefixWord ++ tailWord_1995813) baseStart_1995813 baseEnd_1995813 := by
    simpa [prefixWord, tailWord_1995813, baseEnd_1995813] using wordTrace_append hprefix tailTrace_1995813
  have hstable : (prefixWord ++ tailWord_1995813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995813).length < 2 ^ (prefixWord ++ tailWord_1995813).sum := by decide
  have hdescent : baseEnd_1995813 < baseStart_1995813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995833 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1995833 : Nat := 118140960795 + 1995833 * 2 ^ 59
def prefixEnd_1995833 : Nat := 4983230072969 + 3 ^ 40 * 1995833 * 2
def baseEnd_1995833 : Nat := 1024821635104995027908837

theorem tailTrace_1995833 : CollatzResearch.WordTrace tailWord_1995833 prefixEnd_1995833 1024821635104995027908837 := by
  unfold tailWord_1995833
  simp only [CollatzResearch.WordTrace]
  refine ⟨72794009778445376984168153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48529339852296917989445435 72794009778445376984168153)
  ·
    refine ⟨54595507333834032738126115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72794009778445376984168153 54595507333834032738126115)
    ·
      refine ⟨81893261000751049107189173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54595507333834032738126115 81893261000751049107189173)
      ·
        refine ⟨7677493218820410853798985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81893261000751049107189173 7677493218820410853798985)
        ·
          refine ⟨5758119914115308140349239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7677493218820410853798985 5758119914115308140349239)
          ·
            refine ⟨8637179871172962210523859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5758119914115308140349239 8637179871172962210523859)
            ·
              refine ⟨12955769806759443315785789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8637179871172962210523859 12955769806759443315785789)
              ·
                refine ⟨4858413677534791243419671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12955769806759443315785789 4858413677534791243419671)
                ·
                  refine ⟨7287620516302186865129507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4858413677534791243419671 7287620516302186865129507)
                  ·
                    refine ⟨10931430774453280297694261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7287620516302186865129507 10931430774453280297694261)
                    ·
                      refine ⟨1024821635104995027908837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10931430774453280297694261 1024821635104995027908837)
                      ·
                        rfl

theorem cell23_1995833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1995833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995833 prefixEnd_1995833 := by exact prefixLift 1995833
  have htrace : WordTrace (prefixWord ++ tailWord_1995833) baseStart_1995833 baseEnd_1995833 := by
    simpa [prefixWord, tailWord_1995833, baseEnd_1995833] using wordTrace_append hprefix tailTrace_1995833
  have hstable : (prefixWord ++ tailWord_1995833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995833).length < 2 ^ (prefixWord ++ tailWord_1995833).sum := by decide
  have hdescent : baseEnd_1995833 < baseStart_1995833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995836 : List Nat := [2, 2, 2, 2, 2, 2, 11]
def baseStart_1995836 : Nat := 118140960795 + 1995836 * 2 ^ 59
def prefixEnd_1995836 : Nat := 4983230072969 + 3 ^ 40 * 1995836 * 2
def baseEnd_1995836 : Nat := 12652137969715537236683

theorem tailTrace_1995836 : CollatzResearch.WordTrace tailWord_1995836 prefixEnd_1995836 12652137969715537236683 := by
  unfold tailWord_1995836
  simp only [CollatzResearch.WordTrace]
  refine ⟨36397059598717254248263681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48529412798289672331018241 36397059598717254248263681)
  ·
    refine ⟨27297794699037940686197761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36397059598717254248263681 27297794699037940686197761)
    ·
      refine ⟨20473346024278455514648321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27297794699037940686197761 20473346024278455514648321)
      ·
        refine ⟨15355009518208841635986241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20473346024278455514648321 15355009518208841635986241)
        ·
          refine ⟨11516257138656631226989681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15355009518208841635986241 11516257138656631226989681)
          ·
            refine ⟨8637192853992473420242261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11516257138656631226989681 8637192853992473420242261)
            ·
              refine ⟨12652137969715537236683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8637192853992473420242261 12652137969715537236683)
              ·
                rfl

theorem cell23_1995836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 11].length) (baseStart_1995836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995836 prefixEnd_1995836 := by exact prefixLift 1995836
  have htrace : WordTrace (prefixWord ++ tailWord_1995836) baseStart_1995836 baseEnd_1995836 := by
    simpa [prefixWord, tailWord_1995836, baseEnd_1995836] using wordTrace_append hprefix tailTrace_1995836
  have hstable : (prefixWord ++ tailWord_1995836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995836).length < 2 ^ (prefixWord ++ tailWord_1995836).sum := by decide
  have hdescent : baseEnd_1995836 < baseStart_1995836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995841 : List Nat := [1, 2, 5, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_1995841 : Nat := 118140960795 + 1995841 * 2 ^ 59
def prefixEnd_1995841 : Nat := 4983230072969 + 3 ^ 40 * 1995841 * 2
def baseEnd_1995841 : Nat := 1024825742950230996608801

theorem tailTrace_1995841 : CollatzResearch.WordTrace tailWord_1995841 prefixEnd_1995841 1024825742950230996608801 := by
  unfold tailWord_1995841
  simp only [CollatzResearch.WordTrace]
  refine ⟨72794301562416394350459377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48529534374944262900306251 72794301562416394350459377)
  ·
    refine ⟨54595726171812295762844533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72794301562416394350459377 54595726171812295762844533)
    ·
      refine ⟨5118349328607402727766675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54595726171812295762844533 5118349328607402727766675)
      ·
        refine ⟨7677523992911104091650013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5118349328607402727766675 7677523992911104091650013)
        ·
          refine ⟨2879071497341664034368755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7677523992911104091650013 2879071497341664034368755)
          ·
            refine ⟨4318607246012496051553133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879071497341664034368755 4318607246012496051553133)
            ·
              refine ⟨1619477717254686019332425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4318607246012496051553133 1619477717254686019332425)
              ·
                refine ⟨1214608287941014514499319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1619477717254686019332425 1214608287941014514499319)
                ·
                  refine ⟨1821912431911521771748979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1214608287941014514499319 1821912431911521771748979)
                  ·
                    refine ⟨2732868647867282657623469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1821912431911521771748979 2732868647867282657623469)
                    ·
                      refine ⟨1024825742950230996608801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2732868647867282657623469 1024825742950230996608801)
                      ·
                        rfl

theorem cell23_1995841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_1995841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995841 prefixEnd_1995841 := by exact prefixLift 1995841
  have htrace : WordTrace (prefixWord ++ tailWord_1995841) baseStart_1995841 baseEnd_1995841 := by
    simpa [prefixWord, tailWord_1995841, baseEnd_1995841] using wordTrace_append hprefix tailTrace_1995841
  have hstable : (prefixWord ++ tailWord_1995841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995841).length < 2 ^ (prefixWord ++ tailWord_1995841).sum := by decide
  have hdescent : baseEnd_1995841 < baseStart_1995841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995847 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 3, 2, 2]
def baseStart_1995847 : Nat := 118140960795 + 1995847 * 2 ^ 59
def prefixEnd_1995847 : Nat := 4983230072969 + 3 ^ 40 * 1995847 * 2
def baseEnd_1995847 : Nat := 1024828823834157973133773

theorem tailTrace_1995847 : CollatzResearch.WordTrace tailWord_1995847 prefixEnd_1995847 1024828823834157973133773 := by
  unfold tailWord_1995847
  simp only [CollatzResearch.WordTrace]
  refine ⟨72794520400394657375177795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48529680266929771583451863 72794520400394657375177795)
  ·
    refine ⟨109191780600591986062766693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72794520400394657375177795 109191780600591986062766693)
    ·
      refine ⟨20473458862610997386768755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109191780600591986062766693 20473458862610997386768755)
      ·
        refine ⟨30710188293916496080153133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20473458862610997386768755 30710188293916496080153133)
        ·
          refine ⟨11516320610218686030057425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30710188293916496080153133 11516320610218686030057425)
          ·
            refine ⟨8637240457664014522543069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11516320610218686030057425 8637240457664014522543069)
            ·
              refine ⟨3238965171624005445953651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8637240457664014522543069 3238965171624005445953651)
              ·
                refine ⟨4858447757436008168930477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238965171624005445953651 4858447757436008168930477)
                ·
                  refine ⟨1821917909038503063348929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4858447757436008168930477 1821917909038503063348929)
                  ·
                    refine ⟨1366438431778877297511697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1821917909038503063348929 1366438431778877297511697)
                    ·
                      refine ⟨1024828823834157973133773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1366438431778877297511697 1024828823834157973133773)
                      ·
                        rfl

theorem cell23_1995847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_1995847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995847 prefixEnd_1995847 := by exact prefixLift 1995847
  have htrace : WordTrace (prefixWord ++ tailWord_1995847) baseStart_1995847 baseEnd_1995847 := by
    simpa [prefixWord, tailWord_1995847, baseEnd_1995847] using wordTrace_append hprefix tailTrace_1995847
  have hstable : (prefixWord ++ tailWord_1995847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995847).length < 2 ^ (prefixWord ++ tailWord_1995847).sum := by decide
  have hdescent : baseEnd_1995847 < baseStart_1995847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995853 : List Nat := [1, 6, 1, 1, 1, 2, 1, 10]
def baseStart_1995853 : Nat := 118140960795 + 1995853 * 2 ^ 59
def prefixEnd_1995853 : Nat := 4983230072969 + 3 ^ 40 * 1995853 * 2
def baseEnd_1995853 : Nat := 37956737211780924061435

theorem tailTrace_1995853 : CollatzResearch.WordTrace tailWord_1995853 prefixEnd_1995853 37956737211780924061435 := by
  unfold tailWord_1995853
  simp only [CollatzResearch.WordTrace]
  refine ⟨72794739238372920399896213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48529826158915280266597475 72794739238372920399896213)
  ·
    refine ⟨3412253401798730643745135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72794739238372920399896213 3412253401798730643745135)
    ·
      refine ⟨5118380102698095965617703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3412253401798730643745135 5118380102698095965617703)
      ·
        refine ⟨7677570154047143948426555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5118380102698095965617703 7677570154047143948426555)
        ·
          refine ⟨11516355231070715922639833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7677570154047143948426555 11516355231070715922639833)
          ·
            refine ⟨8637266423303036941979875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11516355231070715922639833 8637266423303036941979875)
            ·
              refine ⟨12955899634954555412969813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8637266423303036941979875 12955899634954555412969813)
              ·
                refine ⟨37956737211780924061435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12955899634954555412969813 37956737211780924061435)
                ·
                  rfl

theorem cell23_1995853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 10].length) (baseStart_1995853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995853 prefixEnd_1995853 := by exact prefixLift 1995853
  have htrace : WordTrace (prefixWord ++ tailWord_1995853) baseStart_1995853 baseEnd_1995853 := by
    simpa [prefixWord, tailWord_1995853, baseEnd_1995853] using wordTrace_append hprefix tailTrace_1995853
  have hstable : (prefixWord ++ tailWord_1995853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995853).length < 2 ^ (prefixWord ++ tailWord_1995853).sum := by decide
  have hdescent : baseEnd_1995853 < baseStart_1995853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995863 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 3]
def baseStart_1995863 : Nat := 118140960795 + 1995863 * 2 ^ 59
def prefixEnd_1995863 : Nat := 4983230072969 + 3 ^ 40 * 1995863 * 2
def baseEnd_1995863 : Nat := 1024837039524629910533699

theorem tailTrace_1995863 : CollatzResearch.WordTrace tailWord_1995863 prefixEnd_1995863 1024837039524629910533699 := by
  unfold tailWord_1995863
  simp only [CollatzResearch.WordTrace]
  refine ⟨72795103968336692107760243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48530069312224461405173495 72795103968336692107760243)
  ·
    refine ⟨109192655952505038161640365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72795103968336692107760243 109192655952505038161640365)
    ·
      refine ⟨40947245982189389310615137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109192655952505038161640365 40947245982189389310615137)
      ·
        refine ⟨30710434486642041982961353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40947245982189389310615137 30710434486642041982961353)
        ·
          refine ⟨23032825864981531487221015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30710434486642041982961353 23032825864981531487221015)
          ·
            refine ⟨34549238797472297230831523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23032825864981531487221015 34549238797472297230831523)
            ·
              refine ⟨51823858196208445846247285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34549238797472297230831523 51823858196208445846247285)
              ·
                refine ⟨4858486705894541798085683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51823858196208445846247285 4858486705894541798085683)
                ·
                  refine ⟨7287730058841812697128525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4858486705894541798085683 7287730058841812697128525)
                  ·
                    refine ⟨2732898772065679761423197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7287730058841812697128525 2732898772065679761423197)
                    ·
                      refine ⟨1024837039524629910533699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2732898772065679761423197 1024837039524629910533699)
                      ·
                        rfl

theorem cell23_1995863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_1995863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995863 prefixEnd_1995863 := by exact prefixLift 1995863
  have htrace : WordTrace (prefixWord ++ tailWord_1995863) baseStart_1995863 baseEnd_1995863 := by
    simpa [prefixWord, tailWord_1995863, baseEnd_1995863] using wordTrace_append hprefix tailTrace_1995863
  have hstable : (prefixWord ++ tailWord_1995863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995863).length < 2 ^ (prefixWord ++ tailWord_1995863).sum := by decide
  have hdescent : baseEnd_1995863 < baseStart_1995863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995866 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 4, 7]
def baseStart_1995866 : Nat := 118140960795 + 1995866 * 2 ^ 59
def prefixEnd_1995866 : Nat := 4983230072969 + 3 ^ 40 * 1995866 * 2
def baseEnd_1995866 : Nat := 341612859988864466265395

theorem tailTrace_1995866 : CollatzResearch.WordTrace tailWord_1995866 prefixEnd_1995866 341612859988864466265395 := by
  unfold tailWord_1995866
  simp only [CollatzResearch.WordTrace]
  refine ⟨18198803346831455905029863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48530142258217215746746301 18198803346831455905029863)
  ·
    refine ⟨27298205020247183857544795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18198803346831455905029863 27298205020247183857544795)
    ·
      refine ⟨40947307530370775786317193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27298205020247183857544795 40947307530370775786317193)
      ·
        refine ⟨30710480647778081839737895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40947307530370775786317193 30710480647778081839737895)
        ·
          refine ⟨46065720971667122759606843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30710480647778081839737895 46065720971667122759606843)
          ·
            refine ⟨69098581457500684139410265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46065720971667122759606843 69098581457500684139410265)
            ·
              refine ⟨51823936093125513104557699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69098581457500684139410265 51823936093125513104557699)
              ·
                refine ⟨77735904139688269656836549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51823936093125513104557699 77735904139688269656836549)
                ·
                  refine ⟨14575482026191550560656853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77735904139688269656836549 14575482026191550560656853)
                  ·
                    refine ⟨341612859988864466265395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14575482026191550560656853 341612859988864466265395)
                    ·
                      rfl

theorem cell23_1995866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_1995866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995866 prefixEnd_1995866 := by exact prefixLift 1995866
  have htrace : WordTrace (prefixWord ++ tailWord_1995866) baseStart_1995866 baseEnd_1995866 := by
    simpa [prefixWord, tailWord_1995866, baseEnd_1995866] using wordTrace_append hprefix tailTrace_1995866
  have hstable : (prefixWord ++ tailWord_1995866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995866).length < 2 ^ (prefixWord ++ tailWord_1995866).sum := by decide
  have hdescent : baseEnd_1995866 < baseStart_1995866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995913 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 2, 6]
def baseStart_1995913 : Nat := 118140960795 + 1995913 * 2 ^ 59
def prefixEnd_1995913 : Nat := 4983230072969 + 3 ^ 40 * 1995913 * 2
def baseEnd_1995913 : Nat := 341620904519118238302823

theorem tailTrace_1995913 : CollatzResearch.WordTrace tailWord_1995913 prefixEnd_1995913 341620904519118238302823 := by
  unfold tailWord_1995913
  simp only [CollatzResearch.WordTrace]
  refine ⟨72796927618155550647080393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48531285078770367098053595 72796927618155550647080393)
  ·
    refine ⟨54597695713616662985310295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72796927618155550647080393 54597695713616662985310295)
    ·
      refine ⟨81896543570424994477965443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54597695713616662985310295 81896543570424994477965443)
      ·
        refine ⟨122844815355637491716948165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81896543570424994477965443 122844815355637491716948165)
        ·
          refine ⟨23033402879182029696927781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122844815355637491716948165 23033402879182029696927781)
          ·
            refine ⟨4318763039846630568173959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23033402879182029696927781 4318763039846630568173959)
            ·
              refine ⟨6478144559769945852260939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4318763039846630568173959 6478144559769945852260939)
              ·
                refine ⟨9717216839654918778391409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6478144559769945852260939 9717216839654918778391409)
                ·
                  refine ⟨7287912629741189083793557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9717216839654918778391409 7287912629741189083793557)
                  ·
                    refine ⟨341620904519118238302823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7287912629741189083793557 341620904519118238302823)
                    ·
                      rfl

theorem cell23_1995913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 6].length) (baseStart_1995913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995913 prefixEnd_1995913 := by exact prefixLift 1995913
  have htrace : WordTrace (prefixWord ++ tailWord_1995913) baseStart_1995913 baseEnd_1995913 := by
    simpa [prefixWord, tailWord_1995913, baseEnd_1995913] using wordTrace_append hprefix tailTrace_1995913
  have hstable : (prefixWord ++ tailWord_1995913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995913).length < 2 ^ (prefixWord ++ tailWord_1995913).sum := by decide
  have hdescent : baseEnd_1995913 < baseStart_1995913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995933 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1995933 : Nat := 118140960795 + 1995933 * 2 ^ 59
def prefixEnd_1995933 : Nat := 4983230072969 + 3 ^ 40 * 1995933 * 2
def baseEnd_1995933 : Nat := 1024872983170444636658377

theorem tailTrace_1995933 : CollatzResearch.WordTrace tailWord_1995933 prefixEnd_1995933 1024872983170444636658377 := by
  unfold tailWord_1995933
  simp only [CollatzResearch.WordTrace]
  refine ⟨72797657078083094062808453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48531771385388729375205635 72797657078083094062808453)
  ·
    refine ⟨13649560702140580136776585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72797657078083094062808453 13649560702140580136776585)
    ·
      refine ⟨10237170526605435102582439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13649560702140580136776585 10237170526605435102582439)
      ·
        refine ⟨15355755789908152653873659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10237170526605435102582439 15355755789908152653873659)
        ·
          refine ⟨23033633684862228980810489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15355755789908152653873659 23033633684862228980810489)
          ·
            refine ⟨17275225263646671735607867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23033633684862228980810489 17275225263646671735607867)
            ·
              refine ⟨25912837895470007603411801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17275225263646671735607867 25912837895470007603411801)
              ·
                refine ⟨19434628421602505702558851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25912837895470007603411801 19434628421602505702558851)
                ·
                  refine ⟨29151942632403758553838277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19434628421602505702558851 29151942632403758553838277)
                  ·
                    refine ⟨5465989243575704728844677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29151942632403758553838277 5465989243575704728844677)
                    ·
                      refine ⟨1024872983170444636658377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5465989243575704728844677 1024872983170444636658377)
                      ·
                        rfl

theorem cell23_1995933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1995933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995933 prefixEnd_1995933 := by exact prefixLift 1995933
  have htrace : WordTrace (prefixWord ++ tailWord_1995933) baseStart_1995933 baseEnd_1995933 := by
    simpa [prefixWord, tailWord_1995933, baseEnd_1995933] using wordTrace_append hprefix tailTrace_1995933
  have hstable : (prefixWord ++ tailWord_1995933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995933).length < 2 ^ (prefixWord ++ tailWord_1995933).sum := by decide
  have hdescent : baseEnd_1995933 < baseStart_1995933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995937 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 4, 2, 2]
def baseStart_1995937 : Nat := 118140960795 + 1995937 * 2 ^ 59
def prefixEnd_1995937 : Nat := 4983230072969 + 3 ^ 40 * 1995937 * 2
def baseEnd_1995937 : Nat := 1024875037093062621008359

theorem tailTrace_1995937 : CollatzResearch.WordTrace tailWord_1995937 prefixEnd_1995937 1024875037093062621008359 := by
  unfold tailWord_1995937
  simp only [CollatzResearch.WordTrace]
  refine ⟨72797802970068602745954065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48531868646712401830636043 72797802970068602745954065)
  ·
    refine ⟨54598352227551452059465549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72797802970068602745954065 54598352227551452059465549)
    ·
      refine ⟨20474382085331794522299581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54598352227551452059465549 20474382085331794522299581)
      ·
        refine ⟨7677893281999422945862343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20474382085331794522299581 7677893281999422945862343)
        ·
          refine ⟨11516839922999134418793515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7677893281999422945862343 11516839922999134418793515)
          ·
            refine ⟨17275259884498701628190273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11516839922999134418793515 17275259884498701628190273)
            ·
              refine ⟨12956444913374026221142705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17275259884498701628190273 12956444913374026221142705)
              ·
                refine ⟨9717333685030519665857029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12956444913374026221142705 9717333685030519665857029)
                ·
                  refine ⟨1822000065943222437348193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9717333685030519665857029 1822000065943222437348193)
                  ·
                    refine ⟨1366500049457416828011145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1822000065943222437348193 1366500049457416828011145)
                    ·
                      refine ⟨1024875037093062621008359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1366500049457416828011145 1024875037093062621008359)
                      ·
                        rfl

theorem cell23_1995937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_1995937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995937 prefixEnd_1995937 := by exact prefixLift 1995937
  have htrace : WordTrace (prefixWord ++ tailWord_1995937) baseStart_1995937 baseEnd_1995937 := by
    simpa [prefixWord, tailWord_1995937, baseEnd_1995937] using wordTrace_append hprefix tailTrace_1995937
  have hstable : (prefixWord ++ tailWord_1995937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995937).length < 2 ^ (prefixWord ++ tailWord_1995937).sum := by decide
  have hdescent : baseEnd_1995937 < baseStart_1995937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995954 : List Nat := [3, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2]
def baseStart_1995954 : Nat := 118140960795 + 1995954 * 2 ^ 59
def prefixEnd_1995954 : Nat := 4983230072969 + 3 ^ 40 * 1995954 * 2
def baseEnd_1995954 : Nat := 1024883766264189054495781

theorem tailTrace_1995954 : CollatzResearch.WordTrace tailWord_1995954 prefixEnd_1995954 1024883766264189054495781 := by
  unfold tailWord_1995954
  simp only [CollatzResearch.WordTrace]
  refine ⟨18199605752751753662330729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48532282007338009766215277 18199605752751753662330729)
  ·
    refine ⟨13649704314563815246748047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18199605752751753662330729 13649704314563815246748047)
    ·
      refine ⟨20474556471845722870122071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13649704314563815246748047 20474556471845722870122071)
      ·
        refine ⟨30711834707768584305183107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20474556471845722870122071 30711834707768584305183107)
        ·
          refine ⟨46067752061652876457774661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30711834707768584305183107 46067752061652876457774661)
          ·
            refine ⟨8637703511559914335832749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46067752061652876457774661 8637703511559914335832749)
            ·
              refine ⟨3239138816834967875937281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8637703511559914335832749 3239138816834967875937281)
              ·
                refine ⟨2429354112626225906952961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3239138816834967875937281 2429354112626225906952961)
                ·
                  refine ⟨1822015584469669430214721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2429354112626225906952961 1822015584469669430214721)
                  ·
                    refine ⟨1366511688352252072661041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1822015584469669430214721 1366511688352252072661041)
                    ·
                      refine ⟨1024883766264189054495781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1366511688352252072661041 1024883766264189054495781)
                      ·
                        rfl

theorem cell23_1995954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_1995954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1995954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1995954 prefixEnd_1995954 := by exact prefixLift 1995954
  have htrace : WordTrace (prefixWord ++ tailWord_1995954) baseStart_1995954 baseEnd_1995954 := by
    simpa [prefixWord, tailWord_1995954, baseEnd_1995954] using wordTrace_append hprefix tailTrace_1995954
  have hstable : (prefixWord ++ tailWord_1995954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995954).length < 2 ^ (prefixWord ++ tailWord_1995954).sum := by decide
  have hdescent : baseEnd_1995954 < baseStart_1995954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996007 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 2, 5]
def baseStart_1996007 : Nat := 118140960795 + 1996007 * 2 ^ 59
def prefixEnd_1996007 : Nat := 4983230072969 + 3 ^ 40 * 1996007 * 2
def baseEnd_1996007 : Nat := 341636993579625782377679

theorem tailTrace_1996007 : CollatzResearch.WordTrace tailWord_1996007 prefixEnd_1996007 341636993579625782377679 := by
  unfold tailWord_1996007
  simp only [CollatzResearch.WordTrace]
  refine ⟨72800356079815004701002275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48533570719876669800668183 72800356079815004701002275)
  ·
    refine ⟨109200534119722507051503413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72800356079815004701002275 109200534119722507051503413)
    ·
      refine ⟨10237550073723985036078445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109200534119722507051503413 10237550073723985036078445)
      ·
        refine ⟨3839081277646494388529417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10237550073723985036078445 3839081277646494388529417)
        ·
          refine ⟨2879310958234870791397063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3839081277646494388529417 2879310958234870791397063)
          ·
            refine ⟨4318966437352306187095595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879310958234870791397063 4318966437352306187095595)
            ·
              refine ⟨6478449656028459280643393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4318966437352306187095595 6478449656028459280643393)
              ·
                refine ⟨4858837242021344460482545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6478449656028459280643393 4858837242021344460482545)
                ·
                  refine ⟨3644127931516008345361909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4858837242021344460482545 3644127931516008345361909)
                  ·
                    refine ⟨341636993579625782377679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3644127931516008345361909 341636993579625782377679)
                    ·
                      rfl

theorem cell23_1996007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_1996007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996007 prefixEnd_1996007 := by exact prefixLift 1996007
  have htrace : WordTrace (prefixWord ++ tailWord_1996007) baseStart_1996007 baseEnd_1996007 := by
    simpa [prefixWord, tailWord_1996007, baseEnd_1996007] using wordTrace_append hprefix tailTrace_1996007
  have hstable : (prefixWord ++ tailWord_1996007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996007).length < 2 ^ (prefixWord ++ tailWord_1996007).sum := by decide
  have hdescent : baseEnd_1996007 < baseStart_1996007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996010 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1996010 : Nat := 118140960795 + 1996010 * 2 ^ 59
def prefixEnd_1996010 : Nat := 4983230072969 + 3 ^ 40 * 1996010 * 2
def baseEnd_1996010 : Nat := 1024912521180840835395523

theorem tailTrace_1996010 : CollatzResearch.WordTrace tailWord_1996010 prefixEnd_1996010 1024912521180840835395523 := by
  unfold tailWord_1996010
  simp only [CollatzResearch.WordTrace]
  refine ⟨18200116374701034053340371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48533643665869424142240989 18200116374701034053340371)
  ·
    refine ⟨27300174562051551080010557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18200116374701034053340371 27300174562051551080010557)
    ·
      refine ⟨10237565460769331655003959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27300174562051551080010557 10237565460769331655003959)
      ·
        refine ⟨15356348191153997482505939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10237565460769331655003959 15356348191153997482505939)
        ·
          refine ⟨23034522286730996223758909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15356348191153997482505939 23034522286730996223758909)
          ·
            refine ⟨8637945857524123583909591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23034522286730996223758909 8637945857524123583909591)
            ·
              refine ⟨12956918786286185375864387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8637945857524123583909591 12956918786286185375864387)
              ·
                refine ⟨19435378179429278063796581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12956918786286185375864387 19435378179429278063796581)
                ·
                  refine ⟨3644133408642989636961859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19435378179429278063796581 3644133408642989636961859)
                  ·
                    refine ⟨5466200112964484455442789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3644133408642989636961859 5466200112964484455442789)
                    ·
                      refine ⟨1024912521180840835395523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5466200112964484455442789 1024912521180840835395523)
                      ·
                        rfl

theorem cell23_1996010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1996010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996010 prefixEnd_1996010 := by exact prefixLift 1996010
  have htrace : WordTrace (prefixWord ++ tailWord_1996010) baseStart_1996010 baseEnd_1996010 := by
    simpa [prefixWord, tailWord_1996010, baseEnd_1996010] using wordTrace_append hprefix tailTrace_1996010
  have hstable : (prefixWord ++ tailWord_1996010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996010).length < 2 ^ (prefixWord ++ tailWord_1996010).sum := by decide
  have hdescent : baseEnd_1996010 < baseStart_1996010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996053 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_1996053 : Nat := 118140960795 + 1996053 * 2 ^ 59
def prefixEnd_1996053 : Nat := 4983230072969 + 3 ^ 40 * 1996053 * 2
def baseEnd_1996053 : Nat := 1024934600848984167157825

theorem tailTrace_1996053 : CollatzResearch.WordTrace tailWord_1996053 prefixEnd_1996053 1024934600848984167157825 := by
  unfold tailWord_1996053
  simp only [CollatzResearch.WordTrace]
  refine ⟨72802033837648354557176813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48534689225098903038117875 72802033837648354557176813)
  ·
    refine ⟨27300762689118132958941305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72802033837648354557176813 27300762689118132958941305)
    ·
      refine ⟨20475572016838599719205979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27300762689118132958941305 20475572016838599719205979)
      ·
        refine ⟨30713358025257899578808969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20475572016838599719205979 30713358025257899578808969)
        ·
          refine ⟨23035018518943424684106727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30713358025257899578808969 23035018518943424684106727)
          ·
            refine ⟨34552527778415137026160091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23035018518943424684106727 34552527778415137026160091)
            ·
              refine ⟨51828791667622705539240137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34552527778415137026160091 51828791667622705539240137)
              ·
                refine ⟨38871593750717029154430103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51828791667622705539240137 38871593750717029154430103)
                ·
                  refine ⟨58307390626075543731645155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38871593750717029154430103 58307390626075543731645155)
                  ·
                    refine ⟨87461085939113315597467733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58307390626075543731645155 87461085939113315597467733)
                    ·
                      refine ⟨1024934600848984167157825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 87461085939113315597467733 1024934600848984167157825)
                      ·
                        rfl

theorem cell23_1996053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_1996053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996053 prefixEnd_1996053 := by exact prefixLift 1996053
  have htrace : WordTrace (prefixWord ++ tailWord_1996053) baseStart_1996053 baseEnd_1996053 := by
    simpa [prefixWord, tailWord_1996053, baseEnd_1996053] using wordTrace_append hprefix tailTrace_1996053
  have hstable : (prefixWord ++ tailWord_1996053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996053).length < 2 ^ (prefixWord ++ tailWord_1996053).sum := by decide
  have hdescent : baseEnd_1996053 < baseStart_1996053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996094 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_1996094 : Nat := 118140960795 + 1996094 * 2 ^ 59
def prefixEnd_1996094 : Nat := 4983230072969 + 3 ^ 40 * 1996094 * 2
def baseEnd_1996094 : Nat := 1024955653555818506745137

theorem tailTrace_1996094 : CollatzResearch.WordTrace tailWord_1996094 prefixEnd_1996094 1024955653555818506745137 := by
  unfold tailWord_1996094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9100441153812477319927417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48535686153666545706279557 9100441153812477319927417)
  ·
    refine ⟨6825330865359357989945563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9100441153812477319927417 6825330865359357989945563)
    ·
      refine ⟨10237996298039036984918345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6825330865359357989945563 10237996298039036984918345)
      ·
        refine ⟨7678497223529277738688759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10237996298039036984918345 7678497223529277738688759)
        ·
          refine ⟨11517745835293916608033139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7678497223529277738688759 11517745835293916608033139)
          ·
            refine ⟨17276618752940874912049709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11517745835293916608033139 17276618752940874912049709)
            ·
              refine ⟨6478732032352828092018641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17276618752940874912049709 6478732032352828092018641)
              ·
                refine ⟨4859049024264621069013981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6478732032352828092018641 4859049024264621069013981)
                ·
                  refine ⟨1822143384099232900880243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4859049024264621069013981 1822143384099232900880243)
                  ·
                    refine ⟨2733215076148849351320365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1822143384099232900880243 2733215076148849351320365)
                    ·
                      refine ⟨1024955653555818506745137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2733215076148849351320365 1024955653555818506745137)
                      ·
                        rfl

theorem cell23_1996094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_1996094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996094 prefixEnd_1996094 := by exact prefixLift 1996094
  have htrace : WordTrace (prefixWord ++ tailWord_1996094) baseStart_1996094 baseEnd_1996094 := by
    simpa [prefixWord, tailWord_1996094, baseEnd_1996094] using wordTrace_append hprefix tailTrace_1996094
  have hstable : (prefixWord ++ tailWord_1996094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996094).length < 2 ^ (prefixWord ++ tailWord_1996094).sum := by decide
  have hdescent : baseEnd_1996094 < baseStart_1996094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996097 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 3, 5]
def baseStart_1996097 : Nat := 118140960795 + 1996097 * 2 ^ 59
def prefixEnd_1996097 : Nat := 4983230072969 + 3 ^ 40 * 1996097 * 2
def baseEnd_1996097 : Nat := 341652397999260665002541

theorem tailTrace_1996097 : CollatzResearch.WordTrace tailWord_1996097 prefixEnd_1996097 341652397999260665002541 := by
  unfold tailWord_1996097
  simp only [CollatzResearch.WordTrace]
  refine ⟨72803638649488950071778545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48535759099659300047852363 72803638649488950071778545)
  ·
    refine ⟨54602728987116712553833909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72803638649488950071778545 54602728987116712553833909)
    ·
      refine ⟨5119005842542191801921929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54602728987116712553833909 5119005842542191801921929)
      ·
        refine ⟨3839254381906643851441447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5119005842542191801921929 3839254381906643851441447)
        ·
          refine ⟨5758881572859965777162171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3839254381906643851441447 5758881572859965777162171)
          ·
            refine ⟨8638322359289948665743257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5758881572859965777162171 8638322359289948665743257)
            ·
              refine ⟨6478741769467461499307443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8638322359289948665743257 6478741769467461499307443)
              ·
                refine ⟨9718112654201192248961165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6478741769467461499307443 9718112654201192248961165)
                ·
                  refine ⟨3644292245325447093360437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9718112654201192248961165 3644292245325447093360437)
                  ·
                    refine ⟨341652397999260665002541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3644292245325447093360437 341652397999260665002541)
                    ·
                      rfl

theorem cell23_1996097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_1996097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996097 prefixEnd_1996097 := by exact prefixLift 1996097
  have htrace : WordTrace (prefixWord ++ tailWord_1996097) baseStart_1996097 baseEnd_1996097 := by
    simpa [prefixWord, tailWord_1996097, baseEnd_1996097] using wordTrace_append hprefix tailTrace_1996097
  have hstable : (prefixWord ++ tailWord_1996097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996097).length < 2 ^ (prefixWord ++ tailWord_1996097).sum := by decide
  have hdescent : baseEnd_1996097 < baseStart_1996097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996110 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_1996110 : Nat := 118140960795 + 1996110 * 2 ^ 59
def prefixEnd_1996110 : Nat := 4983230072969 + 3 ^ 40 * 1996110 * 2
def baseEnd_1996110 : Nat := 341654623082096814715021

theorem tailTrace_1996110 : CollatzResearch.WordTrace tailWord_1996110 prefixEnd_1996110 341654623082096814715021 := by
  unfold tailWord_1996110
  simp only [CollatzResearch.WordTrace]
  refine ⟨9100514099805231661500223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48536075198961235528001189 9100514099805231661500223)
  ·
    refine ⟨13650771149707847492250335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9100514099805231661500223 13650771149707847492250335)
    ·
      refine ⟨20476156724561771238375503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13650771149707847492250335 20476156724561771238375503)
      ·
        refine ⟨30714235086842656857563255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20476156724561771238375503 30714235086842656857563255)
        ·
          refine ⟨46071352630263985286344883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30714235086842656857563255 46071352630263985286344883)
          ·
            refine ⟨69107028945395977929517325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46071352630263985286344883 69107028945395977929517325)
            ·
              refine ⟨25915135854523491723568997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69107028945395977929517325 25915135854523491723568997)
              ·
                refine ⟨4859087972723154698169187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25915135854523491723568997 4859087972723154698169187)
                ·
                  refine ⟨7288631959084732047253781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4859087972723154698169187 7288631959084732047253781)
                  ·
                    refine ⟨341654623082096814715021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7288631959084732047253781 341654623082096814715021)
                    ·
                      rfl

theorem cell23_1996110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_1996110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996110 prefixEnd_1996110 := by exact prefixLift 1996110
  have htrace : WordTrace (prefixWord ++ tailWord_1996110) baseStart_1996110 baseEnd_1996110 := by
    simpa [prefixWord, tailWord_1996110, baseEnd_1996110] using wordTrace_append hprefix tailTrace_1996110
  have hstable : (prefixWord ++ tailWord_1996110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996110).length < 2 ^ (prefixWord ++ tailWord_1996110).sum := by decide
  have hdescent : baseEnd_1996110 < baseStart_1996110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996120 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 1, 1, 5]
def baseStart_1996120 : Nat := 118140960795 + 1996120 * 2 ^ 59
def prefixEnd_1996120 : Nat := 4983230072969 + 3 ^ 40 * 1996120 * 2
def baseEnd_1996120 : Nat := 1024969004052835405020017

theorem tailTrace_1996120 : CollatzResearch.WordTrace tailWord_1996120 prefixEnd_1996120 1024969004052835405020017 := by
  unfold tailWord_1996120
  simp only [CollatzResearch.WordTrace]
  refine ⟨36402238764202812499932907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48536318352270416666577209 36402238764202812499932907)
  ·
    refine ⟨54603358146304218749899361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36402238764202812499932907 54603358146304218749899361)
    ·
      refine ⟨40952518609728164062424521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54603358146304218749899361 40952518609728164062424521)
      ·
        refine ⟨30714388957296123046818391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40952518609728164062424521 30714388957296123046818391)
        ·
          refine ⟨46071583435944184570227587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30714388957296123046818391 46071583435944184570227587)
          ·
            refine ⟨69107375153916276855341381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46071583435944184570227587 69107375153916276855341381)
            ·
              refine ⟨12957632841359301910376509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69107375153916276855341381 12957632841359301910376509)
              ·
                refine ⟨4859112315509738216391191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12957632841359301910376509 4859112315509738216391191)
                ·
                  refine ⟨7288668473264607324586787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4859112315509738216391191 7288668473264607324586787)
                  ·
                    refine ⟨10933002709896910986880181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7288668473264607324586787 10933002709896910986880181)
                    ·
                      refine ⟨1024969004052835405020017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10933002709896910986880181 1024969004052835405020017)
                      ·
                        rfl

theorem cell23_1996120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_1996120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996120 prefixEnd_1996120 := by exact prefixLift 1996120
  have htrace : WordTrace (prefixWord ++ tailWord_1996120) baseStart_1996120 baseEnd_1996120 := by
    simpa [prefixWord, tailWord_1996120, baseEnd_1996120] using wordTrace_append hprefix tailTrace_1996120
  have hstable : (prefixWord ++ tailWord_1996120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996120).length < 2 ^ (prefixWord ++ tailWord_1996120).sum := by decide
  have hdescent : baseEnd_1996120 < baseStart_1996120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996144 : List Nat := [2, 1, 1, 1, 4, 2, 5, 1, 2, 4]
def baseStart_1996144 : Nat := 118140960795 + 1996144 * 2 ^ 59
def prefixEnd_1996144 : Nat := 4983230072969 + 3 ^ 40 * 1996144 * 2
def baseEnd_1996144 : Nat := 341660442529514437039969

theorem tailTrace_1996144 : CollatzResearch.WordTrace tailWord_1996144 prefixEnd_1996144 341660442529514437039969 := by
  unfold tailWord_1996144
  simp only [CollatzResearch.WordTrace]
  refine ⟨36402676440159338549369743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48536901920212451399159657 36402676440159338549369743)
  ·
    refine ⟨54604014660239007824054615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36402676440159338549369743 54604014660239007824054615)
    ·
      refine ⟨81906021990358511736081923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54604014660239007824054615 81906021990358511736081923)
      ·
        refine ⟨122859032985537767604122885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81906021990358511736081923 122859032985537767604122885)
        ·
          refine ⟨23036068684788331425773041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122859032985537767604122885 23036068684788331425773041)
          ·
            refine ⟨17277051513591248569329781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23036068684788331425773041 17277051513591248569329781)
            ·
              refine ⟨1619723579399179553374667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17277051513591248569329781 1619723579399179553374667)
              ·
                refine ⟨2429585369098769330062001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1619723579399179553374667 2429585369098769330062001)
                ·
                  refine ⟨1822189026824076997546501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2429585369098769330062001 1822189026824076997546501)
                  ·
                    refine ⟨341660442529514437039969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1822189026824076997546501 341660442529514437039969)
                    ·
                      rfl

theorem cell23_1996144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 2, 4].length) (baseStart_1996144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996144 prefixEnd_1996144 := by exact prefixLift 1996144
  have htrace : WordTrace (prefixWord ++ tailWord_1996144) baseStart_1996144 baseEnd_1996144 := by
    simpa [prefixWord, tailWord_1996144, baseEnd_1996144] using wordTrace_append hprefix tailTrace_1996144
  have hstable : (prefixWord ++ tailWord_1996144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996144).length < 2 ^ (prefixWord ++ tailWord_1996144).sum := by decide
  have hdescent : baseEnd_1996144 < baseStart_1996144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996168 : List Nat := [2, 1, 3, 3, 1, 2, 3, 3, 1, 2, 2]
def baseStart_1996168 : Nat := 118140960795 + 1996168 * 2 ^ 59
def prefixEnd_1996168 : Nat := 4983230072969 + 3 ^ 40 * 1996168 * 2
def baseEnd_1996168 : Nat := 1024993651124251217219797

theorem tailTrace_1996168 : CollatzResearch.WordTrace tailWord_1996168 prefixEnd_1996168 1024993651124251217219797 := by
  unfold tailWord_1996168
  simp only [CollatzResearch.WordTrace]
  refine ⟨36403114116115864598806579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48537485488154486131742105 36403114116115864598806579)
  ·
    refine ⟨54604671174173796898209869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36403114116115864598806579 54604671174173796898209869)
    ·
      refine ⟨20476751690315173836828701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54604671174173796898209869 20476751690315173836828701)
      ·
        refine ⟨7678781883868190188810763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20476751690315173836828701 7678781883868190188810763)
        ·
          refine ⟨11518172825802285283216145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7678781883868190188810763 11518172825802285283216145)
          ·
            refine ⟨8638629619351713962412109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11518172825802285283216145 8638629619351713962412109)
            ·
              refine ⟨3239486107256892735904541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8638629619351713962412109 3239486107256892735904541)
              ·
                refine ⟨1214807290221334775964203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3239486107256892735904541 1214807290221334775964203)
                ·
                  refine ⟨1822210935332002163946305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1214807290221334775964203 1822210935332002163946305)
                  ·
                    refine ⟨1366658201499001622959729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1822210935332002163946305 1366658201499001622959729)
                    ·
                      refine ⟨1024993651124251217219797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1366658201499001622959729 1024993651124251217219797)
                      ·
                        rfl

theorem cell23_1996168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_1996168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996168 prefixEnd_1996168 := by exact prefixLift 1996168
  have htrace : WordTrace (prefixWord ++ tailWord_1996168) baseStart_1996168 baseEnd_1996168 := by
    simpa [prefixWord, tailWord_1996168, baseEnd_1996168] using wordTrace_append hprefix tailTrace_1996168
  have hstable : (prefixWord ++ tailWord_1996168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996168).length < 2 ^ (prefixWord ++ tailWord_1996168).sum := by decide
  have hdescent : baseEnd_1996168 < baseStart_1996168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996174 : List Nat := [4, 1, 1, 4, 3, 1, 9]
def baseStart_1996174 : Nat := 118140960795 + 1996174 * 2 ^ 59
def prefixEnd_1996174 : Nat := 4983230072969 + 3 ^ 40 * 1996174 * 2
def baseEnd_1996174 : Nat := 12654280642076273996849

theorem tailTrace_1996174 : CollatzResearch.WordTrace tailWord_1996174 prefixEnd_1996174 12654280642076273996849 := by
  unfold tailWord_1996174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9100805883776249027791447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48537631380139994814887717 9100805883776249027791447)
  ·
    refine ⟨13651208825664373541687171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9100805883776249027791447 13651208825664373541687171)
    ·
      refine ⟨20476813238496560312530757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13651208825664373541687171 20476813238496560312530757)
      ·
        refine ⟨3839402482218105058599517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20476813238496560312530757 3839402482218105058599517)
        ·
          refine ⟨1439775930831789396974819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3839402482218105058599517 1439775930831789396974819)
          ·
            refine ⟨2159663896247684095462229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439775930831789396974819 2159663896247684095462229)
            ·
              refine ⟨12654280642076273996849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2159663896247684095462229 12654280642076273996849)
              ·
                rfl

theorem cell23_1996174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 9].length) (baseStart_1996174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996174 prefixEnd_1996174 := by exact prefixLift 1996174
  have htrace : WordTrace (prefixWord ++ tailWord_1996174) baseStart_1996174 baseEnd_1996174 := by
    simpa [prefixWord, tailWord_1996174, baseEnd_1996174] using wordTrace_append hprefix tailTrace_1996174
  have hstable : (prefixWord ++ tailWord_1996174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996174).length < 2 ^ (prefixWord ++ tailWord_1996174).sum := by decide
  have hdescent : baseEnd_1996174 < baseStart_1996174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996207 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 5, 4, 2]
def baseStart_1996207 : Nat := 118140960795 + 1996207 * 2 ^ 59
def prefixEnd_1996207 : Nat := 4983230072969 + 3 ^ 40 * 1996207 * 2
def baseEnd_1996207 : Nat := 1025013676869776564632117

theorem tailTrace_1996207 : CollatzResearch.WordTrace tailWord_1996207 prefixEnd_1996207 1025013676869776564632117 := by
  unfold tailWord_1996207
  simp only [CollatzResearch.WordTrace]
  refine ⟨72807650679090438858282875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48538433786060292572188583 72807650679090438858282875)
  ·
    refine ⟨109211476018635658287424313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72807650679090438858282875 109211476018635658287424313)
    ·
      refine ⟨81908607013976743715568235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109211476018635658287424313 81908607013976743715568235)
      ·
        refine ⟨122862910520965115573352353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81908607013976743715568235 122862910520965115573352353)
        ·
          refine ⟨92147182890723836680014265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122862910520965115573352353 92147182890723836680014265)
          ·
            refine ⟨69110387168042877510010699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92147182890723836680014265 69110387168042877510010699)
            ·
              refine ⟨103665580752064316265016049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69110387168042877510010699 103665580752064316265016049)
              ·
                refine ⟨77749185564048237198762037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103665580752064316265016049 77749185564048237198762037)
                ·
                  refine ⟨7288986146629522237383941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77749185564048237198762037 7288986146629522237383941)
                  ·
                    refine ⟨1366684902493035419509489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7288986146629522237383941 1366684902493035419509489)
                    ·
                      refine ⟨1025013676869776564632117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1366684902493035419509489 1025013676869776564632117)
                      ·
                        rfl

theorem cell23_1996207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 4, 2].length) (baseStart_1996207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996207 prefixEnd_1996207 := by exact prefixLift 1996207
  have htrace : WordTrace (prefixWord ++ tailWord_1996207) baseStart_1996207 baseEnd_1996207 := by
    simpa [prefixWord, tailWord_1996207, baseEnd_1996207] using wordTrace_append hprefix tailTrace_1996207
  have hstable : (prefixWord ++ tailWord_1996207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996207).length < 2 ^ (prefixWord ++ tailWord_1996207).sum := by decide
  have hdescent : baseEnd_1996207 < baseStart_1996207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996224 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 6, 2, 2]
def baseStart_1996224 : Nat := 118140960795 + 1996224 * 2 ^ 59
def prefixEnd_1996224 : Nat := 4983230072969 + 3 ^ 40 * 1996224 * 2
def baseEnd_1996224 : Nat := 1025022406040902998119539

theorem tailTrace_1996224 : CollatzResearch.WordTrace tailWord_1996224 prefixEnd_1996224 1025022406040902998119539 := by
  unfold tailWord_1996224
  simp only [CollatzResearch.WordTrace]
  refine ⟨36404135360014425380825863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48538847146685900507767817 36404135360014425380825863)
  ·
    refine ⟨54606203040021638071238795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36404135360014425380825863 54606203040021638071238795)
    ·
      refine ⟨81909304560032457106858193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54606203040021638071238795 81909304560032457106858193)
      ·
        refine ⟨61431978420024342830143645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81909304560032457106858193 61431978420024342830143645)
        ·
          refine ⟨23036991907509128561303867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61431978420024342830143645 23036991907509128561303867)
          ·
            refine ⟨34555487861263692841955801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23036991907509128561303867 34555487861263692841955801)
            ·
              refine ⟨25916615895947769631466851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34555487861263692841955801 25916615895947769631466851)
              ·
                refine ⟨38874923843921654447200277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25916615895947769631466851 38874923843921654447200277)
                ·
                  refine ⟨1822262055183827552212513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38874923843921654447200277 1822262055183827552212513)
                  ·
                    refine ⟨1366696541387870664159385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1822262055183827552212513 1366696541387870664159385)
                    ·
                      refine ⟨1025022406040902998119539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1366696541387870664159385 1025022406040902998119539)
                      ·
                        rfl

theorem cell23_1996224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 6, 2, 2].length) (baseStart_1996224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996224 prefixEnd_1996224 := by exact prefixLift 1996224
  have htrace : WordTrace (prefixWord ++ tailWord_1996224) baseStart_1996224 baseEnd_1996224 := by
    simpa [prefixWord, tailWord_1996224, baseEnd_1996224] using wordTrace_append hprefix tailTrace_1996224
  have hstable : (prefixWord ++ tailWord_1996224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996224).length < 2 ^ (prefixWord ++ tailWord_1996224).sum := by decide
  have hdescent : baseEnd_1996224 < baseStart_1996224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996257 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_1996257 : Nat := 118140960795 + 1996257 * 2 ^ 59
def prefixEnd_1996257 : Nat := 4983230072969 + 3 ^ 40 * 1996257 * 2
def baseEnd_1996257 : Nat := 1025039350902501369006887

theorem tailTrace_1996257 : CollatzResearch.WordTrace tailWord_1996257 prefixEnd_1996257 1025039350902501369006887 := by
  unfold tailWord_1996257
  simp only [CollatzResearch.WordTrace]
  refine ⟨72809474328909297397603025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48539649552606198265068683 72809474328909297397603025)
  ·
    refine ⟨54607105746681973048202269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72809474328909297397603025 54607105746681973048202269)
    ·
      refine ⟨20477664655005739893075851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54607105746681973048202269 20477664655005739893075851)
      ·
        refine ⟨30716496982508609839613777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20477664655005739893075851 30716496982508609839613777)
        ·
          refine ⟨23037372736881457379710333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30716496982508609839613777 23037372736881457379710333)
          ·
            refine ⟨8639014776330546517391375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23037372736881457379710333 8639014776330546517391375)
            ·
              refine ⟨12958522164495819776087063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8639014776330546517391375 12958522164495819776087063)
              ·
                refine ⟨19437783246743729664130595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12958522164495819776087063 19437783246743729664130595)
                ·
                  refine ⟨29156674870115594496195893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19437783246743729664130595 29156674870115594496195893)
                  ·
                    refine ⟨2733438269073336984018365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29156674870115594496195893 2733438269073336984018365)
                    ·
                      refine ⟨1025039350902501369006887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2733438269073336984018365 1025039350902501369006887)
                      ·
                        rfl

theorem cell23_1996257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_1996257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996257 prefixEnd_1996257 := by exact prefixLift 1996257
  have htrace : WordTrace (prefixWord ++ tailWord_1996257) baseStart_1996257 baseEnd_1996257 := by
    simpa [prefixWord, tailWord_1996257, baseEnd_1996257] using wordTrace_append hprefix tailTrace_1996257
  have hstable : (prefixWord ++ tailWord_1996257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996257).length < 2 ^ (prefixWord ++ tailWord_1996257).sum := by decide
  have hdescent : baseEnd_1996257 < baseStart_1996257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996292 : List Nat := [2, 3, 2, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_1996292 : Nat := 118140960795 + 1996292 * 2 ^ 59
def prefixEnd_1996292 : Nat := 4983230072969 + 3 ^ 40 * 1996292 * 2
def baseEnd_1996292 : Nat := 1025057322725408732069227

theorem tailTrace_1996292 : CollatzResearch.WordTrace tailWord_1996292 prefixEnd_1996292 1025057322725408732069227 := by
  unfold tailWord_1996292
  simp only [CollatzResearch.WordTrace]
  refine ⟨36405375441891249187563565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48540500589188332250084753 36405375441891249187563565)
  ·
    refine ⟨13652015790709218445336337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36405375441891249187563565 13652015790709218445336337)
    ·
      refine ⟨10239011843031913834002253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13652015790709218445336337 10239011843031913834002253)
      ·
        refine ⟨3839629441136967687750845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10239011843031913834002253 3839629441136967687750845)
        ·
          refine ⟨1439861040426362882906567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3839629441136967687750845 1439861040426362882906567)
          ·
            refine ⟨2159791560639544324359851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439861040426362882906567 2159791560639544324359851)
            ·
              refine ⟨3239687340959316486539777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159791560639544324359851 3239687340959316486539777)
              ·
                refine ⟨2429765505719487364904833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3239687340959316486539777 2429765505719487364904833)
                ·
                  refine ⟨1822324129289615523678625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2429765505719487364904833 1822324129289615523678625)
                  ·
                    refine ⟨1366743096967211642758969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1822324129289615523678625 1366743096967211642758969)
                    ·
                      refine ⟨1025057322725408732069227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1366743096967211642758969 1025057322725408732069227)
                      ·
                        rfl

theorem cell23_1996292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_1996292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996292 prefixEnd_1996292 := by exact prefixLift 1996292
  have htrace : WordTrace (prefixWord ++ tailWord_1996292) baseStart_1996292 baseEnd_1996292 := by
    simpa [prefixWord, tailWord_1996292, baseEnd_1996292] using wordTrace_append hprefix tailTrace_1996292
  have hstable : (prefixWord ++ tailWord_1996292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996292).length < 2 ^ (prefixWord ++ tailWord_1996292).sum := by decide
  have hdescent : baseEnd_1996292 < baseStart_1996292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996297 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 4, 1, 4]
def baseStart_1996297 : Nat := 118140960795 + 1996297 * 2 ^ 59
def prefixEnd_1996297 : Nat := 4983230072969 + 3 ^ 40 * 1996297 * 2
def baseEnd_1996297 : Nat := 1025059890128681212506703

theorem tailTrace_1996297 : CollatzResearch.WordTrace tailWord_1996297 prefixEnd_1996297 1025059890128681212506703 := by
  unfold tailWord_1996297
  simp only [CollatzResearch.WordTrace]
  refine ⟨72810933248764384229059145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48540622165842922819372763 72810933248764384229059145)
  ·
    refine ⟨54608199936573288171794359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72810933248764384229059145 54608199936573288171794359)
    ·
      refine ⟨81912299904859932257691539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54608199936573288171794359 81912299904859932257691539)
      ·
        refine ⟨122868449857289898386537309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81912299904859932257691539 122868449857289898386537309)
        ·
          refine ⟨46075668696483711894951491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122868449857289898386537309 46075668696483711894951491)
          ·
            refine ⟨69113503044725567842427237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46075668696483711894951491 69113503044725567842427237)
            ·
              refine ⟨12958781820886043970455107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69113503044725567842427237 12958781820886043970455107)
              ·
                refine ⟨19438172731329065955682661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12958781820886043970455107 19438172731329065955682661)
                ·
                  refine ⟨3644657387124199866690499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19438172731329065955682661 3644657387124199866690499)
                  ·
                    refine ⟨5466986080686299800035749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3644657387124199866690499 5466986080686299800035749)
                    ·
                      refine ⟨1025059890128681212506703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5466986080686299800035749 1025059890128681212506703)
                      ·
                        rfl

theorem cell23_1996297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_1996297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996297 prefixEnd_1996297 := by exact prefixLift 1996297
  have htrace : WordTrace (prefixWord ++ tailWord_1996297) baseStart_1996297 baseEnd_1996297 := by
    simpa [prefixWord, tailWord_1996297, baseEnd_1996297] using wordTrace_append hprefix tailTrace_1996297
  have hstable : (prefixWord ++ tailWord_1996297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996297).length < 2 ^ (prefixWord ++ tailWord_1996297).sum := by decide
  have hdescent : baseEnd_1996297 < baseStart_1996297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996367 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 3, 5]
def baseStart_1996367 : Nat := 118140960795 + 1996367 * 2 ^ 59
def prefixEnd_1996367 : Nat := 4983230072969 + 3 ^ 40 * 1996367 * 2
def baseEnd_1996367 : Nat := 341698611258165312877127

theorem tailTrace_1996367 : CollatzResearch.WordTrace tailWord_1996367 prefixEnd_1996367 341698611258165312877127 := by
  unfold tailWord_1996367
  simp only [CollatzResearch.WordTrace]
  refine ⟨72813486358510786184107355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48542324239007190789404903 72813486358510786184107355)
  ·
    refine ⟨109220229537766179276161033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72813486358510786184107355 109220229537766179276161033)
    ·
      refine ⟨81915172153324634457120775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109220229537766179276161033 81915172153324634457120775)
      ·
        refine ⟨122872758229986951685681163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81915172153324634457120775 122872758229986951685681163)
        ·
          refine ⟨184309137344980427528521745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122872758229986951685681163 184309137344980427528521745)
          ·
            refine ⟨138231853008735320646391309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184309137344980427528521745 138231853008735320646391309)
            ·
              refine ⟨51836944878275745242396741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138231853008735320646391309 51836944878275745242396741)
              ·
                refine ⟨9719427164676702232949389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51836944878275745242396741 9719427164676702232949389)
                ·
                  refine ⟨3644785186753763337356021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9719427164676702232949389 3644785186753763337356021)
                  ·
                    refine ⟨341698611258165312877127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3644785186753763337356021 341698611258165312877127)
                    ·
                      rfl

theorem cell23_1996367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 5].length) (baseStart_1996367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996367 prefixEnd_1996367 := by exact prefixLift 1996367
  have htrace : WordTrace (prefixWord ++ tailWord_1996367) baseStart_1996367 baseEnd_1996367 := by
    simpa [prefixWord, tailWord_1996367, baseEnd_1996367] using wordTrace_append hprefix tailTrace_1996367
  have hstable : (prefixWord ++ tailWord_1996367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996367).length < 2 ^ (prefixWord ++ tailWord_1996367).sum := by decide
  have hdescent : baseEnd_1996367 < baseStart_1996367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996391 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_1996391 : Nat := 118140960795 + 1996391 * 2 ^ 59
def prefixEnd_1996391 : Nat := 4983230072969 + 3 ^ 40 * 1996391 * 2
def baseEnd_1996391 : Nat := 1025108157310203844731271

theorem tailTrace_1996391 : CollatzResearch.WordTrace tailWord_1996391 prefixEnd_1996391 1025108157310203844731271 := by
  unfold tailWord_1996391
  simp only [CollatzResearch.WordTrace]
  refine ⟨72814361710423838282981027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48542907806949225521987351 72814361710423838282981027)
  ·
    refine ⟨109221542565635757424471541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72814361710423838282981027 109221542565635757424471541)
    ·
      refine ⟨10239519615528352258544207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109221542565635757424471541 10239519615528352258544207)
      ·
        refine ⟨15359279423292528387816311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10239519615528352258544207 15359279423292528387816311)
        ·
          refine ⟨23038919134938792581724467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15359279423292528387816311 23038919134938792581724467)
          ·
            refine ⟨34558378702408188872586701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23038919134938792581724467 34558378702408188872586701)
            ·
              refine ⟨12959392013403070827220013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34558378702408188872586701 12959392013403070827220013)
              ·
                refine ⟨4859772005026151560207505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12959392013403070827220013 4859772005026151560207505)
                ·
                  refine ⟨3644829003769613670155629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4859772005026151560207505 3644829003769613670155629)
                  ·
                    refine ⟨1366810876413605126308361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3644829003769613670155629 1366810876413605126308361)
                    ·
                      refine ⟨1025108157310203844731271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1366810876413605126308361 1025108157310203844731271)
                      ·
                        rfl

theorem cell23_1996391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_1996391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996391 prefixEnd_1996391 := by exact prefixLift 1996391
  have htrace : WordTrace (prefixWord ++ tailWord_1996391) baseStart_1996391 baseEnd_1996391 := by
    simpa [prefixWord, tailWord_1996391, baseEnd_1996391] using wordTrace_append hprefix tailTrace_1996391
  have hstable : (prefixWord ++ tailWord_1996391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996391).length < 2 ^ (prefixWord ++ tailWord_1996391).sum := by decide
  have hdescent : baseEnd_1996391 < baseStart_1996391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996437 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_1996437 : Nat := 118140960795 + 1996437 * 2 ^ 59
def prefixEnd_1996437 : Nat := 4983230072969 + 3 ^ 40 * 1996437 * 2
def baseEnd_1996437 : Nat := 1025131777420310664756059

theorem tailTrace_1996437 : CollatzResearch.WordTrace tailWord_1996437 prefixEnd_1996437 1025131777420310664756059 := by
  unfold tailWord_1996437
  simp only [CollatzResearch.WordTrace]
  refine ⟨72816039468257188139155565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48544026312171458759437043 72816039468257188139155565)
  ·
    refine ⟨27306014800596445552183337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72816039468257188139155565 27306014800596445552183337)
    ·
      refine ⟨20479511100447334164137503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27306014800596445552183337 20479511100447334164137503)
      ·
        refine ⟨30719266650671001246206255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20479511100447334164137503 30719266650671001246206255)
        ·
          refine ⟨46078899976006501869309383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30719266650671001246206255 46078899976006501869309383)
          ·
            refine ⟨69118349964009752803964075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46078899976006501869309383 69118349964009752803964075)
            ·
              refine ⟨103677524946014629205946113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69118349964009752803964075 103677524946014629205946113)
              ·
                refine ⟨77758143709510971904459585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103677524946014629205946113 77758143709510971904459585)
                ·
                  refine ⟨58318607782133228928344689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77758143709510971904459585 58318607782133228928344689)
                  ·
                    refine ⟨43738955836599921696258517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58318607782133228928344689 43738955836599921696258517)
                    ·
                      refine ⟨1025131777420310664756059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43738955836599921696258517 1025131777420310664756059)
                      ·
                        rfl

theorem cell23_1996437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_1996437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996437 prefixEnd_1996437 := by exact prefixLift 1996437
  have htrace : WordTrace (prefixWord ++ tailWord_1996437) baseStart_1996437 baseEnd_1996437 := by
    simpa [prefixWord, tailWord_1996437, baseEnd_1996437] using wordTrace_append hprefix tailTrace_1996437
  have hstable : (prefixWord ++ tailWord_1996437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996437).length < 2 ^ (prefixWord ++ tailWord_1996437).sum := by decide
  have hdescent : baseEnd_1996437 < baseStart_1996437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996482 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_1996482 : Nat := 118140960795 + 1996482 * 2 ^ 59
def prefixEnd_1996482 : Nat := 4983230072969 + 3 ^ 40 * 1996482 * 2
def baseEnd_1996482 : Nat := 341718294683254329564451

theorem tailTrace_1996482 : CollatzResearch.WordTrace tailWord_1996482 prefixEnd_1996482 341718294683254329564451 := by
  unfold tailWord_1996482
  simp only [CollatzResearch.WordTrace]
  refine ⟨18204420188273540206135925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48545120502062773883029133 18204420188273540206135925)
  ·
    refine ⟨1706664392650644394325243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18204420188273540206135925 1706664392650644394325243)
    ·
      refine ⟨2559996588975966591487865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1706664392650644394325243 2559996588975966591487865)
      ·
        refine ⟨1919997441731974943615899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2559996588975966591487865 1919997441731974943615899)
        ·
          refine ⟨2879996162597962415423849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919997441731974943615899 2879996162597962415423849)
          ·
            refine ⟨2159997121948471811567887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2879996162597962415423849 2159997121948471811567887)
            ·
              refine ⟨3239995682922707717351831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159997121948471811567887 3239995682922707717351831)
              ·
                refine ⟨4859993524384061576027747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239995682922707717351831 4859993524384061576027747)
                ·
                  refine ⟨7289990286576092364041621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4859993524384061576027747 7289990286576092364041621)
                  ·
                    refine ⟨341718294683254329564451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7289990286576092364041621 341718294683254329564451)
                    ·
                      rfl

theorem cell23_1996482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_1996482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996482 prefixEnd_1996482 := by exact prefixLift 1996482
  have htrace : WordTrace (prefixWord ++ tailWord_1996482) baseStart_1996482 baseEnd_1996482 := by
    simpa [prefixWord, tailWord_1996482, baseEnd_1996482] using wordTrace_append hprefix tailTrace_1996482
  have hstable : (prefixWord ++ tailWord_1996482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996482).length < 2 ^ (prefixWord ++ tailWord_1996482).sum := by decide
  have hdescent : baseEnd_1996482 < baseStart_1996482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996511 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 3, 4, 2]
def baseStart_1996511 : Nat := 118140960795 + 1996511 * 2 ^ 59
def prefixEnd_1996511 : Nat := 4983230072969 + 3 ^ 40 * 1996511 * 2
def baseEnd_1996511 : Nat := 1025169774988743375230719

theorem tailTrace_1996511 : CollatzResearch.WordTrace tailWord_1996511 prefixEnd_1996511 1025169774988743375230719 := by
  unfold tailWord_1996511
  simp only [CollatzResearch.WordTrace]
  refine ⟨72818738469989098777349387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48545825646659399184899591 72818738469989098777349387)
  ·
    refine ⟨109228107704983648166024081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72818738469989098777349387 109228107704983648166024081)
    ·
      refine ⟨81921080778737736124518061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109228107704983648166024081 81921080778737736124518061)
      ·
        refine ⟨30720405292026651046694273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81921080778737736124518061 30720405292026651046694273)
        ·
          refine ⟨23040303969019988285020705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30720405292026651046694273 23040303969019988285020705)
          ·
            refine ⟨17280227976764991213765529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23040303969019988285020705 17280227976764991213765529)
            ·
              refine ⟨12960170982573743410324147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17280227976764991213765529 12960170982573743410324147)
              ·
                refine ⟨19440256473860615115486221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12960170982573743410324147 19440256473860615115486221)
                ·
                  refine ⟨7290096177697730668307333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19440256473860615115486221 7290096177697730668307333)
                  ·
                    refine ⟨1366893033318324500307625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7290096177697730668307333 1366893033318324500307625)
                    ·
                      refine ⟨1025169774988743375230719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1366893033318324500307625 1025169774988743375230719)
                      ·
                        rfl

theorem cell23_1996511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_1996511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996511 prefixEnd_1996511 := by exact prefixLift 1996511
  have htrace : WordTrace (prefixWord ++ tailWord_1996511) baseStart_1996511 baseEnd_1996511 := by
    simpa [prefixWord, tailWord_1996511, baseEnd_1996511] using wordTrace_append hprefix tailTrace_1996511
  have hstable : (prefixWord ++ tailWord_1996511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996511).length < 2 ^ (prefixWord ++ tailWord_1996511).sum := by decide
  have hdescent : baseEnd_1996511 < baseStart_1996511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996524 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_1996524 : Nat := 118140960795 + 1996524 * 2 ^ 59
def prefixEnd_1996524 : Nat := 4983230072969 + 3 ^ 40 * 1996524 * 2
def baseEnd_1996524 : Nat := 1025176450237251824368159

theorem tailTrace_1996524 : CollatzResearch.WordTrace tailWord_1996524 prefixEnd_1996524 1025176450237251824368159 := by
  unfold tailWord_1996524
  simp only [CollatzResearch.WordTrace]
  refine ⟨36409606309471000998786313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48546141745961334665048417 36409606309471000998786313)
  ·
    refine ⟨27307204732103250749089735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36409606309471000998786313 27307204732103250749089735)
    ·
      refine ⟨40960807098154876123634603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27307204732103250749089735 40960807098154876123634603)
      ·
        refine ⟨61441210647232314185451905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40960807098154876123634603 61441210647232314185451905)
        ·
          refine ⟨46080907985424235639088929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61441210647232314185451905 46080907985424235639088929)
          ·
            refine ⟨34560680989068176729316697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46080907985424235639088929 34560680989068176729316697)
            ·
              refine ⟨25920510741801132546987523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34560680989068176729316697 25920510741801132546987523)
              ·
                refine ⟨38880766112701698820481285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25920510741801132546987523 38880766112701698820481285)
                ·
                  refine ⟨7290143646131568528840241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38880766112701698820481285 7290143646131568528840241)
                  ·
                    refine ⟨5467607734598676396630181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7290143646131568528840241 5467607734598676396630181)
                    ·
                      refine ⟨1025176450237251824368159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5467607734598676396630181 1025176450237251824368159)
                      ·
                        rfl

theorem cell23_1996524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_1996524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996524 prefixEnd_1996524 := by exact prefixLift 1996524
  have htrace : WordTrace (prefixWord ++ tailWord_1996524) baseStart_1996524 baseEnd_1996524 := by
    simpa [prefixWord, tailWord_1996524, baseEnd_1996524] using wordTrace_append hprefix tailTrace_1996524
  have hstable : (prefixWord ++ tailWord_1996524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996524).length < 2 ^ (prefixWord ++ tailWord_1996524).sum := by decide
  have hdescent : baseEnd_1996524 < baseStart_1996524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996581 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 2, 5]
def baseStart_1996581 : Nat := 118140960795 + 1996581 * 2 ^ 59
def prefixEnd_1996581 : Nat := 4983230072969 + 3 ^ 40 * 1996581 * 2
def baseEnd_1996581 : Nat := 341735239544852700451799

theorem tailTrace_1996581 : CollatzResearch.WordTrace tailWord_1996581 prefixEnd_1996581 341735239544852700451799 := by
  unfold tailWord_1996581
  simp only [CollatzResearch.WordTrace]
  refine ⟨72821291579735500732397597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48547527719823667154931731 72821291579735500732397597)
  ·
    refine ⟨27307984342400812774649099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72821291579735500732397597 27307984342400812774649099)
    ·
      refine ⟨40961976513601219161973649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27307984342400812774649099 40961976513601219161973649)
      ·
        refine ⟨30721482385200914371480237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40961976513601219161973649 30721482385200914371480237)
        ·
          refine ⟨11520555894450342889305089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30721482385200914371480237 11520555894450342889305089)
          ·
            refine ⟨8640416920837757166978817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11520555894450342889305089 8640416920837757166978817)
            ·
              refine ⟨6480312690628317875234113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8640416920837757166978817 6480312690628317875234113)
              ·
                refine ⟨4860234517971238406425585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6480312690628317875234113 4860234517971238406425585)
                ·
                  refine ⟨3645175888478428804819189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4860234517971238406425585 3645175888478428804819189)
                  ·
                    refine ⟨341735239544852700451799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3645175888478428804819189 341735239544852700451799)
                    ·
                      rfl

theorem cell23_1996581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_1996581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996581 prefixEnd_1996581 := by exact prefixLift 1996581
  have htrace : WordTrace (prefixWord ++ tailWord_1996581) baseStart_1996581 baseEnd_1996581 := by
    simpa [prefixWord, tailWord_1996581, baseEnd_1996581] using wordTrace_append hprefix tailTrace_1996581
  have hstable : (prefixWord ++ tailWord_1996581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996581).length < 2 ^ (prefixWord ++ tailWord_1996581).sum := by decide
  have hdescent : baseEnd_1996581 < baseStart_1996581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996611 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 5, 4]
def baseStart_1996611 : Nat := 118140960795 + 1996611 * 2 ^ 59
def prefixEnd_1996611 : Nat := 4983230072969 + 3 ^ 40 * 1996611 * 2
def baseEnd_1996611 : Nat := 341740374351397661326753

theorem tailTrace_1996611 : CollatzResearch.WordTrace tailWord_1996611 prefixEnd_1996611 341740374351397661326753 := by
  unfold tailWord_1996611
  simp only [CollatzResearch.WordTrace]
  refine ⟨72822385769626815855989687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48548257179751210570659791 72822385769626815855989687)
  ·
    refine ⟨109233578654440223783984531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72822385769626815855989687 109233578654440223783984531)
    ·
      refine ⟨163850367981660335675976797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109233578654440223783984531 163850367981660335675976797)
      ·
        refine ⟨61443887993122625878491299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163850367981660335675976797 61443887993122625878491299)
        ·
          refine ⟨92165831989683938817736949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61443887993122625878491299 92165831989683938817736949)
          ·
            refine ⟨8640546749032869264162839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92165831989683938817736949 8640546749032869264162839)
            ·
              refine ⟨12960820123549303896244259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8640546749032869264162839 12960820123549303896244259)
              ·
                refine ⟨19441230185323955844366389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12960820123549303896244259 19441230185323955844366389)
                ·
                  refine ⟨1822615329874120860409349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19441230185323955844366389 1822615329874120860409349)
                  ·
                    refine ⟨341740374351397661326753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1822615329874120860409349 341740374351397661326753)
                    ·
                      rfl

theorem cell23_1996611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 4].length) (baseStart_1996611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996611 prefixEnd_1996611 := by exact prefixLift 1996611
  have htrace : WordTrace (prefixWord ++ tailWord_1996611) baseStart_1996611 baseEnd_1996611 := by
    simpa [prefixWord, tailWord_1996611, baseEnd_1996611] using wordTrace_append hprefix tailTrace_1996611
  have hstable : (prefixWord ++ tailWord_1996611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996611).length < 2 ^ (prefixWord ++ tailWord_1996611).sum := by decide
  have hdescent : baseEnd_1996611 < baseStart_1996611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996624 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 8]
def baseStart_1996624 : Nat := 118140960795 + 1996624 * 2 ^ 59
def prefixEnd_1996624 : Nat := 4983230072969 + 3 ^ 40 * 1996624 * 2
def baseEnd_1996624 : Nat := 113914199811411270346411

theorem tailTrace_1996624 : CollatzResearch.WordTrace tailWord_1996624 prefixEnd_1996624 113914199811411270346411 := by
  unfold tailWord_1996624
  simp only [CollatzResearch.WordTrace]
  refine ⟨36411429959289859538106463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48548573279053146050808617 36411429959289859538106463)
  ·
    refine ⟨54617144938934789307159695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36411429959289859538106463 54617144938934789307159695)
    ·
      refine ⟨81925717408402183960739543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54617144938934789307159695 81925717408402183960739543)
      ·
        refine ⟨122888576112603275941109315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81925717408402183960739543 122888576112603275941109315)
        ·
          refine ⟨184332864168904913911663973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122888576112603275941109315 184332864168904913911663973)
          ·
            refine ⟨34562412031669671358436995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184332864168904913911663973 34562412031669671358436995)
            ·
              refine ⟨51843618047504507037655493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34562412031669671358436995 51843618047504507037655493)
              ·
                refine ⟨9720678383907095069560405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51843618047504507037655493 9720678383907095069560405)
                ·
                  refine ⟨113914199811411270346411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9720678383907095069560405 113914199811411270346411)
                  ·
                    rfl

theorem cell23_1996624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 8].length) (baseStart_1996624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996624 prefixEnd_1996624 := by exact prefixLift 1996624
  have htrace : WordTrace (prefixWord ++ tailWord_1996624) baseStart_1996624 baseEnd_1996624 := by
    simpa [prefixWord, tailWord_1996624, baseEnd_1996624] using wordTrace_append hprefix tailTrace_1996624
  have hstable : (prefixWord ++ tailWord_1996624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996624).length < 2 ^ (prefixWord ++ tailWord_1996624).sum := by decide
  have hdescent : baseEnd_1996624 < baseStart_1996624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996661 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1996661 : Nat := 118140960795 + 1996661 * 2 ^ 59
def prefixEnd_1996661 : Nat := 4983230072969 + 3 ^ 40 * 1996661 * 2
def baseEnd_1996661 : Nat := 1025246797086917788355029

theorem tailTrace_1996661 : CollatzResearch.WordTrace tailWord_1996661 prefixEnd_1996661 1025246797086917788355029 := by
  unfold tailWord_1996661
  simp only [CollatzResearch.WordTrace]
  refine ⟨72824209419445674395309837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48549472946297116263539891 72824209419445674395309837)
  ·
    refine ⟨27309078532292127898241189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72824209419445674395309837 27309078532292127898241189)
    ·
      refine ⟨5120452224804773980920223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27309078532292127898241189 5120452224804773980920223)
      ·
        refine ⟨7680678337207160971380335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5120452224804773980920223 7680678337207160971380335)
        ·
          refine ⟨11521017505810741457070503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7680678337207160971380335 11521017505810741457070503)
          ·
            refine ⟨17281526258716112185605755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11521017505810741457070503 17281526258716112185605755)
            ·
              refine ⟨25922289388074168278408633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17281526258716112185605755 25922289388074168278408633)
              ·
                refine ⟨19441717041055626208806475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25922289388074168278408633 19441717041055626208806475)
                ·
                  refine ⟨29162575561583439313209713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19441717041055626208806475 29162575561583439313209713)
                  ·
                    refine ⟨21871931671187579484907285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29162575561583439313209713 21871931671187579484907285)
                    ·
                      refine ⟨1025246797086917788355029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21871931671187579484907285 1025246797086917788355029)
                      ·
                        rfl

theorem cell23_1996661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1996661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996661 prefixEnd_1996661 := by exact prefixLift 1996661
  have htrace : WordTrace (prefixWord ++ tailWord_1996661) baseStart_1996661 baseEnd_1996661 := by
    simpa [prefixWord, tailWord_1996661, baseEnd_1996661] using wordTrace_append hprefix tailTrace_1996661
  have hstable : (prefixWord ++ tailWord_1996661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996661).length < 2 ^ (prefixWord ++ tailWord_1996661).sum := by decide
  have hdescent : baseEnd_1996661 < baseStart_1996661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996679 : List Nat := [1, 1, 4, 2, 5, 1, 1, 3, 1, 4]
def baseStart_1996679 : Nat := 118140960795 + 1996679 * 2 ^ 59
def prefixEnd_1996679 : Nat := 4983230072969 + 3 ^ 40 * 1996679 * 2
def baseEnd_1996679 : Nat := 341752013246232905976649

theorem tailTrace_1996679 : CollatzResearch.WordTrace tailWord_1996679 prefixEnd_1996679 341752013246232905976649 := by
  unfold tailWord_1996679
  simp only [CollatzResearch.WordTrace]
  refine ⟨72824865933380463469465091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48549910622253642312976727 72824865933380463469465091)
  ·
    refine ⟨109237298900070695204197637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72824865933380463469465091 109237298900070695204197637)
    ·
      refine ⟨20481993543763255350787057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109237298900070695204197637 20481993543763255350787057)
      ·
        refine ⟨15361495157822441513090293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20481993543763255350787057 15361495157822441513090293)
        ·
          refine ⟨1440140171045853891852215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15361495157822441513090293 1440140171045853891852215)
          ·
            refine ⟨2160210256568780837778323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440140171045853891852215 2160210256568780837778323)
            ·
              refine ⟨3240315384853171256667485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160210256568780837778323 3240315384853171256667485)
              ·
                refine ⟨1215118269319939221250307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3240315384853171256667485 1215118269319939221250307)
                ·
                  refine ⟨1822677403979908831875461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1215118269319939221250307 1822677403979908831875461)
                  ·
                    refine ⟨341752013246232905976649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1822677403979908831875461 341752013246232905976649)
                    ·
                      rfl

theorem cell23_1996679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_1996679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996679 prefixEnd_1996679 := by exact prefixLift 1996679
  have htrace : WordTrace (prefixWord ++ tailWord_1996679) baseStart_1996679 baseEnd_1996679 := by
    simpa [prefixWord, tailWord_1996679, baseEnd_1996679] using wordTrace_append hprefix tailTrace_1996679
  have hstable : (prefixWord ++ tailWord_1996679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996679).length < 2 ^ (prefixWord ++ tailWord_1996679).sum := by decide
  have hdescent : baseEnd_1996679 < baseStart_1996679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996695 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 2, 3, 2]
def baseStart_1996695 : Nat := 118140960795 + 1996695 * 2 ^ 59
def prefixEnd_1996695 : Nat := 4983230072969 + 3 ^ 40 * 1996695 * 2
def baseEnd_1996695 : Nat := 1025264255429170655329873

theorem tailTrace_1996695 : CollatzResearch.WordTrace tailWord_1996695 prefixEnd_1996695 1025264255429170655329873 := by
  unfold tailWord_1996695
  simp only [CollatzResearch.WordTrace]
  refine ⟨72825449501322498202047539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48550299667548332134698359 72825449501322498202047539)
  ·
    refine ⟨109238174251983747303071309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72825449501322498202047539 109238174251983747303071309)
    ·
      refine ⟨40964315344493905238651741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109238174251983747303071309 40964315344493905238651741)
      ·
        refine ⟨15361618254185214464494403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40964315344493905238651741 15361618254185214464494403)
        ·
          refine ⟨23042427381277821696741605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15361618254185214464494403 23042427381277821696741605)
          ·
            refine ⟨4320455133989591568139051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23042427381277821696741605 4320455133989591568139051)
            ·
              refine ⟨6480682700984387352208577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320455133989591568139051 6480682700984387352208577)
              ·
                refine ⟨4860512025738290514156433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6480682700984387352208577 4860512025738290514156433)
                ·
                  refine ⟨3645384019303717885617325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4860512025738290514156433 3645384019303717885617325)
                  ·
                    refine ⟨1367019007238894207106497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3645384019303717885617325 1367019007238894207106497)
                    ·
                      refine ⟨1025264255429170655329873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1367019007238894207106497 1025264255429170655329873)
                      ·
                        rfl

theorem cell23_1996695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_1996695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996695 prefixEnd_1996695 := by exact prefixLift 1996695
  have htrace : WordTrace (prefixWord ++ tailWord_1996695) baseStart_1996695 baseEnd_1996695 := by
    simpa [prefixWord, tailWord_1996695, baseEnd_1996695] using wordTrace_append hprefix tailTrace_1996695
  have hstable : (prefixWord ++ tailWord_1996695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996695).length < 2 ^ (prefixWord ++ tailWord_1996695).sum := by decide
  have hdescent : baseEnd_1996695 < baseStart_1996695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996725 : List Nat := [1, 3, 3, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_1996725 : Nat := 118140960795 + 1996725 * 2 ^ 59
def prefixEnd_1996725 : Nat := 4983230072969 + 3 ^ 40 * 1996725 * 2
def baseEnd_1996725 : Nat := 1025279659848805537954735

theorem tailTrace_1996725 : CollatzResearch.WordTrace tailWord_1996725 prefixEnd_1996725 1025279659848805537954735 := by
  unfold tailWord_1996725
  simp only [CollatzResearch.WordTrace]
  refine ⟨72826543691213813325639629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48551029127475875550426419 72826543691213813325639629)
  ·
    refine ⟨27309953884205179997114861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72826543691213813325639629 27309953884205179997114861)
    ·
      refine ⟨10241232706576942498918073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27309953884205179997114861 10241232706576942498918073)
      ·
        refine ⟨7680924529932706874188555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10241232706576942498918073 7680924529932706874188555)
        ·
          refine ⟨11521386794899060311282833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7680924529932706874188555 11521386794899060311282833)
          ·
            refine ⟨8641040096174295233462125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11521386794899060311282833 8641040096174295233462125)
            ·
              refine ⟨3240390036065360712548297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8641040096174295233462125 3240390036065360712548297)
              ·
                refine ⟨2430292527049020534411223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3240390036065360712548297 2430292527049020534411223)
                ·
                  refine ⟨3645438790573530801616835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430292527049020534411223 3645438790573530801616835)
                  ·
                    refine ⟨5468158185860296202425253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3645438790573530801616835 5468158185860296202425253)
                    ·
                      refine ⟨1025279659848805537954735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5468158185860296202425253 1025279659848805537954735)
                      ·
                        rfl

theorem cell23_1996725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_1996725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996725 prefixEnd_1996725 := by exact prefixLift 1996725
  have htrace : WordTrace (prefixWord ++ tailWord_1996725) baseStart_1996725 baseEnd_1996725 := by
    simpa [prefixWord, tailWord_1996725, baseEnd_1996725] using wordTrace_append hprefix tailTrace_1996725
  have hstable : (prefixWord ++ tailWord_1996725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996725).length < 2 ^ (prefixWord ++ tailWord_1996725).sum := by decide
  have hdescent : baseEnd_1996725 < baseStart_1996725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996728 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 3, 2, 3]
def baseStart_1996728 : Nat := 118140960795 + 1996728 * 2 ^ 59
def prefixEnd_1996728 : Nat := 4983230072969 + 3 ^ 40 * 1996728 * 2
def baseEnd_1996728 : Nat := 1025281200290769026217221

theorem tailTrace_1996728 : CollatzResearch.WordTrace tailWord_1996728 prefixEnd_1996728 1025281200290769026217221 := by
  unfold tailWord_1996728
  simp only [CollatzResearch.WordTrace]
  refine ⟨36413326555101472418999419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48551102073468629891999225 36413326555101472418999419)
  ·
    refine ⟨54619989832652208628499129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36413326555101472418999419 54619989832652208628499129)
    ·
      refine ⟨40964992374489156471374347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54619989832652208628499129 40964992374489156471374347)
      ·
        refine ⟨61447488561733734707061521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40964992374489156471374347 61447488561733734707061521)
        ·
          refine ⟨46085616421300301030296141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61447488561733734707061521 46085616421300301030296141)
          ·
            refine ⟨17282106157987612886361053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46085616421300301030296141 17282106157987612886361053)
            ·
              refine ⟨6480789809245354832385395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17282106157987612886361053 6480789809245354832385395)
              ·
                refine ⟨9721184713868032248578093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6480789809245354832385395 9721184713868032248578093)
                ·
                  refine ⟨3645444267700512093216785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9721184713868032248578093 3645444267700512093216785)
                  ·
                    refine ⟨2734083200775384069912589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3645444267700512093216785 2734083200775384069912589)
                    ·
                      refine ⟨1025281200290769026217221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2734083200775384069912589 1025281200290769026217221)
                      ·
                        rfl

theorem cell23_1996728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_1996728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996728 prefixEnd_1996728 := by exact prefixLift 1996728
  have htrace : WordTrace (prefixWord ++ tailWord_1996728) baseStart_1996728 baseEnd_1996728 := by
    simpa [prefixWord, tailWord_1996728, baseEnd_1996728] using wordTrace_append hprefix tailTrace_1996728
  have hstable : (prefixWord ++ tailWord_1996728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996728).length < 2 ^ (prefixWord ++ tailWord_1996728).sum := by decide
  have hdescent : baseEnd_1996728 < baseStart_1996728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996765 : List Nat := [1, 4, 3, 1, 3, 2, 1, 8]
def baseStart_1996765 : Nat := 118140960795 + 1996765 * 2 ^ 59
def prefixEnd_1996765 : Nat := 4983230072969 + 3 ^ 40 * 1996765 * 2
def baseEnd_1996765 : Nat := 37974081447221680794613

theorem tailTrace_1996765 : CollatzResearch.WordTrace tailWord_1996765 prefixEnd_1996765 37974081447221680794613 := by
  unfold tailWord_1996765
  simp only [CollatzResearch.WordTrace]
  refine ⟨72828002611068900157095749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48552001740712600104730499 72828002611068900157095749)
  ·
    refine ⟨13655250489575418779455453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72828002611068900157095749 13655250489575418779455453)
    ·
      refine ⟨5120718933590782042295795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13655250489575418779455453 5120718933590782042295795)
      ·
        refine ⟨7681078400386173063443693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5120718933590782042295795 7681078400386173063443693)
        ·
          refine ⟨2880404400144814898791385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7681078400386173063443693 2880404400144814898791385)
          ·
            refine ⟨2160303300108611174093539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2880404400144814898791385 2160303300108611174093539)
            ·
              refine ⟨3240454950162916761140309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160303300108611174093539 3240454950162916761140309)
              ·
                refine ⟨37974081447221680794613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3240454950162916761140309 37974081447221680794613)
                ·
                  rfl

theorem cell23_1996765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 8].length) (baseStart_1996765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996765 prefixEnd_1996765 := by exact prefixLift 1996765
  have htrace : WordTrace (prefixWord ++ tailWord_1996765) baseStart_1996765 baseEnd_1996765 := by
    simpa [prefixWord, tailWord_1996765, baseEnd_1996765] using wordTrace_append hprefix tailTrace_1996765
  have hstable : (prefixWord ++ tailWord_1996765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996765).length < 2 ^ (prefixWord ++ tailWord_1996765).sum := by decide
  have hdescent : baseEnd_1996765 < baseStart_1996765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996841 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 6]
def baseStart_1996841 : Nat := 118140960795 + 1996841 * 2 ^ 59
def prefixEnd_1996841 : Nat := 4983230072969 + 3 ^ 40 * 1996841 * 2
def baseEnd_1996841 : Nat := 1025339223604727084104201

theorem tailTrace_1996841 : CollatzResearch.WordTrace tailWord_1996841 prefixEnd_1996841 1025339223604727084104201 := by
  unfold tailWord_1996841
  simp only [CollatzResearch.WordTrace]
  refine ⟨72830774558793565136862377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48553849705862376757908251 72830774558793565136862377)
  ·
    refine ⟨54623080919095173852646783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72830774558793565136862377 54623080919095173852646783)
    ·
      refine ⟨81934621378642760778970175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54623080919095173852646783 81934621378642760778970175)
      ·
        refine ⟨122901932067964141168455263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81934621378642760778970175 122901932067964141168455263)
        ·
          refine ⟨184352898101946211752682895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122901932067964141168455263 184352898101946211752682895)
          ·
            refine ⟨276529347152919317629024343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184352898101946211752682895 276529347152919317629024343)
            ·
              refine ⟨414794020729378976443536515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276529347152919317629024343 414794020729378976443536515)
              ·
                refine ⟨622191031094068464665304773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414794020729378976443536515 622191031094068464665304773)
                ·
                  refine ⟨116660818330137837124744645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622191031094068464665304773 116660818330137837124744645)
                  ·
                    refine ⟨21873903436900844460889621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116660818330137837124744645 21873903436900844460889621)
                    ·
                      refine ⟨1025339223604727084104201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21873903436900844460889621 1025339223604727084104201)
                      ·
                        rfl

theorem cell23_1996841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_1996841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996841 prefixEnd_1996841 := by exact prefixLift 1996841
  have htrace : WordTrace (prefixWord ++ tailWord_1996841) baseStart_1996841 baseEnd_1996841 := by
    simpa [prefixWord, tailWord_1996841, baseEnd_1996841] using wordTrace_append hprefix tailTrace_1996841
  have hstable : (prefixWord ++ tailWord_1996841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996841).length < 2 ^ (prefixWord ++ tailWord_1996841).sum := by decide
  have hdescent : baseEnd_1996841 < baseStart_1996841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996852 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1996852 : Nat := 118140960795 + 1996852 * 2 ^ 59
def prefixEnd_1996852 : Nat := 4983230072969 + 3 ^ 40 * 1996852 * 2
def baseEnd_1996852 : Nat := 1025344871891926541066651

theorem tailTrace_1996852 : CollatzResearch.WordTrace tailWord_1996852 prefixEnd_1996852 1025344871891926541066651 := by
  unfold tailWord_1996852
  simp only [CollatzResearch.WordTrace]
  refine ⟨36415587880876857007756405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48554117174502476010341873 36415587880876857007756405)
  ·
    refine ⟨3413961363832205344477163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36415587880876857007756405 3413961363832205344477163)
    ·
      refine ⟨5120942045748308016715745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3413961363832205344477163 5120942045748308016715745)
      ·
        refine ⟨3840706534311231012536809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5120942045748308016715745 3840706534311231012536809)
        ·
          refine ⟨2880529900733423259402607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3840706534311231012536809 2880529900733423259402607)
          ·
            refine ⟨4320794851100134889103911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880529900733423259402607 4320794851100134889103911)
            ·
              refine ⟨6481192276650202333655867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320794851100134889103911 6481192276650202333655867)
              ·
                refine ⟨9721788414975303500483801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6481192276650202333655867 9721788414975303500483801)
                ·
                  refine ⟨7291341311231477625362851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9721788414975303500483801 7291341311231477625362851)
                  ·
                    refine ⟨10937011966847216438044277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7291341311231477625362851 10937011966847216438044277)
                    ·
                      refine ⟨1025344871891926541066651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10937011966847216438044277 1025344871891926541066651)
                      ·
                        rfl

theorem cell23_1996852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1996852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996852 prefixEnd_1996852 := by exact prefixLift 1996852
  have htrace : WordTrace (prefixWord ++ tailWord_1996852) baseStart_1996852 baseEnd_1996852 := by
    simpa [prefixWord, tailWord_1996852, baseEnd_1996852] using wordTrace_append hprefix tailTrace_1996852
  have hstable : (prefixWord ++ tailWord_1996852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996852).length < 2 ^ (prefixWord ++ tailWord_1996852).sum := by decide
  have hdescent : baseEnd_1996852 < baseStart_1996852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996855 : List Nat := [1, 1, 3, 1, 2, 2, 5, 3, 5]
def baseStart_1996855 : Nat := 118140960795 + 1996855 * 2 ^ 59
def prefixEnd_1996855 : Nat := 4983230072969 + 3 ^ 40 * 1996855 * 2
def baseEnd_1996855 : Nat := 113927379148210003258793

theorem tailTrace_1996855 : CollatzResearch.WordTrace tailWord_1996855 prefixEnd_1996855 113927379148210003258793 := by
  unfold tailWord_1996855
  simp only [CollatzResearch.WordTrace]
  refine ⟨72831285180742845527872019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48554190120495230351914679 72831285180742845527872019)
  ·
    refine ⟨109246927771114268291808029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72831285180742845527872019 109246927771114268291808029)
    ·
      refine ⟨40967597914167850609428011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109246927771114268291808029 40967597914167850609428011)
      ·
        refine ⟨61451396871251775914142017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40967597914167850609428011 61451396871251775914142017)
        ·
          refine ⟨46088547653438831935606513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61451396871251775914142017 46088547653438831935606513)
          ·
            refine ⟨34566410740079123951704885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46088547653438831935606513 34566410740079123951704885)
            ·
              refine ⟨3240601006882417870472333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34566410740079123951704885 3240601006882417870472333)
              ·
                refine ⟨1215225377580906701427125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3240601006882417870472333 1215225377580906701427125)
                ·
                  refine ⟨113927379148210003258793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1215225377580906701427125 113927379148210003258793)
                  ·
                    rfl

theorem cell23_1996855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 5].length) (baseStart_1996855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996855 prefixEnd_1996855 := by exact prefixLift 1996855
  have htrace : WordTrace (prefixWord ++ tailWord_1996855) baseStart_1996855 baseEnd_1996855 := by
    simpa [prefixWord, tailWord_1996855, baseEnd_1996855] using wordTrace_append hprefix tailTrace_1996855
  have hstable : (prefixWord ++ tailWord_1996855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996855).length < 2 ^ (prefixWord ++ tailWord_1996855).sum := by decide
  have hdescent : baseEnd_1996855 < baseStart_1996855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996878 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_1996878 : Nat := 118140960795 + 1996878 * 2 ^ 59
def prefixEnd_1996878 : Nat := 4983230072969 + 3 ^ 40 * 1996878 * 2
def baseEnd_1996878 : Nat := 1025358222388943439341531

theorem tailTrace_1996878 : CollatzResearch.WordTrace tailWord_1996878 prefixEnd_1996878 1025358222388943439341531 := by
  unfold tailWord_1996878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9104015507457440056994911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48554749373106346970639525 9104015507457440056994911)
  ·
    refine ⟨13656023261186160085492367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9104015507457440056994911 13656023261186160085492367)
    ·
      refine ⟨20484034891779240128238551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13656023261186160085492367 20484034891779240128238551)
      ·
        refine ⟨30726052337668860192357827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20484034891779240128238551 30726052337668860192357827)
        ·
          refine ⟨46089078506503290288536741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30726052337668860192357827 46089078506503290288536741)
          ·
            refine ⟨8641702219969366929100639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46089078506503290288536741 8641702219969366929100639)
            ·
              refine ⟨12962553329954050393650959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8641702219969366929100639 12962553329954050393650959)
              ·
                refine ⟨19443829994931075590476439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12962553329954050393650959 19443829994931075590476439)
                ·
                  refine ⟨29165744992396613385714659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19443829994931075590476439 29165744992396613385714659)
                  ·
                    refine ⟨43748617488594920078571989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29165744992396613385714659 43748617488594920078571989)
                    ·
                      refine ⟨1025358222388943439341531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43748617488594920078571989 1025358222388943439341531)
                      ·
                        rfl

theorem cell23_1996878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_1996878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996878 prefixEnd_1996878 := by exact prefixLift 1996878
  have htrace : WordTrace (prefixWord ++ tailWord_1996878) baseStart_1996878 baseEnd_1996878 := by
    simpa [prefixWord, tailWord_1996878, baseEnd_1996878] using wordTrace_append hprefix tailTrace_1996878
  have hstable : (prefixWord ++ tailWord_1996878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996878).length < 2 ^ (prefixWord ++ tailWord_1996878).sum := by decide
  have hdescent : baseEnd_1996878 < baseStart_1996878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996905 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 2, 1, 4]
def baseStart_1996905 : Nat := 118140960795 + 1996905 * 2 ^ 59
def prefixEnd_1996905 : Nat := 4983230072969 + 3 ^ 40 * 1996905 * 2
def baseEnd_1996905 : Nat := 1025372086366614833703907

theorem tailTrace_1996905 : CollatzResearch.WordTrace tailWord_1996905 prefixEnd_1996905 1025372086366614833703907 := by
  unfold tailWord_1996905
  simp only [CollatzResearch.WordTrace]
  refine ⟨72833108830561704067192169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48555405887041136044794779 72833108830561704067192169)
  ·
    refine ⟨54624831622921278050394127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72833108830561704067192169 54624831622921278050394127)
    ·
      refine ⟨81937247434381917075591191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54624831622921278050394127 81937247434381917075591191)
      ·
        refine ⟨122905871151572875613386787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81937247434381917075591191 122905871151572875613386787)
        ·
          refine ⟨184358806727359313420080181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122905871151572875613386787 184358806727359313420080181)
          ·
            refine ⟨17283638130689935633132517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184358806727359313420080181 17283638130689935633132517)
            ·
              refine ⟨3240682149504362931212347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17283638130689935633132517 3240682149504362931212347)
              ·
                refine ⟨4861023224256544396818521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240682149504362931212347 4861023224256544396818521)
                ·
                  refine ⟨3645767418192408297613891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4861023224256544396818521 3645767418192408297613891)
                  ·
                    refine ⟨5468651127288612446420837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3645767418192408297613891 5468651127288612446420837)
                    ·
                      refine ⟨1025372086366614833703907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5468651127288612446420837 1025372086366614833703907)
                      ·
                        rfl

theorem cell23_1996905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 1, 4].length) (baseStart_1996905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996905 prefixEnd_1996905 := by exact prefixLift 1996905
  have htrace : WordTrace (prefixWord ++ tailWord_1996905) baseStart_1996905 baseEnd_1996905 := by
    simpa [prefixWord, tailWord_1996905, baseEnd_1996905] using wordTrace_append hprefix tailTrace_1996905
  have hstable : (prefixWord ++ tailWord_1996905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996905).length < 2 ^ (prefixWord ++ tailWord_1996905).sum := by decide
  have hdescent : baseEnd_1996905 < baseStart_1996905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996959 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1996959 : Nat := 118140960795 + 1996959 * 2 ^ 59
def prefixEnd_1996959 : Nat := 4983230072969 + 3 ^ 40 * 1996959 * 2
def baseEnd_1996959 : Nat := 1025399814321957622428659

theorem tailTrace_1996959 : CollatzResearch.WordTrace tailWord_1996959 prefixEnd_1996959 1025399814321957622428659 := by
  unfold tailWord_1996959
  simp only [CollatzResearch.WordTrace]
  refine ⟨72835078372366071289657931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48556718914910714193105287 72835078372366071289657931)
  ·
    refine ⟨109252617558549106934486897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72835078372366071289657931 109252617558549106934486897)
    ·
      refine ⟨81939463168911830200865173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109252617558549106934486897 81939463168911830200865173)
      ·
        refine ⟨3840912336042742040665555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81939463168911830200865173 3840912336042742040665555)
        ·
          refine ⟨5761368504064113060998333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3840912336042742040665555 5761368504064113060998333)
          ·
            refine ⟨2160513189024042397874375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5761368504064113060998333 2160513189024042397874375)
            ·
              refine ⟨3240769783536063596811563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160513189024042397874375 3240769783536063596811563)
              ·
                refine ⟨4861154675304095395217345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240769783536063596811563 4861154675304095395217345)
                ·
                  refine ⟨3645866006478071546413009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4861154675304095395217345 3645866006478071546413009)
                  ·
                    refine ⟨2734399504858553659809757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3645866006478071546413009 2734399504858553659809757)
                    ·
                      refine ⟨1025399814321957622428659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2734399504858553659809757 1025399814321957622428659)
                      ·
                        rfl

theorem cell23_1996959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1996959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1996959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1996959 prefixEnd_1996959 := by exact prefixLift 1996959
  have htrace : WordTrace (prefixWord ++ tailWord_1996959) baseStart_1996959 baseEnd_1996959 := by
    simpa [prefixWord, tailWord_1996959, baseEnd_1996959] using wordTrace_append hprefix tailTrace_1996959
  have hstable : (prefixWord ++ tailWord_1996959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996959).length < 2 ^ (prefixWord ++ tailWord_1996959).sum := by decide
  have hdescent : baseEnd_1996959 < baseStart_1996959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997025 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_1997025 : Nat := 118140960795 + 1997025 * 2 ^ 59
def prefixEnd_1997025 : Nat := 4983230072969 + 3 ^ 40 * 1997025 * 2
def baseEnd_1997025 : Nat := 1025433704045154364203355

theorem tailTrace_1997025 : CollatzResearch.WordTrace tailWord_1997025 prefixEnd_1997025 1025433704045154364203355 := by
  unfold tailWord_1997025
  simp only [CollatzResearch.WordTrace]
  refine ⟨72837485590126964561560529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48558323726751309707707019 72837485590126964561560529)
  ·
    refine ⟨54628114192595223421170397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72837485590126964561560529 54628114192595223421170397)
    ·
      refine ⟨20485542822223208782938899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54628114192595223421170397 20485542822223208782938899)
      ·
        refine ⟨30728314233334813174408349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20485542822223208782938899 30728314233334813174408349)
        ·
          refine ⟨11523117837500554940403131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30728314233334813174408349 11523117837500554940403131)
          ·
            refine ⟨17284676756250832410604697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11523117837500554940403131 17284676756250832410604697)
            ·
              refine ⟨12963507567188124307953523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17284676756250832410604697 12963507567188124307953523)
              ·
                refine ⟨19445261350782186461930285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12963507567188124307953523 19445261350782186461930285)
                ·
                  refine ⟨7291973006543319923223857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19445261350782186461930285 7291973006543319923223857)
                  ·
                    refine ⟨5468979754907489942417893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7291973006543319923223857 5468979754907489942417893)
                    ·
                      refine ⟨1025433704045154364203355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5468979754907489942417893 1025433704045154364203355)
                      ·
                        rfl

theorem cell23_1997025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_1997025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997025 prefixEnd_1997025 := by exact prefixLift 1997025
  have htrace : WordTrace (prefixWord ++ tailWord_1997025) baseStart_1997025 baseEnd_1997025 := by
    simpa [prefixWord, tailWord_1997025, baseEnd_1997025] using wordTrace_append hprefix tailTrace_1997025
  have hstable : (prefixWord ++ tailWord_1997025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997025).length < 2 ^ (prefixWord ++ tailWord_1997025).sum := by decide
  have hdescent : baseEnd_1997025 < baseStart_1997025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997032 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_1997032 : Nat := 118140960795 + 1997032 * 2 ^ 59
def prefixEnd_1997032 : Nat := 4983230072969 + 3 ^ 40 * 1997032 * 2
def baseEnd_1997032 : Nat := 1025437298409735836815823

theorem tailTrace_1997032 : CollatzResearch.WordTrace tailWord_1997032 prefixEnd_1997032 1025437298409735836815823 := by
  unfold tailWord_1997032
  simp only [CollatzResearch.WordTrace]
  refine ⟨36418870450550802378532675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48558493934067736504710233 36418870450550802378532675)
  ·
    refine ⟨54628305675826203567799013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36418870450550802378532675 54628305675826203567799013)
    ·
      refine ⟨10242807314217413168962315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54628305675826203567799013 10242807314217413168962315)
      ·
        refine ⟨15364210971326119753443473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10242807314217413168962315 15364210971326119753443473)
        ·
          refine ⟨11523158228494589815082605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15364210971326119753443473 11523158228494589815082605)
          ·
            refine ⟨4321184335685471180655977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11523158228494589815082605 4321184335685471180655977)
            ·
              refine ⟨3240888251764103385491983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4321184335685471180655977 3240888251764103385491983)
              ·
                refine ⟨4861332377646155078237975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240888251764103385491983 4861332377646155078237975)
                ·
                  refine ⟨7291998566469232617356963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861332377646155078237975 7291998566469232617356963)
                  ·
                    refine ⟨10937997849703848926035445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7291998566469232617356963 10937997849703848926035445)
                    ·
                      refine ⟨1025437298409735836815823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10937997849703848926035445 1025437298409735836815823)
                      ·
                        rfl

theorem cell23_1997032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_1997032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997032 prefixEnd_1997032 := by exact prefixLift 1997032
  have htrace : WordTrace (prefixWord ++ tailWord_1997032) baseStart_1997032 baseEnd_1997032 := by
    simpa [prefixWord, tailWord_1997032, baseEnd_1997032] using wordTrace_append hprefix tailTrace_1997032
  have hstable : (prefixWord ++ tailWord_1997032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997032).length < 2 ^ (prefixWord ++ tailWord_1997032).sum := by decide
  have hdescent : baseEnd_1997032 < baseStart_1997032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997046 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_1997046 : Nat := 118140960795 + 1997046 * 2 ^ 59
def prefixEnd_1997046 : Nat := 4983230072969 + 3 ^ 40 * 1997046 * 2
def baseEnd_1997046 : Nat := 1025444487138898782040759

theorem tailTrace_1997046 : CollatzResearch.WordTrace tailWord_1997046 prefixEnd_1997046 1025444487138898782040759 := by
  unfold tailWord_1997046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4552390720190680321754687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48558834348700590098716661 4552390720190680321754687)
  ·
    refine ⟨6828586080286020482632031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4552390720190680321754687 6828586080286020482632031)
    ·
      refine ⟨10242879120429030723948047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6828586080286020482632031 10242879120429030723948047)
      ·
        refine ⟨15364318680643546085922071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10242879120429030723948047 15364318680643546085922071)
        ·
          refine ⟨23046478020965319128883107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15364318680643546085922071 23046478020965319128883107)
          ·
            refine ⟨34569717031447978693324661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23046478020965319128883107 34569717031447978693324661)
            ·
              refine ⟨3240910971698248002499187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34569717031447978693324661 3240910971698248002499187)
              ·
                refine ⟨4861366457547372003748781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240910971698248002499187 4861366457547372003748781)
                ·
                  refine ⟨1823012421580264501405793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4861366457547372003748781 1823012421580264501405793)
                  ·
                    refine ⟨1367259316185198376054345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1823012421580264501405793 1367259316185198376054345)
                    ·
                      refine ⟨1025444487138898782040759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1367259316185198376054345 1025444487138898782040759)
                      ·
                        rfl

theorem cell23_1997046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_1997046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997046 prefixEnd_1997046 := by exact prefixLift 1997046
  have htrace : WordTrace (prefixWord ++ tailWord_1997046) baseStart_1997046 baseEnd_1997046 := by
    simpa [prefixWord, tailWord_1997046, baseEnd_1997046] using wordTrace_append hprefix tailTrace_1997046
  have hstable : (prefixWord ++ tailWord_1997046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997046).length < 2 ^ (prefixWord ++ tailWord_1997046).sum := by decide
  have hdescent : baseEnd_1997046 < baseStart_1997046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997063 : List Nat := [1, 1, 4, 5, 2, 1, 1, 2, 1, 1, 4]
def baseStart_1997063 : Nat := 118140960795 + 1997063 * 2 ^ 59
def prefixEnd_1997063 : Nat := 4983230072969 + 3 ^ 40 * 1997063 * 2
def baseEnd_1997063 : Nat := 1025453216310025215528181

theorem tailTrace_1997063 : CollatzResearch.WordTrace tailWord_1997063 prefixEnd_1997063 1025453216310025215528181 := by
  unfold tailWord_1997063
  simp only [CollatzResearch.WordTrace]
  refine ⟨72838871563989297051443843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48559247709326198034295895 72838871563989297051443843)
  ·
    refine ⟨109258307345983945577165765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72838871563989297051443843 109258307345983945577165765)
    ·
      refine ⟨20485932627371989795718581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109258307345983945577165765 20485932627371989795718581)
      ·
        refine ⟨1920556183816124043348617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20485932627371989795718581 1920556183816124043348617)
        ·
          refine ⟨1440417137862093032511463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1920556183816124043348617 1440417137862093032511463)
          ·
            refine ⟨2160625706793139548767195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440417137862093032511463 2160625706793139548767195)
            ·
              refine ⟨3240938560189709323150793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160625706793139548767195 3240938560189709323150793)
              ·
                refine ⟨2430703920142281992363095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3240938560189709323150793 2430703920142281992363095)
                ·
                  refine ⟨3646055880213422988544643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430703920142281992363095 3646055880213422988544643)
                  ·
                    refine ⟨5469083820320134482816965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3646055880213422988544643 5469083820320134482816965)
                    ·
                      refine ⟨1025453216310025215528181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5469083820320134482816965 1025453216310025215528181)
                      ·
                        rfl

theorem cell23_1997063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_1997063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997063 prefixEnd_1997063 := by exact prefixLift 1997063
  have htrace : WordTrace (prefixWord ++ tailWord_1997063) baseStart_1997063 baseEnd_1997063 := by
    simpa [prefixWord, tailWord_1997063, baseEnd_1997063] using wordTrace_append hprefix tailTrace_1997063
  have hstable : (prefixWord ++ tailWord_1997063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997063).length < 2 ^ (prefixWord ++ tailWord_1997063).sum := by decide
  have hdescent : baseEnd_1997063 < baseStart_1997063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997089 : List Nat := [1, 2, 3, 2, 1, 1, 2, 5, 1, 3, 2]
def baseStart_1997089 : Nat := 118140960795 + 1997089 * 2 ^ 59
def prefixEnd_1997089 : Nat := 4983230072969 + 3 ^ 40 * 1997089 * 2
def baseEnd_1997089 : Nat := 1025466566807042113803061

theorem tailTrace_1997089 : CollatzResearch.WordTrace tailWord_1997089 prefixEnd_1997089 1025466566807042113803061 := by
  unfold tailWord_1997089
  simp only [CollatzResearch.WordTrace]
  refine ⟨72839819861895103491890321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48559879907930068994593547 72839819861895103491890321)
  ·
    refine ⟨54629864896421327618917741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72839819861895103491890321 54629864896421327618917741)
    ·
      refine ⟨20486199336157997857094153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54629864896421327618917741 20486199336157997857094153)
      ·
        refine ⟨15364649502118498392820615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20486199336157997857094153 15364649502118498392820615)
        ·
          refine ⟨23046974253177747589230923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15364649502118498392820615 23046974253177747589230923)
          ·
            refine ⟨34570461379766621383846385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23046974253177747589230923 34570461379766621383846385)
            ·
              refine ⟨25927846034824966037884789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34570461379766621383846385 25927846034824966037884789)
              ·
                refine ⟨2430735565764840566051699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25927846034824966037884789 2430735565764840566051699)
                ·
                  refine ⟨3646103348647260849077549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430735565764840566051699 3646103348647260849077549)
                  ·
                    refine ⟨1367288755742722818404081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3646103348647260849077549 1367288755742722818404081)
                    ·
                      refine ⟨1025466566807042113803061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1367288755742722818404081 1025466566807042113803061)
                      ·
                        rfl

theorem cell23_1997089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_1997089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997089 prefixEnd_1997089 := by exact prefixLift 1997089
  have htrace : WordTrace (prefixWord ++ tailWord_1997089) baseStart_1997089 baseEnd_1997089 := by
    simpa [prefixWord, tailWord_1997089, baseEnd_1997089] using wordTrace_append hprefix tailTrace_1997089
  have hstable : (prefixWord ++ tailWord_1997089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997089).length < 2 ^ (prefixWord ++ tailWord_1997089).sum := by decide
  have hdescent : baseEnd_1997089 < baseStart_1997089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997119 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 1, 4, 2]
def baseStart_1997119 : Nat := 118140960795 + 1997119 * 2 ^ 59
def prefixEnd_1997119 : Nat := 4983230072969 + 3 ^ 40 * 1997119 * 2
def baseEnd_1997119 : Nat := 1025481971226676996427923

theorem tailTrace_1997119 : CollatzResearch.WordTrace tailWord_1997119 prefixEnd_1997119 1025481971226676996427923 := by
  unfold tailWord_1997119
  simp only [CollatzResearch.WordTrace]
  refine ⟨72840914051786418615482411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48560609367857612410321607 72840914051786418615482411)
  ·
    refine ⟨109261371077679627923223617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72840914051786418615482411 109261371077679627923223617)
    ·
      refine ⟨81946028308259720942417713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109261371077679627923223617 81946028308259720942417713)
      ·
        refine ⟨61459521231194790706813285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81946028308259720942417713 61459521231194790706813285)
        ·
          refine ⟨11523660230849023257527491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61459521231194790706813285 11523660230849023257527491)
          ·
            refine ⟨17285490346273534886291237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11523660230849023257527491 17285490346273534886291237)
            ·
              refine ⟨3241029439926287791179607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17285490346273534886291237 3241029439926287791179607)
              ·
                refine ⟨4861544159889431686769411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241029439926287791179607 4861544159889431686769411)
                ·
                  refine ⟨7292316239834147530154117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861544159889431686769411 7292316239834147530154117)
                  ·
                    refine ⟨1367309294968902661903897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7292316239834147530154117 1367309294968902661903897)
                    ·
                      refine ⟨1025481971226676996427923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1367309294968902661903897 1025481971226676996427923)
                      ·
                        rfl

theorem cell23_1997119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 4, 2].length) (baseStart_1997119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997119 prefixEnd_1997119 := by exact prefixLift 1997119
  have htrace : WordTrace (prefixWord ++ tailWord_1997119) baseStart_1997119 baseEnd_1997119 := by
    simpa [prefixWord, tailWord_1997119, baseEnd_1997119] using wordTrace_append hprefix tailTrace_1997119
  have hstable : (prefixWord ++ tailWord_1997119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997119).length < 2 ^ (prefixWord ++ tailWord_1997119).sum := by decide
  have hdescent : baseEnd_1997119 < baseStart_1997119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997159 : List Nat := [1, 1, 5, 1, 3, 1, 2, 4, 5]
def baseStart_1997159 : Nat := 118140960795 + 1997159 * 2 ^ 59
def prefixEnd_1997159 : Nat := 4983230072969 + 3 ^ 40 * 1997159 * 2
def baseEnd_1997159 : Nat := 113944723383650759991971

theorem tailTrace_1997159 : CollatzResearch.WordTrace tailWord_1997159 prefixEnd_1997159 113944723383650759991971 := by
  unfold tailWord_1997159
  simp only [CollatzResearch.WordTrace]
  refine ⟨72842372971641505446938531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48561581981094336964625687 72842372971641505446938531)
  ·
    refine ⟨109263559457462258170407797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72842372971641505446938531 109263559457462258170407797)
    ·
      refine ⟨10243458699137086703475731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109263559457462258170407797 10243458699137086703475731)
      ·
        refine ⟨15365188048705630055213597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10243458699137086703475731 15365188048705630055213597)
        ·
          refine ⟨5761945518264611270705099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15365188048705630055213597 5761945518264611270705099)
          ·
            refine ⟨8642918277396916906057649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5761945518264611270705099 8642918277396916906057649)
            ·
              refine ⟨6482188708047687679543237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8642918277396916906057649 6482188708047687679543237)
              ·
                refine ⟨1215410382758941439914357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6482188708047687679543237 1215410382758941439914357)
                ·
                  refine ⟨113944723383650759991971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1215410382758941439914357 113944723383650759991971)
                  ·
                    rfl

theorem cell23_1997159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 5].length) (baseStart_1997159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997159 prefixEnd_1997159 := by exact prefixLift 1997159
  have htrace : WordTrace (prefixWord ++ tailWord_1997159) baseStart_1997159 baseEnd_1997159 := by
    simpa [prefixWord, tailWord_1997159, baseEnd_1997159] using wordTrace_append hprefix tailTrace_1997159
  have hstable : (prefixWord ++ tailWord_1997159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997159).length < 2 ^ (prefixWord ++ tailWord_1997159).sum := by decide
  have hdescent : baseEnd_1997159 < baseStart_1997159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997192 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1997192 : Nat := 118140960795 + 1997192 * 2 ^ 59
def prefixEnd_1997192 : Nat := 4983230072969 + 3 ^ 40 * 1997192 * 2
def baseEnd_1997192 : Nat := 1025519455314455210815087

theorem tailTrace_1997192 : CollatzResearch.WordTrace tailWord_1997192 prefixEnd_1997192 1025519455314455210815087 := by
  unfold tailWord_1997192
  simp only [CollatzResearch.WordTrace]
  refine ⟨36421788290260976041444915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48562384387014634721926553 36421788290260976041444915)
  ·
    refine ⟨54632682435391464062167373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36421788290260976041444915 54632682435391464062167373)
    ·
      refine ⟨20487255913271799023312765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54632682435391464062167373 20487255913271799023312765)
      ·
        refine ⟨7682720967476924633742287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20487255913271799023312765 7682720967476924633742287)
        ·
          refine ⟨11524081451215386950613431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7682720967476924633742287 11524081451215386950613431)
          ·
            refine ⟨17286122176823080425920147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11524081451215386950613431 17286122176823080425920147)
            ·
              refine ⟨25929183265234620638880221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17286122176823080425920147 25929183265234620638880221)
              ·
                refine ⟨9723443724462982739580083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25929183265234620638880221 9723443724462982739580083)
                ·
                  refine ⟨14585165586694474109370125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9723443724462982739580083 14585165586694474109370125)
                  ·
                    refine ⟨5469437095010427791013797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14585165586694474109370125 5469437095010427791013797)
                    ·
                      refine ⟨1025519455314455210815087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5469437095010427791013797 1025519455314455210815087)
                      ·
                        rfl

theorem cell23_1997192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1997192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997192 prefixEnd_1997192 := by exact prefixLift 1997192
  have htrace : WordTrace (prefixWord ++ tailWord_1997192) baseStart_1997192 baseEnd_1997192 := by
    simpa [prefixWord, tailWord_1997192, baseEnd_1997192] using wordTrace_append hprefix tailTrace_1997192
  have hstable : (prefixWord ++ tailWord_1997192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997192).length < 2 ^ (prefixWord ++ tailWord_1997192).sum := by decide
  have hdescent : baseEnd_1997192 < baseStart_1997192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997219 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 3, 4]
def baseStart_1997219 : Nat := 118140960795 + 1997219 * 2 ^ 59
def prefixEnd_1997219 : Nat := 4983230072969 + 3 ^ 40 * 1997219 * 2
def baseEnd_1997219 : Nat := 341844439764042201725821

theorem tailTrace_1997219 : CollatzResearch.WordTrace tailWord_1997219 prefixEnd_1997219 341844439764042201725821 := by
  unfold tailWord_1997219
  simp only [CollatzResearch.WordTrace]
  refine ⟨72844561351424135694122711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48563040900949423796081807 72844561351424135694122711)
  ·
    refine ⟨109266842027136203541184067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72844561351424135694122711 109266842027136203541184067)
    ·
      refine ⟨163900263040704305311776101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109266842027136203541184067 163900263040704305311776101)
      ·
        refine ⟨30731299320132057245958019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163900263040704305311776101 30731299320132057245958019)
        ·
          refine ⟨46096948980198085868937029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30731299320132057245958019 46096948980198085868937029)
          ·
            refine ⟨8643177933787141100425693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46096948980198085868937029 8643177933787141100425693)
            ·
              refine ⟨3241191725170177912659635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8643177933787141100425693 3241191725170177912659635)
              ·
                refine ⟨4861787587755266868989453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241191725170177912659635 4861787587755266868989453)
                ·
                  refine ⟨1823170345408225075871045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4861787587755266868989453 1823170345408225075871045)
                  ·
                    refine ⟨341844439764042201725821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1823170345408225075871045 341844439764042201725821)
                    ·
                      rfl

theorem cell23_1997219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 4].length) (baseStart_1997219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997219 prefixEnd_1997219 := by exact prefixLift 1997219
  have htrace : WordTrace (prefixWord ++ tailWord_1997219) baseStart_1997219 baseEnd_1997219 := by
    simpa [prefixWord, tailWord_1997219, baseEnd_1997219] using wordTrace_append hprefix tailTrace_1997219
  have hstable : (prefixWord ++ tailWord_1997219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997219).length < 2 ^ (prefixWord ++ tailWord_1997219).sum := by decide
  have hdescent : baseEnd_1997219 < baseStart_1997219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997242 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3]
def baseStart_1997242 : Nat := 118140960795 + 1997242 * 2 ^ 59
def prefixEnd_1997242 : Nat := 4983230072969 + 3 ^ 40 * 1997242 * 2
def baseEnd_1997242 : Nat := 1025545129347180015189857

theorem tailTrace_1997242 : CollatzResearch.WordTrace tailWord_1997242 prefixEnd_1997242 1025545129347180015189857 := by
  unfold tailWord_1997242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18211350057585202655552495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48563600153560540414806653 18211350057585202655552495)
  ·
    refine ⟨27317025086377803983328743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18211350057585202655552495 27317025086377803983328743)
    ·
      refine ⟨40975537629566705974993115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27317025086377803983328743 40975537629566705974993115)
      ·
        refine ⟨61463306444350058962489673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40975537629566705974993115 61463306444350058962489673)
        ·
          refine ⟨46097479833262544221867255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61463306444350058962489673 46097479833262544221867255)
          ·
            refine ⟨69146219749893816332800883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46097479833262544221867255 69146219749893816332800883)
            ·
              refine ⟨103719329624840724499201325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69146219749893816332800883 103719329624840724499201325)
              ·
                refine ⟨38894748609315271687200497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103719329624840724499201325 38894748609315271687200497)
                ·
                  refine ⟨29171061456986453765400373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38894748609315271687200497 29171061456986453765400373)
                  ·
                    refine ⟨2734787011592480040506285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29171061456986453765400373 2734787011592480040506285)
                    ·
                      refine ⟨1025545129347180015189857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2734787011592480040506285 1025545129347180015189857)
                      ·
                        rfl

theorem cell23_1997242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_1997242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997242 prefixEnd_1997242 := by exact prefixLift 1997242
  have htrace : WordTrace (prefixWord ++ tailWord_1997242) baseStart_1997242 baseEnd_1997242 := by
    simpa [prefixWord, tailWord_1997242, baseEnd_1997242] using wordTrace_append hprefix tailTrace_1997242
  have hstable : (prefixWord ++ tailWord_1997242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997242).length < 2 ^ (prefixWord ++ tailWord_1997242).sum := by decide
  have hdescent : baseEnd_1997242 < baseStart_1997242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997293 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1997293 : Nat := 118140960795 + 1997293 * 2 ^ 59
def prefixEnd_1997293 : Nat := 4983230072969 + 3 ^ 40 * 1997293 * 2
def baseEnd_1997293 : Nat := 1025571316860559315652123

theorem tailTrace_1997293 : CollatzResearch.WordTrace tailWord_1997293 prefixEnd_1997293 1025571316860559315652123 := by
  unfold tailWord_1997293
  simp only [CollatzResearch.WordTrace]
  refine ⟨72847260353156046332316533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48564840235437364221544355 72847260353156046332316533)
  ·
    refine ⟨6829430658108379343654675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72847260353156046332316533 6829430658108379343654675)
    ·
      refine ⟨10244145987162569015482013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6829430658108379343654675 10244145987162569015482013)
      ·
        refine ⟨3841554745185963380805755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10244145987162569015482013 3841554745185963380805755)
        ·
          refine ⟨5762332117778945071208633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3841554745185963380805755 5762332117778945071208633)
          ·
            refine ⟨4321749088334208803406475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5762332117778945071208633 4321749088334208803406475)
            ·
              refine ⟨6482623632501313205109713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4321749088334208803406475 6482623632501313205109713)
              ·
                refine ⟨4861967724375984903832285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6482623632501313205109713 4861967724375984903832285)
                ·
                  refine ⟨1823237896640994338937107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4861967724375984903832285 1823237896640994338937107)
                  ·
                    refine ⟨2734856844961491508405661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1823237896640994338937107 2734856844961491508405661)
                    ·
                      refine ⟨1025571316860559315652123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2734856844961491508405661 1025571316860559315652123)
                      ·
                        rfl

theorem cell23_1997293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1997293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997293 prefixEnd_1997293 := by exact prefixLift 1997293
  have htrace : WordTrace (prefixWord ++ tailWord_1997293) baseStart_1997293 baseEnd_1997293 := by
    simpa [prefixWord, tailWord_1997293, baseEnd_1997293] using wordTrace_append hprefix tailTrace_1997293
  have hstable : (prefixWord ++ tailWord_1997293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997293).length < 2 ^ (prefixWord ++ tailWord_1997293).sum := by decide
  have hdescent : baseEnd_1997293 < baseStart_1997293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997299 : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 1, 1, 4]
def baseStart_1997299 : Nat := 118140960795 + 1997299 * 2 ^ 59
def prefixEnd_1997299 : Nat := 4983230072969 + 3 ^ 40 * 1997299 * 2
def baseEnd_1997299 : Nat := 1025574397744486292177095

theorem tailTrace_1997299 : CollatzResearch.WordTrace tailWord_1997299 prefixEnd_1997299 1025574397744486292177095 := by
  unfold tailWord_1997299
  simp only [CollatzResearch.WordTrace]
  refine ⟨72847479191134309357034951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48564986127422872904689967 72847479191134309357034951)
  ·
    refine ⟨109271218786701464035552427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72847479191134309357034951 109271218786701464035552427)
    ·
      refine ⟨163906828180052196053328641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109271218786701464035552427 163906828180052196053328641)
      ·
        refine ⟨122930121135039147039996481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163906828180052196053328641 122930121135039147039996481)
        ·
          refine ⟨92197590851279360279997361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122930121135039147039996481 92197590851279360279997361)
          ·
            refine ⟨69148193138459520209998021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92197590851279360279997361 69148193138459520209998021)
            ·
              refine ⟨12965286213461160039374629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69148193138459520209998021 12965286213461160039374629)
              ·
                refine ⟨2430991165023967507382743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12965286213461160039374629 2430991165023967507382743)
                ·
                  refine ⟨3646486747535951261074115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430991165023967507382743 3646486747535951261074115)
                  ·
                    refine ⟨5469730121303926891611173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3646486747535951261074115 5469730121303926891611173)
                    ·
                      refine ⟨1025574397744486292177095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5469730121303926891611173 1025574397744486292177095)
                      ·
                        rfl

theorem cell23_1997299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 1, 4].length) (baseStart_1997299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997299 prefixEnd_1997299 := by exact prefixLift 1997299
  have htrace : WordTrace (prefixWord ++ tailWord_1997299) baseStart_1997299 baseEnd_1997299 := by
    simpa [prefixWord, tailWord_1997299, baseEnd_1997299] using wordTrace_append hprefix tailTrace_1997299
  have hstable : (prefixWord ++ tailWord_1997299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997299).length < 2 ^ (prefixWord ++ tailWord_1997299).sum := by decide
  have hdescent : baseEnd_1997299 < baseStart_1997299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997309 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_1997309 : Nat := 118140960795 + 1997309 * 2 ^ 59
def prefixEnd_1997309 : Nat := 4983230072969 + 3 ^ 40 * 1997309 * 2
def baseEnd_1997309 : Nat := 341859844183677084350683

theorem tailTrace_1997309 : CollatzResearch.WordTrace tailWord_1997309 prefixEnd_1997309 341859844183677084350683 := by
  unfold tailWord_1997309
  simp only [CollatzResearch.WordTrace]
  refine ⟨72847843921098081064898981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48565229280732054043265987 72847843921098081064898981)
  ·
    refine ⟨13658970735205890199668559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72847843921098081064898981 13658970735205890199668559)
    ·
      refine ⟨20488456102808835299502839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13658970735205890199668559 20488456102808835299502839)
      ·
        refine ⟨30732684154213252949254259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20488456102808835299502839 30732684154213252949254259)
        ·
          refine ⟨46099026231319879423881389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30732684154213252949254259 46099026231319879423881389)
          ·
            refine ⟨17287134836744954783955521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46099026231319879423881389 17287134836744954783955521)
            ·
              refine ⟨12965351127558716087966641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17287134836744954783955521 12965351127558716087966641)
              ·
                refine ⟨9724013345669037065974981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12965351127558716087966641 9724013345669037065974981)
                ·
                  refine ⟨1823252502312944449870309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9724013345669037065974981 1823252502312944449870309)
                  ·
                    refine ⟨341859844183677084350683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1823252502312944449870309 341859844183677084350683)
                    ·
                      rfl

theorem cell23_1997309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_1997309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997309 prefixEnd_1997309 := by exact prefixLift 1997309
  have htrace : WordTrace (prefixWord ++ tailWord_1997309) baseStart_1997309 baseEnd_1997309 := by
    simpa [prefixWord, tailWord_1997309, baseEnd_1997309] using wordTrace_append hprefix tailTrace_1997309
  have hstable : (prefixWord ++ tailWord_1997309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997309).length < 2 ^ (prefixWord ++ tailWord_1997309).sum := by decide
  have hdescent : baseEnd_1997309 < baseStart_1997309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997313 : List Nat := [1, 2, 4, 1, 3, 3, 2, 1, 1, 5]
def baseStart_1997313 : Nat := 118140960795 + 1997313 * 2 ^ 59
def prefixEnd_1997313 : Nat := 4983230072969 + 3 ^ 40 * 1997313 * 2
def baseEnd_1997313 : Nat := 341860528824549745800677

theorem tailTrace_1997313 : CollatzResearch.WordTrace tailWord_1997313 prefixEnd_1997313 341860528824549745800677 := by
  unfold tailWord_1997313
  simp only [CollatzResearch.WordTrace]
  refine ⟨72847989813083589748044593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48565326542055726498696395 72847989813083589748044593)
  ·
    refine ⟨54635992359812692311033445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72847989813083589748044593 54635992359812692311033445)
    ·
      refine ⟨10244248567464879808318771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54635992359812692311033445 10244248567464879808318771)
      ·
        refine ⟨15366372851197319712478157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10244248567464879808318771 15366372851197319712478157)
        ·
          refine ⟨5762389819198994892179309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15366372851197319712478157 5762389819198994892179309)
          ·
            refine ⟨2160896182199623084567241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5762389819198994892179309 2160896182199623084567241)
            ·
              refine ⟨1620672136649717313425431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2160896182199623084567241 1620672136649717313425431)
              ·
                refine ⟨2431008204974575970138147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620672136649717313425431 2431008204974575970138147)
                ·
                  refine ⟨3646512307461863955207221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2431008204974575970138147 3646512307461863955207221)
                  ·
                    refine ⟨341860528824549745800677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3646512307461863955207221 341860528824549745800677)
                    ·
                      rfl

theorem cell23_1997313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_1997313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997313 prefixEnd_1997313 := by exact prefixLift 1997313
  have htrace : WordTrace (prefixWord ++ tailWord_1997313) baseStart_1997313 baseEnd_1997313 := by
    simpa [prefixWord, tailWord_1997313, baseEnd_1997313] using wordTrace_append hprefix tailTrace_1997313
  have hstable : (prefixWord ++ tailWord_1997313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997313).length < 2 ^ (prefixWord ++ tailWord_1997313).sum := by decide
  have hdescent : baseEnd_1997313 < baseStart_1997313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997322 : List Nat := [3, 1, 2, 2, 2, 1, 12]
def baseStart_1997322 : Nat := 118140960795 + 1997322 * 2 ^ 59
def prefixEnd_1997322 : Nat := 4983230072969 + 3 ^ 40 * 1997322 * 2
def baseEnd_1997322 : Nat := 12661558120981971631969

theorem tailTrace_1997322 : CollatzResearch.WordTrace tailWord_1997322 prefixEnd_1997322 12661558120981971631969 := by
  unfold tailWord_1997322
  simp only [CollatzResearch.WordTrace]
  refine ⟨18212079517512746071280555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48565545380033989523414813 18212079517512746071280555)
  ·
    refine ⟨27318119276269119106920833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18212079517512746071280555 27318119276269119106920833)
    ·
      refine ⟨20488589457201839330190625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27318119276269119106920833 20488589457201839330190625)
      ·
        refine ⟨15366442092901379497642969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20488589457201839330190625 15366442092901379497642969)
        ·
          refine ⟨11524831569676034623232227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15366442092901379497642969 11524831569676034623232227)
          ·
            refine ⟨17287247354514051934848341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11524831569676034623232227 17287247354514051934848341)
            ·
              refine ⟨12661558120981971631969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 17287247354514051934848341 12661558120981971631969)
              ·
                rfl

theorem cell23_1997322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 12].length) (baseStart_1997322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997322 prefixEnd_1997322 := by exact prefixLift 1997322
  have htrace : WordTrace (prefixWord ++ tailWord_1997322) baseStart_1997322 baseEnd_1997322 := by
    simpa [prefixWord, tailWord_1997322, baseEnd_1997322] using wordTrace_append hprefix tailTrace_1997322
  have hstable : (prefixWord ++ tailWord_1997322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997322).length < 2 ^ (prefixWord ++ tailWord_1997322).sum := by decide
  have hdescent : baseEnd_1997322 < baseStart_1997322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997326 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_1997326 : Nat := 118140960795 + 1997326 * 2 ^ 59
def prefixEnd_1997326 : Nat := 4983230072969 + 3 ^ 40 * 1997326 * 2
def baseEnd_1997326 : Nat := 341862753907385895513157

theorem tailTrace_1997326 : CollatzResearch.WordTrace tailWord_1997326 prefixEnd_1997326 341862753907385895513157 := by
  unfold tailWord_1997326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9106057995254561621033479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48565642641357661978845221 9106057995254561621033479)
  ·
    refine ⟨13659086992881842431550219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9106057995254561621033479 13659086992881842431550219)
    ·
      refine ⟨20488630489322763647325329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13659086992881842431550219 20488630489322763647325329)
      ·
        refine ⟨15366472866992072735493997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20488630489322763647325329 15366472866992072735493997)
        ·
          refine ⟨5762427325122027275810249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15366472866992072735493997 5762427325122027275810249)
          ·
            refine ⟨4321820493841520456857687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5762427325122027275810249 4321820493841520456857687)
            ·
              refine ⟨6482730740762280685286531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4321820493841520456857687 6482730740762280685286531)
              ·
                refine ⟨9724096111143421027929797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482730740762280685286531 9724096111143421027929797)
                ·
                  refine ⟨1823268020839391442736837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9724096111143421027929797 1823268020839391442736837)
                  ·
                    refine ⟨341862753907385895513157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1823268020839391442736837 341862753907385895513157)
                    ·
                      rfl

theorem cell23_1997326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_1997326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997326 prefixEnd_1997326 := by exact prefixLift 1997326
  have htrace : WordTrace (prefixWord ++ tailWord_1997326) baseStart_1997326 baseEnd_1997326 := by
    simpa [prefixWord, tailWord_1997326, baseEnd_1997326] using wordTrace_append hprefix tailTrace_1997326
  have hstable : (prefixWord ++ tailWord_1997326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997326).length < 2 ^ (prefixWord ++ tailWord_1997326).sum := by decide
  have hdescent : baseEnd_1997326 < baseStart_1997326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997333 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 3, 2, 2]
def baseStart_1997333 : Nat := 118140960795 + 1997333 * 2 ^ 59
def prefixEnd_1997333 : Nat := 4983230072969 + 3 ^ 40 * 1997333 * 2
def baseEnd_1997333 : Nat := 1025591856086739159151939

theorem tailTrace_1997333 : CollatzResearch.WordTrace tailWord_1997333 prefixEnd_1997333 1025591856086739159151939 := by
  unfold tailWord_1997333
  simp only [CollatzResearch.WordTrace]
  refine ⟨72848719273011133163772653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48565812848674088775848435 72848719273011133163772653)
  ·
    refine ⟨27318269727379174936414745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72848719273011133163772653 27318269727379174936414745)
    ·
      refine ⟨20488702295534381202311059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27318269727379174936414745 20488702295534381202311059)
      ·
        refine ⟨30733053443301571803466589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20488702295534381202311059 30733053443301571803466589)
        ·
          refine ⟨11524895041238089426299971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30733053443301571803466589 11524895041238089426299971)
          ·
            refine ⟨17287342561857134139449957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11524895041238089426299971 17287342561857134139449957)
            ·
              refine ⟨3241376730348212651146867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17287342561857134139449957 3241376730348212651146867)
              ·
                refine ⟨4862065095522318976720301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241376730348212651146867 4862065095522318976720301)
                ·
                  refine ⟨1823274410820869616270113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4862065095522318976720301 1823274410820869616270113)
                  ·
                    refine ⟨1367455808115652212202585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1823274410820869616270113 1367455808115652212202585)
                    ·
                      refine ⟨1025591856086739159151939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1367455808115652212202585 1025591856086739159151939)
                      ·
                        rfl

theorem cell23_1997333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_1997333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997333 prefixEnd_1997333 := by exact prefixLift 1997333
  have htrace : WordTrace (prefixWord ++ tailWord_1997333) baseStart_1997333 baseEnd_1997333 := by
    simpa [prefixWord, tailWord_1997333, baseEnd_1997333] using wordTrace_append hprefix tailTrace_1997333
  have hstable : (prefixWord ++ tailWord_1997333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997333).length < 2 ^ (prefixWord ++ tailWord_1997333).sum := by decide
  have hdescent : baseEnd_1997333 < baseStart_1997333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997359 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 4, 7, 2]
def baseStart_1997359 : Nat := 118140960795 + 1997359 * 2 ^ 59
def prefixEnd_1997359 : Nat := 4983230072969 + 3 ^ 40 * 1997359 * 2
def baseEnd_1997359 : Nat := 1025605206583756057426819

theorem tailTrace_1997359 : CollatzResearch.WordTrace tailWord_1997359 prefixEnd_1997359 1025605206583756057426819 := by
  unfold tailWord_1997359
  simp only [CollatzResearch.WordTrace]
  refine ⟨72849667570916939604219131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48566445047277959736146087 72849667570916939604219131)
  ·
    refine ⟨109274501356375409406328697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72849667570916939604219131 109274501356375409406328697)
    ·
      refine ⟨81955876017281557054746523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109274501356375409406328697 81955876017281557054746523)
      ·
        refine ⟨122933814025922335582119785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81955876017281557054746523 122933814025922335582119785)
        ·
          refine ⟨92200360519441751686589839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122933814025922335582119785 92200360519441751686589839)
          ·
            refine ⟨138300540779162627529884759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92200360519441751686589839 138300540779162627529884759)
            ·
              refine ⟨207450811168743941294827139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138300540779162627529884759 207450811168743941294827139)
              ·
                refine ⟨311176216753115911942240709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207450811168743941294827139 311176216753115911942240709)
                ·
                  refine ⟨58345540641209233489170133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311176216753115911942240709 58345540641209233489170133)
                  ·
                    refine ⟨1367473608778341409902425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58345540641209233489170133 1367473608778341409902425)
                    ·
                      refine ⟨1025605206583756057426819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1367473608778341409902425 1025605206583756057426819)
                      ·
                        rfl

theorem cell23_1997359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 7, 2].length) (baseStart_1997359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997359 prefixEnd_1997359 := by exact prefixLift 1997359
  have htrace : WordTrace (prefixWord ++ tailWord_1997359) baseStart_1997359 baseEnd_1997359 := by
    simpa [prefixWord, tailWord_1997359, baseEnd_1997359] using wordTrace_append hprefix tailTrace_1997359
  have hstable : (prefixWord ++ tailWord_1997359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997359).length < 2 ^ (prefixWord ++ tailWord_1997359).sum := by decide
  have hdescent : baseEnd_1997359 < baseStart_1997359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997409 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_1997409 : Nat := 118140960795 + 1997409 * 2 ^ 59
def prefixEnd_1997409 : Nat := 4983230072969 + 3 ^ 40 * 1997409 * 2
def baseEnd_1997409 : Nat := 1025630880616480861801589

theorem tailTrace_1997409 : CollatzResearch.WordTrace tailWord_1997409 prefixEnd_1997409 1025630880616480861801589 := by
  unfold tailWord_1997409
  simp only [CollatzResearch.WordTrace]
  refine ⟨72851491220735798143539281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48567660813823865429026187 72851491220735798143539281)
  ·
    refine ⟨54638618415551848607654461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72851491220735798143539281 54638618415551848607654461)
    ·
      refine ⟨20489481905831943227870423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54638618415551848607654461 20489481905831943227870423)
      ·
        refine ⟨30734222858747914841805635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20489481905831943227870423 30734222858747914841805635)
        ·
          refine ⟨46101334288121872262708453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30734222858747914841805635 46101334288121872262708453)
          ·
            refine ⟨8644000179022851049257835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46101334288121872262708453 8644000179022851049257835)
            ·
              refine ⟨12966000268534276573886753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8644000179022851049257835 12966000268534276573886753)
              ·
                refine ⟨9724500201400707430415065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12966000268534276573886753 9724500201400707430415065)
                ·
                  refine ⟨7293375151050530572811299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9724500201400707430415065 7293375151050530572811299)
                  ·
                    refine ⟨10940062726575795859216949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7293375151050530572811299 10940062726575795859216949)
                    ·
                      refine ⟨1025630880616480861801589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10940062726575795859216949 1025630880616480861801589)
                      ·
                        rfl

theorem cell23_1997409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_1997409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997409 prefixEnd_1997409 := by exact prefixLift 1997409
  have htrace : WordTrace (prefixWord ++ tailWord_1997409) baseStart_1997409 baseEnd_1997409 := by
    simpa [prefixWord, tailWord_1997409, baseEnd_1997409] using wordTrace_append hprefix tailTrace_1997409
  have hstable : (prefixWord ++ tailWord_1997409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997409).length < 2 ^ (prefixWord ++ tailWord_1997409).sum := by decide
  have hdescent : baseEnd_1997409 < baseStart_1997409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997440 : List Nat := [2, 1, 1, 2, 1, 6, 2, 2, 2, 2, 2]
def baseStart_1997440 : Nat := 118140960795 + 1997440 * 2 ^ 59
def prefixEnd_1997440 : Nat := 4983230072969 + 3 ^ 40 * 1997440 * 2
def baseEnd_1997440 : Nat := 1025646798516770240513947

theorem tailTrace_1997440 : CollatzResearch.WordTrace tailWord_1997440 prefixEnd_1997440 1025646798516770240513947 := by
  unfold tailWord_1997440
  simp only [CollatzResearch.WordTrace]
  refine ⟨36426310941811745218958887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48568414589082326958611849 36426310941811745218958887)
  ·
    refine ⟨54639466412717617828438331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36426310941811745218958887 54639466412717617828438331)
    ·
      refine ⟨81959199619076426742657497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54639466412717617828438331 81959199619076426742657497)
      ·
        refine ⟨61469399714307320056993123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81959199619076426742657497 61469399714307320056993123)
        ·
          refine ⟨92204099571460980085489685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61469399714307320056993123 92204099571460980085489685)
          ·
            refine ⟨4322067167412233441507329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92204099571460980085489685 4322067167412233441507329)
            ·
              refine ⟨3241550375559175081130497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4322067167412233441507329 3241550375559175081130497)
              ·
                refine ⟨2431162781669381310847873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3241550375559175081130497 2431162781669381310847873)
                ·
                  refine ⟨1823372086252035983135905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2431162781669381310847873 1823372086252035983135905)
                  ·
                    refine ⟨1367529064689026987351929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1823372086252035983135905 1367529064689026987351929)
                    ·
                      refine ⟨1025646798516770240513947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1367529064689026987351929 1025646798516770240513947)
                      ·
                        rfl

theorem cell23_1997440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 2, 2, 2].length) (baseStart_1997440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997440 prefixEnd_1997440 := by exact prefixLift 1997440
  have htrace : WordTrace (prefixWord ++ tailWord_1997440) baseStart_1997440 baseEnd_1997440 := by
    simpa [prefixWord, tailWord_1997440, baseEnd_1997440] using wordTrace_append hprefix tailTrace_1997440
  have hstable : (prefixWord ++ tailWord_1997440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997440).length < 2 ^ (prefixWord ++ tailWord_1997440).sum := by decide
  have hdescent : baseEnd_1997440 < baseStart_1997440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997469 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1997469 : Nat := 118140960795 + 1997469 * 2 ^ 59
def prefixEnd_1997469 : Nat := 4983230072969 + 3 ^ 40 * 1997469 * 2
def baseEnd_1997469 : Nat := 1025661689455750627051313

theorem tailTrace_1997469 : CollatzResearch.WordTrace tailWord_1997469 prefixEnd_1997469 1025661689455750627051313 := by
  unfold tailWord_1997469
  simp only [CollatzResearch.WordTrace]
  refine ⟨72853679600518428390723461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48569119733678952260482307 72853679600518428390723461)
  ·
    refine ⟨13660064925097205323260649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72853679600518428390723461 13660064925097205323260649)
    ·
      refine ⟨10245048693822903992445487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13660064925097205323260649 10245048693822903992445487)
      ·
        refine ⟨15367573040734355988668231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10245048693822903992445487 15367573040734355988668231)
        ·
          refine ⟨23051359561101533983002347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15367573040734355988668231 23051359561101533983002347)
          ·
            refine ⟨34577039341652300974503521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23051359561101533983002347 34577039341652300974503521)
            ·
              refine ⟨25932779506239225730877641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34577039341652300974503521 25932779506239225730877641)
              ·
                refine ⟨19449584629679419298158231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25932779506239225730877641 19449584629679419298158231)
                ·
                  refine ⟨29174376944519128947237347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19449584629679419298158231 29174376944519128947237347)
                  ·
                    refine ⟨43761565416778693420856021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29174376944519128947237347 43761565416778693420856021)
                    ·
                      refine ⟨1025661689455750627051313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43761565416778693420856021 1025661689455750627051313)
                      ·
                        rfl

theorem cell23_1997469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1997469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997469 prefixEnd_1997469 := by exact prefixLift 1997469
  have htrace : WordTrace (prefixWord ++ tailWord_1997469) baseStart_1997469 baseEnd_1997469 := by
    simpa [prefixWord, tailWord_1997469, baseEnd_1997469] using wordTrace_append hprefix tailTrace_1997469
  have hstable : (prefixWord ++ tailWord_1997469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997469).length < 2 ^ (prefixWord ++ tailWord_1997469).sum := by decide
  have hdescent : baseEnd_1997469 < baseStart_1997469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997509 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_1997509 : Nat := 118140960795 + 1997509 * 2 ^ 59
def prefixEnd_1997509 : Nat := 4983230072969 + 3 ^ 40 * 1997509 * 2
def baseEnd_1997509 : Nat := 1025682228681930470551129

theorem tailTrace_1997509 : CollatzResearch.WordTrace tailWord_1997509 prefixEnd_1997509 1025682228681930470551129 := by
  unfold tailWord_1997509
  simp only [CollatzResearch.WordTrace]
  refine ⟨72855138520373515222179581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48570092346915676814786387 72855138520373515222179581)
  ·
    refine ⟨27320676945140068208317343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72855138520373515222179581 27320676945140068208317343)
    ·
      refine ⟨40981015417710102312476015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27320676945140068208317343 40981015417710102312476015)
      ·
        refine ⟨61471523126565153468714023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40981015417710102312476015 61471523126565153468714023)
        ·
          refine ⟨92207284689847730203071035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61471523126565153468714023 92207284689847730203071035)
          ·
            refine ⟨138310927034771595304606553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92207284689847730203071035 138310927034771595304606553)
            ·
              refine ⟨103733195276078696478454915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138310927034771595304606553 103733195276078696478454915)
              ·
                refine ⟨155599792914118044717682373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103733195276078696478454915 155599792914118044717682373)
                ·
                  refine ⟨29174961171397133384565445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155599792914118044717682373 29174961171397133384565445)
                  ·
                    refine ⟨5470305219636962509606021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29174961171397133384565445 5470305219636962509606021)
                    ·
                      refine ⟨1025682228681930470551129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5470305219636962509606021 1025682228681930470551129)
                      ·
                        rfl

theorem cell23_1997509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_1997509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997509 prefixEnd_1997509 := by exact prefixLift 1997509
  have htrace : WordTrace (prefixWord ++ tailWord_1997509) baseStart_1997509 baseEnd_1997509 := by
    simpa [prefixWord, tailWord_1997509, baseEnd_1997509] using wordTrace_append hprefix tailTrace_1997509
  have hstable : (prefixWord ++ tailWord_1997509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997509).length < 2 ^ (prefixWord ++ tailWord_1997509).sum := by decide
  have hdescent : baseEnd_1997509 < baseStart_1997509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997540 : List Nat := [2, 3, 1, 1, 1, 4, 3, 3, 1, 4]
def baseStart_1997540 : Nat := 118140960795 + 1997540 * 2 ^ 59
def prefixEnd_1997540 : Nat := 4983230072969 + 3 ^ 40 * 1997540 * 2
def baseEnd_1997540 : Nat := 341899382194073283087829

theorem tailTrace_1997540 : CollatzResearch.WordTrace tailWord_1997540 prefixEnd_1997540 341899382194073283087829 := by
  unfold tailWord_1997540
  simp only [CollatzResearch.WordTrace]
  refine ⟨36428134591630603758279037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48570846122174138344372049 36428134591630603758279037)
  ·
    refine ⟨13660550471861476409354639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36428134591630603758279037 13660550471861476409354639)
    ·
      refine ⟨20490825707792214614031959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13660550471861476409354639 20490825707792214614031959)
      ·
        refine ⟨30736238561688321921047939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20490825707792214614031959 30736238561688321921047939)
        ·
          refine ⟨46104357842532482881571909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30736238561688321921047939 46104357842532482881571909)
          ·
            refine ⟨8644567095474840540294733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46104357842532482881571909 8644567095474840540294733)
            ·
              refine ⟨3241712660803065202610525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8644567095474840540294733 3241712660803065202610525)
              ·
                refine ⟨1215642247801149450978947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3241712660803065202610525 1215642247801149450978947)
                ·
                  refine ⟨1823463371701724176468421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1215642247801149450978947 1823463371701724176468421)
                  ·
                    refine ⟨341899382194073283087829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1823463371701724176468421 341899382194073283087829)
                    ·
                      rfl

theorem cell23_1997540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_1997540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997540 prefixEnd_1997540 := by exact prefixLift 1997540
  have htrace : WordTrace (prefixWord ++ tailWord_1997540) baseStart_1997540 baseEnd_1997540 := by
    simpa [prefixWord, tailWord_1997540, baseEnd_1997540] using wordTrace_append hprefix tailTrace_1997540
  have hstable : (prefixWord ++ tailWord_1997540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997540).length < 2 ^ (prefixWord ++ tailWord_1997540).sum := by decide
  have hdescent : baseEnd_1997540 < baseStart_1997540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997559 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_1997559 : Nat := 118140960795 + 1997559 * 2 ^ 59
def prefixEnd_1997559 : Nat := 4983230072969 + 3 ^ 40 * 1997559 * 2
def baseEnd_1997559 : Nat := 1025707902714655274925899

theorem tailTrace_1997559 : CollatzResearch.WordTrace tailWord_1997559 prefixEnd_1997559 1025707902714655274925899 := by
  unfold tailWord_1997559
  simp only [CollatzResearch.WordTrace]
  refine ⟨72856962170192373761499731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48571308113461582507666487 72856962170192373761499731)
  ·
    refine ⟨109285443255288560642249597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72856962170192373761499731 109285443255288560642249597)
    ·
      refine ⟨40982041220733210240843599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109285443255288560642249597 40982041220733210240843599)
      ·
        refine ⟨61473061831099815361265399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40982041220733210240843599 61473061831099815361265399)
        ·
          refine ⟨92209592746649723041898099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61473061831099815361265399 92209592746649723041898099)
          ·
            refine ⟨138314389119974584562847149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92209592746649723041898099 138314389119974584562847149)
            ·
              refine ⟨51867895919990469211067681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138314389119974584562847149 51867895919990469211067681)
              ·
                refine ⟨38900921939992851908300761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51867895919990469211067681 38900921939992851908300761)
                ·
                  refine ⟨29175691454994638931225571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38900921939992851908300761 29175691454994638931225571)
                  ·
                    refine ⟨43763537182491958396838357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29175691454994638931225571 43763537182491958396838357)
                    ·
                      refine ⟨1025707902714655274925899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43763537182491958396838357 1025707902714655274925899)
                      ·
                        rfl

theorem cell23_1997559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_1997559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997559 prefixEnd_1997559 := by exact prefixLift 1997559
  have htrace : WordTrace (prefixWord ++ tailWord_1997559) baseStart_1997559 baseEnd_1997559 := by
    simpa [prefixWord, tailWord_1997559, baseEnd_1997559] using wordTrace_append hprefix tailTrace_1997559
  have hstable : (prefixWord ++ tailWord_1997559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997559).length < 2 ^ (prefixWord ++ tailWord_1997559).sum := by decide
  have hdescent : baseEnd_1997559 < baseStart_1997559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997570 : List Nat := [3, 4, 1, 1, 1, 2, 4, 1, 6]
def baseStart_1997570 : Nat := 118140960795 + 1997570 * 2 ^ 59
def prefixEnd_1997570 : Nat := 4983230072969 + 3 ^ 40 * 1997570 * 2
def baseEnd_1997570 : Nat := 113968172333539414654261

theorem tailTrace_1997570 : CollatzResearch.WordTrace tailWord_1997570 prefixEnd_1997570 113968172333539414654261 := by
  unfold tailWord_1997570
  simp only [CollatzResearch.WordTrace]
  refine ⟨18214340843288130660037541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48571575582101681760100109 18214340843288130660037541)
  ·
    refine ⟨3415188908116524498757039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18214340843288130660037541 3415188908116524498757039)
    ·
      refine ⟨5122783362174786748135559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3415188908116524498757039 5122783362174786748135559)
      ·
        refine ⟨7684175043262180122203339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5122783362174786748135559 7684175043262180122203339)
        ·
          refine ⟨11526262564893270183305009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7684175043262180122203339 11526262564893270183305009)
          ·
            refine ⟨8644696923669952637478757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11526262564893270183305009 8644696923669952637478757)
            ·
              refine ⟨1620880673188116119527267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8644696923669952637478757 1620880673188116119527267)
              ·
                refine ⟨2431321009782174179290901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620880673188116119527267 2431321009782174179290901)
                ·
                  refine ⟨113968172333539414654261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2431321009782174179290901 113968172333539414654261)
                  ·
                    rfl

theorem cell23_1997570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_1997570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997570 prefixEnd_1997570 := by exact prefixLift 1997570
  have htrace : WordTrace (prefixWord ++ tailWord_1997570) baseStart_1997570 baseEnd_1997570 := by
    simpa [prefixWord, tailWord_1997570, baseEnd_1997570] using wordTrace_append hprefix tailTrace_1997570
  have hstable : (prefixWord ++ tailWord_1997570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997570).length < 2 ^ (prefixWord ++ tailWord_1997570).sum := by decide
  have hdescent : baseEnd_1997570 < baseStart_1997570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997596 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 3, 6]
def baseStart_1997596 : Nat := 118140960795 + 1997596 * 2 ^ 59
def prefixEnd_1997596 : Nat := 4983230072969 + 3 ^ 40 * 1997596 * 2
def baseEnd_1997596 : Nat := 341908967166290543387743

theorem tailTrace_1997596 : CollatzResearch.WordTrace tailWord_1997596 prefixEnd_1997596 341908967166290543387743 := by
  unfold tailWord_1997596
  simp only [CollatzResearch.WordTrace]
  refine ⟨36429155835529164540298321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48572207780705552720397761 36429155835529164540298321)
  ·
    refine ⟨27321866876646873405223741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36429155835529164540298321 27321866876646873405223741)
    ·
      refine ⟨10245700078742577526958903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27321866876646873405223741 10245700078742577526958903)
      ·
        refine ⟨15368550118113866290438355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10245700078742577526958903 15368550118113866290438355)
        ·
          refine ⟨23052825177170799435657533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15368550118113866290438355 23052825177170799435657533)
          ·
            refine ⟨8644809441439049788371575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23052825177170799435657533 8644809441439049788371575)
            ·
              refine ⟨12967214162158574682557363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8644809441439049788371575 12967214162158574682557363)
              ·
                refine ⟨19450821243237862023836045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12967214162158574682557363 19450821243237862023836045)
                ·
                  refine ⟨7294057966214198258938517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19450821243237862023836045 7294057966214198258938517)
                  ·
                    refine ⟨341908967166290543387743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7294057966214198258938517 341908967166290543387743)
                    ·
                      rfl

theorem cell23_1997596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_1997596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997596 prefixEnd_1997596 := by exact prefixLift 1997596
  have htrace : WordTrace (prefixWord ++ tailWord_1997596) baseStart_1997596 baseEnd_1997596 := by
    simpa [prefixWord, tailWord_1997596, baseEnd_1997596] using wordTrace_append hprefix tailTrace_1997596
  have hstable : (prefixWord ++ tailWord_1997596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997596).length < 2 ^ (prefixWord ++ tailWord_1997596).sum := by decide
  have hdescent : baseEnd_1997596 < baseStart_1997596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997600 : List Nat := [2, 1, 1, 5, 1, 3, 3, 1, 1, 5]
def baseStart_1997600 : Nat := 118140960795 + 1997600 * 2 ^ 59
def prefixEnd_1997600 : Nat := 4983230072969 + 3 ^ 40 * 1997600 * 2
def baseEnd_1997600 : Nat := 341909651807163204837737

theorem tailTrace_1997600 : CollatzResearch.WordTrace tailWord_1997600 prefixEnd_1997600 341909651807163204837737 := by
  unfold tailWord_1997600
  simp only [CollatzResearch.WordTrace]
  refine ⟨36429228781521918881871127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48572305042029225175828169 36429228781521918881871127)
  ·
    refine ⟨54643843172282878322806691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36429228781521918881871127 54643843172282878322806691)
    ·
      refine ⟨81965764758424317484210037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54643843172282878322806691 81965764758424317484210037)
      ·
        refine ⟨7684290446102279764144691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81965764758424317484210037 7684290446102279764144691)
        ·
          refine ⟨11526435669153419646217037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7684290446102279764144691 11526435669153419646217037)
          ·
            refine ⟨4322413375932532367331389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11526435669153419646217037 4322413375932532367331389)
            ·
              refine ⟨1620905015974699637749271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4322413375932532367331389 1620905015974699637749271)
              ·
                refine ⟨2431357523962049456623907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620905015974699637749271 2431357523962049456623907)
                ·
                  refine ⟨3647036285943074184935861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2431357523962049456623907 3647036285943074184935861)
                  ·
                    refine ⟨341909651807163204837737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3647036285943074184935861 341909651807163204837737)
                    ·
                      rfl

theorem cell23_1997600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 1, 5].length) (baseStart_1997600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997600 prefixEnd_1997600 := by exact prefixLift 1997600
  have htrace : WordTrace (prefixWord ++ tailWord_1997600) baseStart_1997600 baseEnd_1997600 := by
    simpa [prefixWord, tailWord_1997600, baseEnd_1997600] using wordTrace_append hprefix tailTrace_1997600
  have hstable : (prefixWord ++ tailWord_1997600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997600).length < 2 ^ (prefixWord ++ tailWord_1997600).sum := by decide
  have hdescent : baseEnd_1997600 < baseStart_1997600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997614 : List Nat := [4, 1, 3, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_1997614 : Nat := 118140960795 + 1997614 * 2 ^ 59
def prefixEnd_1997614 : Nat := 4983230072969 + 3 ^ 40 * 1997614 * 2
def baseEnd_1997614 : Nat := 1025736144150652559738147

theorem tailTrace_1997614 : CollatzResearch.WordTrace tailWord_1997614 prefixEnd_1997614 1025736144150652559738147 := by
  unfold tailWord_1997614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9107371023124139769343987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48572645456662078769834597 9107371023124139769343987)
  ·
    refine ⟨13661056534686209654015981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9107371023124139769343987 13661056534686209654015981)
    ·
      refine ⟨5122896200507328620255993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13661056534686209654015981 5122896200507328620255993)
      ·
        refine ⟨3842172150380496465191995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5122896200507328620255993 3842172150380496465191995)
        ·
          refine ⟨5763258225570744697787993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3842172150380496465191995 5763258225570744697787993)
          ·
            refine ⟨4322443669178058523340995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5763258225570744697787993 4322443669178058523340995)
            ·
              refine ⟨6483665503767087785011493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322443669178058523340995 6483665503767087785011493)
              ·
                refine ⟨1215687281956328959689655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6483665503767087785011493 1215687281956328959689655)
                ·
                  refine ⟨1823530922934493439534483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1215687281956328959689655 1823530922934493439534483)
                  ·
                    refine ⟨2735296384401740159301725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1823530922934493439534483 2735296384401740159301725)
                    ·
                      refine ⟨1025736144150652559738147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2735296384401740159301725 1025736144150652559738147)
                      ·
                        rfl

theorem cell23_1997614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_1997614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997614 prefixEnd_1997614 := by exact prefixLift 1997614
  have htrace : WordTrace (prefixWord ++ tailWord_1997614) baseStart_1997614 baseEnd_1997614 := by
    simpa [prefixWord, tailWord_1997614, baseEnd_1997614] using wordTrace_append hprefix tailTrace_1997614
  have hstable : (prefixWord ++ tailWord_1997614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997614).length < 2 ^ (prefixWord ++ tailWord_1997614).sum := by decide
  have hdescent : baseEnd_1997614 < baseStart_1997614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997630 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_1997630 : Nat := 118140960795 + 1997630 * 2 ^ 59
def prefixEnd_1997630 : Nat := 4983230072969 + 3 ^ 40 * 1997630 * 2
def baseEnd_1997630 : Nat := 341914786613708165712691

theorem tailTrace_1997630 : CollatzResearch.WordTrace tailWord_1997630 prefixEnd_1997630 341914786613708165712691 := by
  unfold tailWord_1997630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9107443969116894110916793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48573034501956768591556229 9107443969116894110916793)
  ·
    refine ⟨6830582976837670583187595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9107443969116894110916793 6830582976837670583187595)
    ·
      refine ⟨10245874465256505874781393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6830582976837670583187595 10245874465256505874781393)
      ·
        refine ⟨7684405848942379406086045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10245874465256505874781393 7684405848942379406086045)
        ·
          refine ⟨2881652193353392277282267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7684405848942379406086045 2881652193353392277282267)
          ·
            refine ⟨4322478290030088415923401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881652193353392277282267 4322478290030088415923401)
            ·
              refine ⟨3241858717522566311942551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4322478290030088415923401 3241858717522566311942551)
              ·
                refine ⟨4862788076283849467913827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241858717522566311942551 4862788076283849467913827)
                ·
                  refine ⟨7294182114425774201870741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4862788076283849467913827 7294182114425774201870741)
                  ·
                    refine ⟨341914786613708165712691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7294182114425774201870741 341914786613708165712691)
                    ·
                      rfl

theorem cell23_1997630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_1997630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997630 prefixEnd_1997630 := by exact prefixLift 1997630
  have htrace : WordTrace (prefixWord ++ tailWord_1997630) baseStart_1997630 baseEnd_1997630 := by
    simpa [prefixWord, tailWord_1997630, baseEnd_1997630] using wordTrace_append hprefix tailTrace_1997630
  have hstable : (prefixWord ++ tailWord_1997630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997630).length < 2 ^ (prefixWord ++ tailWord_1997630).sum := by decide
  have hdescent : baseEnd_1997630 < baseStart_1997630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997653 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_1997653 : Nat := 118140960795 + 1997653 * 2 ^ 59
def prefixEnd_1997653 : Nat := 4983230072969 + 3 ^ 40 * 1997653 * 2
def baseEnd_1997653 : Nat := 1025756169896177907150467

theorem tailTrace_1997653 : CollatzResearch.WordTrace tailWord_1997653 prefixEnd_1997653 1025756169896177907150467 := by
  unfold tailWord_1997653
  simp only [CollatzResearch.WordTrace]
  refine ⟨72860390631851827815421613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48573593754567885210281075 72860390631851827815421613)
  ·
    refine ⟨27322646486944435430783105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72860390631851827815421613 27322646486944435430783105)
    ·
      refine ⟨20491984865208326573087329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27322646486944435430783105 20491984865208326573087329)
      ·
        refine ⟨15368988648906244929815497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20491984865208326573087329 15368988648906244929815497)
        ·
          refine ⟨11526741486679683697361623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15368988648906244929815497 11526741486679683697361623)
          ·
            refine ⟨17290112230019525546042435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11526741486679683697361623 17290112230019525546042435)
            ·
              refine ⟨25935168345029288319063653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17290112230019525546042435 25935168345029288319063653)
              ·
                refine ⟨4862844064692991559824435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25935168345029288319063653 4862844064692991559824435)
                ·
                  refine ⟨7294266097039487339736653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4862844064692991559824435 7294266097039487339736653)
                  ·
                    refine ⟨2735349786389807752401245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7294266097039487339736653 2735349786389807752401245)
                    ·
                      refine ⟨1025756169896177907150467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2735349786389807752401245 1025756169896177907150467)
                      ·
                        rfl

theorem cell23_1997653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_1997653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997653 prefixEnd_1997653 := by exact prefixLift 1997653
  have htrace : WordTrace (prefixWord ++ tailWord_1997653) baseStart_1997653 baseEnd_1997653 := by
    simpa [prefixWord, tailWord_1997653, baseEnd_1997653] using wordTrace_append hprefix tailTrace_1997653
  have hstable : (prefixWord ++ tailWord_1997653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997653).length < 2 ^ (prefixWord ++ tailWord_1997653).sum := by decide
  have hdescent : baseEnd_1997653 < baseStart_1997653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997657 : List Nat := [1, 2, 1, 2, 2, 6, 2, 1, 1, 2, 3]
def baseStart_1997657 : Nat := 118140960795 + 1997657 * 2 ^ 59
def prefixEnd_1997657 : Nat := 4983230072969 + 3 ^ 40 * 1997657 * 2
def baseEnd_1997657 : Nat := 1025758223818795891500449

theorem tailTrace_1997657 : CollatzResearch.WordTrace tailWord_1997657 prefixEnd_1997657 1025758223818795891500449 := by
  unfold tailWord_1997657
  simp only [CollatzResearch.WordTrace]
  refine ⟨72860536523837336498567225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48573691015891557665711483 72860536523837336498567225)
  ·
    refine ⟨54645402392878002373925419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72860536523837336498567225 54645402392878002373925419)
    ·
      refine ⟨81968103589317003560888129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54645402392878002373925419 81968103589317003560888129)
      ·
        refine ⟨61476077691987752670666097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81968103589317003560888129 61476077691987752670666097)
        ·
          refine ⟨46107058268990814502999573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61476077691987752670666097 46107058268990814502999573)
          ·
            refine ⟨2161268356358944429828105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46107058268990814502999573 2161268356358944429828105)
            ·
              refine ⟨1620951267269208322371079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161268356358944429828105 1620951267269208322371079)
              ·
                refine ⟨2431426900903812483556619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620951267269208322371079 2431426900903812483556619)
                ·
                  refine ⟨3647140351355718725334929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2431426900903812483556619 3647140351355718725334929)
                  ·
                    refine ⟨2735355263516789044001197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3647140351355718725334929 2735355263516789044001197)
                    ·
                      refine ⟨1025758223818795891500449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2735355263516789044001197 1025758223818795891500449)
                      ·
                        rfl

theorem cell23_1997657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 1, 2, 3].length) (baseStart_1997657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997657 prefixEnd_1997657 := by exact prefixLift 1997657
  have htrace : WordTrace (prefixWord ++ tailWord_1997657) baseStart_1997657 baseEnd_1997657 := by
    simpa [prefixWord, tailWord_1997657, baseEnd_1997657] using wordTrace_append hprefix tailTrace_1997657
  have hstable : (prefixWord ++ tailWord_1997657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997657).length < 2 ^ (prefixWord ++ tailWord_1997657).sum := by decide
  have hdescent : baseEnd_1997657 < baseStart_1997657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997694 : List Nat := [4, 2, 3, 1, 3, 1, 2, 7]
def baseStart_1997694 : Nat := 118140960795 + 1997694 * 2 ^ 59
def prefixEnd_1997694 : Nat := 4983230072969 + 3 ^ 40 * 1997694 * 2
def baseEnd_1997694 : Nat := 37991748985296749879177

theorem tailTrace_1997694 : CollatzResearch.WordTrace tailWord_1997694 prefixEnd_1997694 37991748985296749879177 := by
  unfold tailWord_1997694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9107735753087911477208017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48574590683135527878442757 9107735753087911477208017)
  ·
    refine ⟨6830801814815933607906013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9107735753087911477208017 6830801814815933607906013)
    ·
      refine ⟨2561550680555975102964755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6830801814815933607906013 2561550680555975102964755)
      ·
        refine ⟨3842326020833962654447133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2561550680555975102964755 3842326020833962654447133)
        ·
          refine ⟨1440872257812735995417675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3842326020833962654447133 1440872257812735995417675)
          ·
            refine ⟨2161308386719103993126513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440872257812735995417675 2161308386719103993126513)
            ·
              refine ⟨1620981290039327994844885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161308386719103993126513 1620981290039327994844885)
              ·
                refine ⟨37991748985296749879177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1620981290039327994844885 37991748985296749879177)
                ·
                  rfl

theorem cell23_1997694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_1997694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997694 prefixEnd_1997694 := by exact prefixLift 1997694
  have htrace : WordTrace (prefixWord ++ tailWord_1997694) baseStart_1997694 baseEnd_1997694 := by
    simpa [prefixWord, tailWord_1997694, baseEnd_1997694] using wordTrace_append hprefix tailTrace_1997694
  have hstable : (prefixWord ++ tailWord_1997694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997694).length < 2 ^ (prefixWord ++ tailWord_1997694).sum := by decide
  have hdescent : baseEnd_1997694 < baseStart_1997694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997727 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 4, 2, 2]
def baseStart_1997727 : Nat := 118140960795 + 1997727 * 2 ^ 59
def prefixEnd_1997727 : Nat := 4983230072969 + 3 ^ 40 * 1997727 * 2
def baseEnd_1997727 : Nat := 1025794167464610617625127

theorem tailTrace_1997727 : CollatzResearch.WordTrace tailWord_1997727 prefixEnd_1997727 1025794167464610617625127 := by
  unfold tailWord_1997727
  simp only [CollatzResearch.WordTrace]
  refine ⟨72863089633583738453615435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48575393089055825635743623 72863089633583738453615435)
  ·
    refine ⟨109294634450375607680423153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72863089633583738453615435 109294634450375607680423153)
    ·
      refine ⟨81970975837781705760317365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109294634450375607680423153 81970975837781705760317365)
      ·
        refine ⟨7684778984792034915029753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81970975837781705760317365 7684778984792034915029753)
        ·
          refine ⟨5763584238594026186272315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7684778984792034915029753 5763584238594026186272315)
          ·
            refine ⟨8645376357891039279408473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5763584238594026186272315 8645376357891039279408473)
            ·
              refine ⟨6484032268418279459556355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8645376357891039279408473 6484032268418279459556355)
              ·
                refine ⟨9726048402627419189334533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6484032268418279459556355 9726048402627419189334533)
                ·
                  refine ⟨1823634075492641098000225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9726048402627419189334533 1823634075492641098000225)
                  ·
                    refine ⟨1367725556619480823500169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1823634075492641098000225 1367725556619480823500169)
                    ·
                      refine ⟨1025794167464610617625127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1367725556619480823500169 1025794167464610617625127)
                      ·
                        rfl

theorem cell23_1997727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_1997727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997727 prefixEnd_1997727 := by exact prefixLift 1997727
  have htrace : WordTrace (prefixWord ++ tailWord_1997727) baseStart_1997727 baseEnd_1997727 := by
    simpa [prefixWord, tailWord_1997727, baseEnd_1997727] using wordTrace_append hprefix tailTrace_1997727
  have hstable : (prefixWord ++ tailWord_1997727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997727).length < 2 ^ (prefixWord ++ tailWord_1997727).sum := by decide
  have hdescent : baseEnd_1997727 < baseStart_1997727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997780 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_1997780 : Nat := 118140960795 + 1997780 * 2 ^ 59
def prefixEnd_1997780 : Nat := 4983230072969 + 3 ^ 40 * 1997780 * 2
def baseEnd_1997780 : Nat := 341940460646432970087461

theorem tailTrace_1997780 : CollatzResearch.WordTrace tailWord_1997780 prefixEnd_1997780 341940460646432970087461 := by
  unfold tailWord_1997780
  simp only [CollatzResearch.WordTrace]
  refine ⟨36432511351195864252647397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48576681801594485670196529 36432511351195864252647397)
  ·
    refine ⟨6831095878349224547371387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36432511351195864252647397 6831095878349224547371387)
    ·
      refine ⟨10246643817523836821057081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6831095878349224547371387 10246643817523836821057081)
      ·
        refine ⟨7684982863142877615792811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10246643817523836821057081 7684982863142877615792811)
        ·
          refine ⟨11527474294714316423689217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7684982863142877615792811 11527474294714316423689217)
          ·
            refine ⟨8645605721035737317766913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11527474294714316423689217 8645605721035737317766913)
            ·
              refine ⟨6484204290776802988325185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8645605721035737317766913 6484204290776802988325185)
              ·
                refine ⟨4863153218082602241243889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6484204290776802988325185 4863153218082602241243889)
                ·
                  refine ⟨3647364913561951680932917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4863153218082602241243889 3647364913561951680932917)
                  ·
                    refine ⟨341940460646432970087461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3647364913561951680932917 341940460646432970087461)
                    ·
                      rfl

theorem cell23_1997780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_1997780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997780 prefixEnd_1997780 := by exact prefixLift 1997780
  have htrace : WordTrace (prefixWord ++ tailWord_1997780) baseStart_1997780 baseEnd_1997780 := by
    simpa [prefixWord, tailWord_1997780, baseEnd_1997780] using wordTrace_append hprefix tailTrace_1997780
  have hstable : (prefixWord ++ tailWord_1997780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997780).length < 2 ^ (prefixWord ++ tailWord_1997780).sum := by decide
  have hdescent : baseEnd_1997780 < baseStart_1997780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997783 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 4]
def baseStart_1997783 : Nat := 118140960795 + 1997783 * 2 ^ 59
def prefixEnd_1997783 : Nat := 4983230072969 + 3 ^ 40 * 1997783 * 2
def baseEnd_1997783 : Nat := 1025822922381262398524869

theorem tailTrace_1997783 : CollatzResearch.WordTrace tailWord_1997783 prefixEnd_1997783 1025822922381262398524869 := by
  unfold tailWord_1997783
  simp only [CollatzResearch.WordTrace]
  refine ⟨72865132121380860017654003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48576754747587240011769335 72865132121380860017654003)
  ·
    refine ⟨109297698182071290026481005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72865132121380860017654003 109297698182071290026481005)
    ·
      refine ⟨40986636818276733759930377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109297698182071290026481005 40986636818276733759930377)
      ·
        refine ⟨30739977613707550319947783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40986636818276733759930377 30739977613707550319947783)
        ·
          refine ⟨46109966420561325479921675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30739977613707550319947783 46109966420561325479921675)
          ·
            refine ⟨69164949630841988219882513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46109966420561325479921675 69164949630841988219882513)
            ·
              refine ⟨51873712223131491164911885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69164949630841988219882513 51873712223131491164911885)
              ·
                refine ⟨19452642083674309186841957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51873712223131491164911885 19452642083674309186841957)
                ·
                  refine ⟨3647370390688932972532867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19452642083674309186841957 3647370390688932972532867)
                  ·
                    refine ⟨5471055586033399458799301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3647370390688932972532867 5471055586033399458799301)
                    ·
                      refine ⟨1025822922381262398524869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5471055586033399458799301 1025822922381262398524869)
                      ·
                        rfl

theorem cell23_1997783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_1997783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997783 prefixEnd_1997783 := by exact prefixLift 1997783
  have htrace : WordTrace (prefixWord ++ tailWord_1997783) baseStart_1997783 baseEnd_1997783 := by
    simpa [prefixWord, tailWord_1997783, baseEnd_1997783] using wordTrace_append hprefix tailTrace_1997783
  have hstable : (prefixWord ++ tailWord_1997783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997783).length < 2 ^ (prefixWord ++ tailWord_1997783).sum := by decide
  have hdescent : baseEnd_1997783 < baseStart_1997783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997800 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_1997800 : Nat := 118140960795 + 1997800 * 2 ^ 59
def prefixEnd_1997800 : Nat := 4983230072969 + 3 ^ 40 * 1997800 * 2
def baseEnd_1997800 : Nat := 1025831651552388832012291

theorem tailTrace_1997800 : CollatzResearch.WordTrace tailWord_1997800 prefixEnd_1997800 1025831651552388832012291 := by
  unfold tailWord_1997800
  simp only [CollatzResearch.WordTrace]
  refine ⟨36432876081159635960511427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48577168108212847947348569 36432876081159635960511427)
  ·
    refine ⟨54649314121739453940767141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36432876081159635960511427 54649314121739453940767141)
    ·
      refine ⟨10246746397826147613893839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54649314121739453940767141 10246746397826147613893839)
      ·
        refine ⟨15370119596739221420840759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10246746397826147613893839 15370119596739221420840759)
        ·
          refine ⟨23055179395108832131261139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15370119596739221420840759 23055179395108832131261139)
          ·
            refine ⟨34582769092663248196891709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23055179395108832131261139 34582769092663248196891709)
            ·
              refine ⟨12968538409748718073834391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34582769092663248196891709 12968538409748718073834391)
              ·
                refine ⟨19452807614623077110751587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12968538409748718073834391 19452807614623077110751587)
                ·
                  refine ⟨29179211421934615666127381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19452807614623077110751587 29179211421934615666127381)
                  ·
                    refine ⟨1367775535403185109349721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29179211421934615666127381 1367775535403185109349721)
                    ·
                      refine ⟨1025831651552388832012291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1367775535403185109349721 1025831651552388832012291)
                      ·
                        rfl

theorem cell23_1997800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_1997800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997800 prefixEnd_1997800 := by exact prefixLift 1997800
  have htrace : WordTrace (prefixWord ++ tailWord_1997800) baseStart_1997800 baseEnd_1997800 := by
    simpa [prefixWord, tailWord_1997800, baseEnd_1997800] using wordTrace_append hprefix tailTrace_1997800
  have hstable : (prefixWord ++ tailWord_1997800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997800).length < 2 ^ (prefixWord ++ tailWord_1997800).sum := by decide
  have hdescent : baseEnd_1997800 < baseStart_1997800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997820 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_1997820 : Nat := 118140960795 + 1997820 * 2 ^ 59
def prefixEnd_1997820 : Nat := 4983230072969 + 3 ^ 40 * 1997820 * 2
def baseEnd_1997820 : Nat := 1025841921165478753762199

theorem tailTrace_1997820 : CollatzResearch.WordTrace tailWord_1997820 prefixEnd_1997820 1025841921165478753762199 := by
  unfold tailWord_1997820
  simp only [CollatzResearch.WordTrace]
  refine ⟨36433240811123407668375457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48577654414831210224500609 36433240811123407668375457)
  ·
    refine ⟨27324930608342555751281593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36433240811123407668375457 27324930608342555751281593)
    ·
      refine ⟨20493697956256916813461195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27324930608342555751281593 20493697956256916813461195)
      ·
        refine ⟨30740546934385375220191793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20493697956256916813461195 30740546934385375220191793)
        ·
          refine ⟨23055410200789031415143845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30740546934385375220191793 23055410200789031415143845)
          ·
            refine ⟨4322889412647943390339471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23055410200789031415143845 4322889412647943390339471)
            ·
              refine ⟨6484334118971915085509207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322889412647943390339471 6484334118971915085509207)
              ·
                refine ⟨9726501178457872628263811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6484334118971915085509207 9726501178457872628263811)
                ·
                  refine ⟨14589751767686808942395717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9726501178457872628263811 14589751767686808942395717)
                  ·
                    refine ⟨2735578456441276676699197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14589751767686808942395717 2735578456441276676699197)
                    ·
                      refine ⟨1025841921165478753762199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2735578456441276676699197 1025841921165478753762199)
                      ·
                        rfl

theorem cell23_1997820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_1997820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997820 prefixEnd_1997820 := by exact prefixLift 1997820
  have htrace : WordTrace (prefixWord ++ tailWord_1997820) baseStart_1997820 baseEnd_1997820 := by
    simpa [prefixWord, tailWord_1997820, baseEnd_1997820] using wordTrace_append hprefix tailTrace_1997820
  have hstable : (prefixWord ++ tailWord_1997820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997820).length < 2 ^ (prefixWord ++ tailWord_1997820).sum := by decide
  have hdescent : baseEnd_1997820 < baseStart_1997820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997833 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 1, 7, 3]
def baseStart_1997833 : Nat := 118140960795 + 1997833 * 2 ^ 59
def prefixEnd_1997833 : Nat := 4983230072969 + 3 ^ 40 * 1997833 * 2
def baseEnd_1997833 : Nat := 1025848596413987202899639

theorem tailTrace_1997833 : CollatzResearch.WordTrace tailWord_1997833 prefixEnd_1997833 1025848596413987202899639 := by
  unfold tailWord_1997833
  simp only [CollatzResearch.WordTrace]
  refine ⟨72866955771199718556974153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48577970514133145704649435 72866955771199718556974153)
  ·
    refine ⟨54650216828399788917730615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72866955771199718556974153 54650216828399788917730615)
    ·
      refine ⟨81975325242599683376595923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54650216828399788917730615 81975325242599683376595923)
      ·
        refine ⟨122962987863899525064893885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81975325242599683376595923 122962987863899525064893885)
        ·
          refine ⟨46111120448962321899335207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122962987863899525064893885 46111120448962321899335207)
          ·
            refine ⟨69166680673443482849002811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46111120448962321899335207 69166680673443482849002811)
            ·
              refine ⟨103750021010165224273504217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69166680673443482849002811 103750021010165224273504217)
              ·
                refine ⟨77812515757623918205128163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103750021010165224273504217 77812515757623918205128163)
                ·
                  refine ⟨116718773636435877307692245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77812515757623918205128163 116718773636435877307692245)
                  ·
                    refine ⟨2735596257103965874399037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 116718773636435877307692245 2735596257103965874399037)
                    ·
                      refine ⟨1025848596413987202899639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2735596257103965874399037 1025848596413987202899639)
                      ·
                        rfl

theorem cell23_1997833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 7, 3].length) (baseStart_1997833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997833 prefixEnd_1997833 := by exact prefixLift 1997833
  have htrace : WordTrace (prefixWord ++ tailWord_1997833) baseStart_1997833 baseEnd_1997833 := by
    simpa [prefixWord, tailWord_1997833, baseEnd_1997833] using wordTrace_append hprefix tailTrace_1997833
  have hstable : (prefixWord ++ tailWord_1997833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997833).length < 2 ^ (prefixWord ++ tailWord_1997833).sum := by decide
  have hdescent : baseEnd_1997833 < baseStart_1997833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997857 : List Nat := [1, 2, 3, 2, 3, 2, 3, 1, 6]
def baseStart_1997857 : Nat := 118140960795 + 1997857 * 2 ^ 59
def prefixEnd_1997857 : Nat := 4983230072969 + 3 ^ 40 * 1997857 * 2
def baseEnd_1997857 : Nat := 113984546661077234333281

theorem tailTrace_1997857 : CollatzResearch.WordTrace tailWord_1997857 prefixEnd_1997857 113984546661077234333281 := by
  unfold tailWord_1997857
  simp only [CollatzResearch.WordTrace]
  refine ⟨72867831123112770655847825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48578554082075180437231883 72867831123112770655847825)
  ·
    refine ⟨54650873342334577991885869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72867831123112770655847825 54650873342334577991885869)
    ·
      refine ⟨20494077503375466746957201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54650873342334577991885869 20494077503375466746957201)
      ·
        refine ⟨15370558127531600060217901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20494077503375466746957201 15370558127531600060217901)
        ·
          refine ⟨5763959297824350022581713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15370558127531600060217901 5763959297824350022581713)
          ·
            refine ⟨4322969473368262516936285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5763959297824350022581713 4322969473368262516936285)
            ·
              refine ⟨1621113552513098443851107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4322969473368262516936285 1621113552513098443851107)
              ·
                refine ⟨2431670328769647665776661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1621113552513098443851107 2431670328769647665776661)
                ·
                  refine ⟨113984546661077234333281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2431670328769647665776661 113984546661077234333281)
                  ·
                    rfl

theorem cell23_1997857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 6].length) (baseStart_1997857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997857 prefixEnd_1997857 := by exact prefixLift 1997857
  have htrace : WordTrace (prefixWord ++ tailWord_1997857) baseStart_1997857 baseEnd_1997857 := by
    simpa [prefixWord, tailWord_1997857, baseEnd_1997857] using wordTrace_append hprefix tailTrace_1997857
  have hstable : (prefixWord ++ tailWord_1997857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997857).length < 2 ^ (prefixWord ++ tailWord_1997857).sum := by decide
  have hdescent : baseEnd_1997857 < baseStart_1997857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997877 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_1997877 : Nat := 118140960795 + 1997877 * 2 ^ 59
def prefixEnd_1997877 : Nat := 4983230072969 + 3 ^ 40 * 1997877 * 2
def baseEnd_1997877 : Nat := 1025871189562785030749437

theorem tailTrace_1997877 : CollatzResearch.WordTrace tailWord_1997877 prefixEnd_1997877 1025871189562785030749437 := by
  unfold tailWord_1997877
  simp only [CollatzResearch.WordTrace]
  refine ⟨72868560583040314071575885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48579040388693542714383923 72868560583040314071575885)
  ·
    refine ⟨27325710218640117776840957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72868560583040314071575885 27325710218640117776840957)
    ·
      refine ⟨10247141331990044166315359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27325710218640117776840957 10247141331990044166315359)
      ·
        refine ⟨15370711997985066249473039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10247141331990044166315359 15370711997985066249473039)
        ·
          refine ⟨23056067996977599374209559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15370711997985066249473039 23056067996977599374209559)
          ·
            refine ⟨34584101995466399061314339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23056067996977599374209559 34584101995466399061314339)
            ·
              refine ⟨51876152993199598591971509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34584101995466399061314339 51876152993199598591971509)
              ·
                refine ⟨4863389343112462367997329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51876152993199598591971509 4863389343112462367997329)
                ·
                  refine ⟨3647542007334346775997997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4863389343112462367997329 3647542007334346775997997)
                  ·
                    refine ⟨1367828252750380040999249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3647542007334346775997997 1367828252750380040999249)
                    ·
                      refine ⟨1025871189562785030749437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1367828252750380040999249 1025871189562785030749437)
                      ·
                        rfl

theorem cell23_1997877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_1997877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997877 prefixEnd_1997877 := by exact prefixLift 1997877
  have htrace : WordTrace (prefixWord ++ tailWord_1997877) baseStart_1997877 baseEnd_1997877 := by
    simpa [prefixWord, tailWord_1997877, baseEnd_1997877] using wordTrace_append hprefix tailTrace_1997877
  have hstable : (prefixWord ++ tailWord_1997877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997877).length < 2 ^ (prefixWord ++ tailWord_1997877).sum := by decide
  have hdescent : baseEnd_1997877 < baseStart_1997877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997901 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_1997901 : Nat := 118140960795 + 1997901 * 2 ^ 59
def prefixEnd_1997901 : Nat := 4983230072969 + 3 ^ 40 * 1997901 * 2
def baseEnd_1997901 : Nat := 1025883513098492936849327

theorem tailTrace_1997901 : CollatzResearch.WordTrace tailWord_1997901 prefixEnd_1997901 1025883513098492936849327 := by
  unfold tailWord_1997901
  simp only [CollatzResearch.WordTrace]
  refine ⟨72869435934953366170449557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48579623956635577446966371 72869435934953366170449557)
  ·
    refine ⟨3415754809450939039239823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72869435934953366170449557 3415754809450939039239823)
    ·
      refine ⟨5123632214176408558859735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3415754809450939039239823 5123632214176408558859735)
      ·
        refine ⟨7685448321264612838289603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5123632214176408558859735 7685448321264612838289603)
        ·
          refine ⟨11528172481896919257434405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7685448321264612838289603 11528172481896919257434405)
          ·
            refine ⟨2161532340355672360768951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11528172481896919257434405 2161532340355672360768951)
            ·
              refine ⟨3242298510533508541153427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2161532340355672360768951 3242298510533508541153427)
              ·
                refine ⟨4863447765800262811730141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3242298510533508541153427 4863447765800262811730141)
                ·
                  refine ⟨1823792912175098554398803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4863447765800262811730141 1823792912175098554398803)
                  ·
                    refine ⟨2735689368262647831598205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1823792912175098554398803 2735689368262647831598205)
                    ·
                      refine ⟨1025883513098492936849327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2735689368262647831598205 1025883513098492936849327)
                      ·
                        rfl

theorem cell23_1997901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_1997901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997901 prefixEnd_1997901 := by exact prefixLift 1997901
  have htrace : WordTrace (prefixWord ++ tailWord_1997901) baseStart_1997901 baseEnd_1997901 := by
    simpa [prefixWord, tailWord_1997901, baseEnd_1997901] using wordTrace_append hprefix tailTrace_1997901
  have hstable : (prefixWord ++ tailWord_1997901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997901).length < 2 ^ (prefixWord ++ tailWord_1997901).sum := by decide
  have hdescent : baseEnd_1997901 < baseStart_1997901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997903 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 4]
def baseStart_1997903 : Nat := 118140960795 + 1997903 * 2 ^ 59
def prefixEnd_1997903 : Nat := 4983230072969 + 3 ^ 40 * 1997903 * 2
def baseEnd_1997903 : Nat := 1025884540059801929024317

theorem tailTrace_1997903 : CollatzResearch.WordTrace tailWord_1997903 prefixEnd_1997903 1025884540059801929024317 := by
  unfold tailWord_1997903
  simp only [CollatzResearch.WordTrace]
  refine ⟨72869508880946120512022363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48579672587297413674681575 72869508880946120512022363)
  ·
    refine ⟨109304263321419180768033545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72869508880946120512022363 109304263321419180768033545)
    ·
      refine ⟨81978197491064385576025159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109304263321419180768033545 81978197491064385576025159)
      ·
        refine ⟨122967296236596578364037739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81978197491064385576025159 122967296236596578364037739)
        ·
          refine ⟨184450944354894867546056609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122967296236596578364037739 184450944354894867546056609)
          ·
            refine ⟨138338208266171150659542457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184450944354894867546056609 138338208266171150659542457)
            ·
              refine ⟨103753656199628362994656843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138338208266171150659542457 103753656199628362994656843)
              ·
                refine ⟨155630484299442544491985265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103753656199628362994656843 155630484299442544491985265)
                ·
                  refine ⟨116722863224581908368988949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155630484299442544491985265 116722863224581908368988949)
                  ·
                    refine ⟨5471384213652276954796357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116722863224581908368988949 5471384213652276954796357)
                    ·
                      refine ⟨1025884540059801929024317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5471384213652276954796357 1025884540059801929024317)
                      ·
                        rfl

theorem cell23_1997903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_1997903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997903 prefixEnd_1997903 := by exact prefixLift 1997903
  have htrace : WordTrace (prefixWord ++ tailWord_1997903) baseStart_1997903 baseEnd_1997903 := by
    simpa [prefixWord, tailWord_1997903, baseEnd_1997903] using wordTrace_append hprefix tailTrace_1997903
  have hstable : (prefixWord ++ tailWord_1997903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997903).length < 2 ^ (prefixWord ++ tailWord_1997903).sum := by decide
  have hdescent : baseEnd_1997903 < baseStart_1997903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997920 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 4]
def baseStart_1997920 : Nat := 118140960795 + 1997920 * 2 ^ 59
def prefixEnd_1997920 : Nat := 4983230072969 + 3 ^ 40 * 1997920 * 2
def baseEnd_1997920 : Nat := 1025893269230928362511739

theorem tailTrace_1997920 : CollatzResearch.WordTrace tailWord_1997920 prefixEnd_1997920 1025893269230928362511739 := by
  unfold tailWord_1997920
  simp only [CollatzResearch.WordTrace]
  refine ⟨36435064460942266207695607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48580085947923021610260809 36435064460942266207695607)
  ·
    refine ⟨54652596691413399311543411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36435064460942266207695607 54652596691413399311543411)
    ·
      refine ⟨81978895037120098967315117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54652596691413399311543411 81978895037120098967315117)
      ·
        refine ⟨30742085638920037112743169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81978895037120098967315117 30742085638920037112743169)
        ·
          refine ⟨23056564229190027834557377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30742085638920037112743169 23056564229190027834557377)
          ·
            refine ⟨17292423171892520875918033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23056564229190027834557377 17292423171892520875918033)
            ·
              refine ⟨12969317378919390656938525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17292423171892520875918033 12969317378919390656938525)
              ·
                refine ⟨4863494017094771496351947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12969317378919390656938525 4863494017094771496351947)
                ·
                  refine ⟨7295241025642157244527921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4863494017094771496351947 7295241025642157244527921)
                  ·
                    refine ⟨5471430769231617933395941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7295241025642157244527921 5471430769231617933395941)
                    ·
                      refine ⟨1025893269230928362511739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5471430769231617933395941 1025893269230928362511739)
                      ·
                        rfl

theorem cell23_1997920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_1997920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997920 prefixEnd_1997920 := by exact prefixLift 1997920
  have htrace : WordTrace (prefixWord ++ tailWord_1997920) baseStart_1997920 baseEnd_1997920 := by
    simpa [prefixWord, tailWord_1997920, baseEnd_1997920] using wordTrace_append hprefix tailTrace_1997920
  have hstable : (prefixWord ++ tailWord_1997920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997920).length < 2 ^ (prefixWord ++ tailWord_1997920).sum := by decide
  have hdescent : baseEnd_1997920 < baseStart_1997920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997927 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_1997927 : Nat := 118140960795 + 1997927 * 2 ^ 59
def prefixEnd_1997927 : Nat := 4983230072969 + 3 ^ 40 * 1997927 * 2
def baseEnd_1997927 : Nat := 1025896863595509835124207

theorem tailTrace_1997927 : CollatzResearch.WordTrace tailWord_1997927 prefixEnd_1997927 1025896863595509835124207 := by
  unfold tailWord_1997927
  simp only [CollatzResearch.WordTrace]
  refine ⟨72870384232859172610896035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48580256155239448407264023 72870384232859172610896035)
  ·
    refine ⟨109305576349288758916344053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72870384232859172610896035 109305576349288758916344053)
    ·
      refine ⟨10247397782745821148407255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109305576349288758916344053 10247397782745821148407255)
      ·
        refine ⟨15371096674118731722610883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10247397782745821148407255 15371096674118731722610883)
        ·
          refine ⟨23056645011178097583916325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15371096674118731722610883 23056645011178097583916325)
          ·
            refine ⟨4323120939595893296984311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23056645011178097583916325 4323120939595893296984311)
            ·
              refine ⟨6484681409393839945476467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323120939595893296984311 6484681409393839945476467)
              ·
                refine ⟨9727022114090759918214701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6484681409393839945476467 9727022114090759918214701)
                ·
                  refine ⟨3647633292784034969330513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9727022114090759918214701 3647633292784034969330513)
                  ·
                    refine ⟨2735724969588026226997885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3647633292784034969330513 2735724969588026226997885)
                    ·
                      refine ⟨1025896863595509835124207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2735724969588026226997885 1025896863595509835124207)
                      ·
                        rfl

theorem cell23_1997927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_1997927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997927 prefixEnd_1997927 := by exact prefixLift 1997927
  have htrace : WordTrace (prefixWord ++ tailWord_1997927) baseStart_1997927 baseEnd_1997927 := by
    simpa [prefixWord, tailWord_1997927, baseEnd_1997927] using wordTrace_append hprefix tailTrace_1997927
  have hstable : (prefixWord ++ tailWord_1997927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997927).length < 2 ^ (prefixWord ++ tailWord_1997927).sum := by decide
  have hdescent : baseEnd_1997927 < baseStart_1997927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997930 : List Nat := [3, 1, 3, 2, 2, 1, 2, 9]
def baseStart_1997930 : Nat := 118140960795 + 1997930 * 2 ^ 59
def prefixEnd_1997930 : Nat := 4983230072969 + 3 ^ 40 * 1997930 * 2
def baseEnd_1997930 : Nat := 37996237186573086051359

theorem tailTrace_1997930 : CollatzResearch.WordTrace tailWord_1997930 prefixEnd_1997930 37996237186573086051359 := by
  unfold tailWord_1997930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18217623412962076030813811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48580329101232202748836829 18217623412962076030813811)
  ·
    refine ⟨27326435119443114046220717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18217623412962076030813811 27326435119443114046220717)
    ·
      refine ⟨10247413169791167767332769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27326435119443114046220717 10247413169791167767332769)
      ·
        refine ⟨7685559877343375825499577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10247413169791167767332769 7685559877343375825499577)
        ·
          refine ⟨5764169908007531869124683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7685559877343375825499577 5764169908007531869124683)
          ·
            refine ⟨8646254862011297803687025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5764169908007531869124683 8646254862011297803687025)
            ·
              refine ⟨6484691146508473352765269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8646254862011297803687025 6484691146508473352765269)
              ·
                refine ⟨37996237186573086051359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6484691146508473352765269 37996237186573086051359)
                ·
                  rfl

theorem cell23_1997930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 9].length) (baseStart_1997930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997930 prefixEnd_1997930 := by exact prefixLift 1997930
  have htrace : WordTrace (prefixWord ++ tailWord_1997930) baseStart_1997930 baseEnd_1997930 := by
    simpa [prefixWord, tailWord_1997930, baseEnd_1997930] using wordTrace_append hprefix tailTrace_1997930
  have hstable : (prefixWord ++ tailWord_1997930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997930).length < 2 ^ (prefixWord ++ tailWord_1997930).sum := by decide
  have hdescent : baseEnd_1997930 < baseStart_1997930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997984 : List Nat := [2, 1, 1, 4, 2, 1, 2, 4, 1, 3, 2]
def baseStart_1997984 : Nat := 118140960795 + 1997984 * 2 ^ 59
def prefixEnd_1997984 : Nat := 4983230072969 + 3 ^ 40 * 1997984 * 2
def baseEnd_1997984 : Nat := 1025926131992816112111445

theorem tailTrace_1997984 : CollatzResearch.WordTrace tailWord_1997984 prefixEnd_1997984 1025926131992816112111445 := by
  unfold tailWord_1997984
  simp only [CollatzResearch.WordTrace]
  refine ⟨36436231596826335672860503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48581642129101780897147337 36436231596826335672860503)
  ·
    refine ⟨54654347395239503509290755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36436231596826335672860503 54654347395239503509290755)
    ·
      refine ⟨81981521092859255263936133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54654347395239503509290755 81981521092859255263936133)
      ·
        refine ⟨15371535204911110361988025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81981521092859255263936133 15371535204911110361988025)
        ·
          refine ⟨11528651403683332771491019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15371535204911110361988025 11528651403683332771491019)
          ·
            refine ⟨17292977105524999157236529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11528651403683332771491019 17292977105524999157236529)
            ·
              refine ⟨12969732829143749367927397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17292977105524999157236529 12969732829143749367927397)
              ·
                refine ⟨2431824905464453006486387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12969732829143749367927397 2431824905464453006486387)
                ·
                  refine ⟨3647737358196679509729581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2431824905464453006486387 3647737358196679509729581)
                  ·
                    refine ⟨1367901509323754816148593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3647737358196679509729581 1367901509323754816148593)
                    ·
                      refine ⟨1025926131992816112111445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1367901509323754816148593 1025926131992816112111445)
                      ·
                        rfl

theorem cell23_1997984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_1997984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1997984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1997984 prefixEnd_1997984 := by exact prefixLift 1997984
  have htrace : WordTrace (prefixWord ++ tailWord_1997984) baseStart_1997984 baseEnd_1997984 := by
    simpa [prefixWord, tailWord_1997984, baseEnd_1997984] using wordTrace_append hprefix tailTrace_1997984
  have hstable : (prefixWord ++ tailWord_1997984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997984).length < 2 ^ (prefixWord ++ tailWord_1997984).sum := by decide
  have hdescent : baseEnd_1997984 < baseStart_1997984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998000 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 3]
def baseStart_1998000 : Nat := 118140960795 + 1998000 * 2 ^ 59
def prefixEnd_1998000 : Nat := 4983230072969 + 3 ^ 40 * 1998000 * 2
def baseEnd_1998000 : Nat := 1025934347683288049511371

theorem tailTrace_1998000 : CollatzResearch.WordTrace tailWord_1998000 prefixEnd_1998000 1025934347683288049511371 := by
  unfold tailWord_1998000
  simp only [CollatzResearch.WordTrace]
  refine ⟨36436523380797353039151727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48582031174396470718868969 36436523380797353039151727)
  ·
    refine ⟨54654785071196029558727591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36436523380797353039151727 54654785071196029558727591)
    ·
      refine ⟨81982177606794044338091387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54654785071196029558727591 81982177606794044338091387)
      ·
        refine ⟨122973266410191066507137081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81982177606794044338091387 122973266410191066507137081)
        ·
          refine ⟨92229949807643299880352811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122973266410191066507137081 92229949807643299880352811)
          ·
            refine ⟨138344924711464949820529217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92229949807643299880352811 138344924711464949820529217)
            ·
              refine ⟨103758693533598712365396913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138344924711464949820529217 103758693533598712365396913)
              ·
                refine ⟨77819020150199034274047685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103758693533598712365396913 77819020150199034274047685)
                ·
                  refine ⟨14591066278162318926383941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77819020150199034274047685 14591066278162318926383941)
                  ·
                    refine ⟨2735824927155434798696989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14591066278162318926383941 2735824927155434798696989)
                    ·
                      refine ⟨1025934347683288049511371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2735824927155434798696989 1025934347683288049511371)
                      ·
                        rfl

theorem cell23_1998000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 3].length) (baseStart_1998000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998000 prefixEnd_1998000 := by exact prefixLift 1998000
  have htrace : WordTrace (prefixWord ++ tailWord_1998000) baseStart_1998000 baseEnd_1998000 := by
    simpa [prefixWord, tailWord_1998000, baseEnd_1998000] using wordTrace_append hprefix tailTrace_1998000
  have hstable : (prefixWord ++ tailWord_1998000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998000).length < 2 ^ (prefixWord ++ tailWord_1998000).sum := by decide
  have hdescent : baseEnd_1998000 < baseStart_1998000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998001 : List Nat := [1, 2, 2, 5, 1, 2, 1, 3, 1, 3, 2]
def baseStart_1998001 : Nat := 118140960795 + 1998001 * 2 ^ 59
def prefixEnd_1998001 : Nat := 4983230072969 + 3 ^ 40 * 1998001 * 2
def baseEnd_1998001 : Nat := 1025934861163942545598867

theorem tailTrace_1998001 : CollatzResearch.WordTrace tailWord_1998001 prefixEnd_1998001 1025934861163942545598867 := by
  unfold tailWord_1998001
  simp only [CollatzResearch.WordTrace]
  refine ⟨72873083234591083249089857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48582055489727388832726571 72873083234591083249089857)
  ·
    refine ⟨54654812425943312436817393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72873083234591083249089857 54654812425943312436817393)
    ·
      refine ⟨40991109319457484327613045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54654812425943312436817393 40991109319457484327613045)
      ·
        refine ⟨3842916498699139155713723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40991109319457484327613045 3842916498699139155713723)
        ·
          refine ⟨5764374748048708733570585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3842916498699139155713723 5764374748048708733570585)
          ·
            refine ⟨4323281061036531550177939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5764374748048708733570585 4323281061036531550177939)
            ·
              refine ⟨6484921591554797325266909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323281061036531550177939 6484921591554797325266909)
              ·
                refine ⟨2431845596833048996975091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6484921591554797325266909 2431845596833048996975091)
                ·
                  refine ⟨3647768395249573495462637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2431845596833048996975091 3647768395249573495462637)
                  ·
                    refine ⟨1367913148218590060798489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3647768395249573495462637 1367913148218590060798489)
                    ·
                      refine ⟨1025934861163942545598867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1367913148218590060798489 1025934861163942545598867)
                      ·
                        rfl

theorem cell23_1998001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_1998001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998001 prefixEnd_1998001 := by exact prefixLift 1998001
  have htrace : WordTrace (prefixWord ++ tailWord_1998001) baseStart_1998001 baseEnd_1998001 := by
    simpa [prefixWord, tailWord_1998001, baseEnd_1998001] using wordTrace_append hprefix tailTrace_1998001
  have hstable : (prefixWord ++ tailWord_1998001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998001).length < 2 ^ (prefixWord ++ tailWord_1998001).sum := by decide
  have hdescent : baseEnd_1998001 < baseStart_1998001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998037 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 7]
def baseStart_1998037 : Nat := 118140960795 + 1998037 * 2 ^ 59
def prefixEnd_1998037 : Nat := 4983230072969 + 3 ^ 40 * 1998037 * 2
def baseEnd_1998037 : Nat := 113994816274167156083189

theorem tailTrace_1998037 : CollatzResearch.WordTrace tailWord_1998037 prefixEnd_1998037 113994816274167156083189 := by
  unfold tailWord_1998037
  simp only [CollatzResearch.WordTrace]
  refine ⟨72874396262460661397400365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48582930841640440931600243 72874396262460661397400365)
  ·
    refine ⟨27327898598422748024025137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72874396262460661397400365 27327898598422748024025137)
    ·
      refine ⟨20495923948817061018018853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27327898598422748024025137 20495923948817061018018853)
      ·
        refine ⟨3842985740403198940878535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20495923948817061018018853 3842985740403198940878535)
        ·
          refine ⟨5764478610604798411317803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3842985740403198940878535 5764478610604798411317803)
          ·
            refine ⟨8646717915907197616976705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5764478610604798411317803 8646717915907197616976705)
            ·
              refine ⟨6485038436930398212732529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8646717915907197616976705 6485038436930398212732529)
              ·
                refine ⟨4863778827697798659549397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6485038436930398212732529 4863778827697798659549397)
                ·
                  refine ⟨113994816274167156083189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4863778827697798659549397 113994816274167156083189)
                  ·
                    rfl

theorem cell23_1998037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_1998037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998037 prefixEnd_1998037 := by exact prefixLift 1998037
  have htrace : WordTrace (prefixWord ++ tailWord_1998037) baseStart_1998037 baseEnd_1998037 := by
    simpa [prefixWord, tailWord_1998037, baseEnd_1998037] using wordTrace_append hprefix tailTrace_1998037
  have hstable : (prefixWord ++ tailWord_1998037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998037).length < 2 ^ (prefixWord ++ tailWord_1998037).sum := by decide
  have hdescent : baseEnd_1998037 < baseStart_1998037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998067 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 2, 5]
def baseStart_1998067 : Nat := 118140960795 + 1998067 * 2 ^ 59
def prefixEnd_1998067 : Nat := 4983230072969 + 3 ^ 40 * 1998067 * 2
def baseEnd_1998067 : Nat := 341989583629046429124521

theorem tailTrace_1998067 : CollatzResearch.WordTrace tailWord_1998067 prefixEnd_1998067 341989583629046429124521 := by
  unfold tailWord_1998067
  simp only [CollatzResearch.WordTrace]
  refine ⟨72875490452351976520992455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48583660301567984347328303 72875490452351976520992455)
  ·
    refine ⟨109313235678527964781488683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72875490452351976520992455 109313235678527964781488683)
    ·
      refine ⟨163969853517791947172233025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109313235678527964781488683 163969853517791947172233025)
      ·
        refine ⟨122977390138343960379174769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163969853517791947172233025 122977390138343960379174769)
        ·
          refine ⟨92233042603757970284381077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122977390138343960379174769 92233042603757970284381077)
          ·
            refine ⟨4323423872051154857080363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92233042603757970284381077 4323423872051154857080363)
            ·
              refine ⟨6485135808076732285620545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323423872051154857080363 6485135808076732285620545)
              ·
                refine ⟨4863851856057549214215409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6485135808076732285620545 4863851856057549214215409)
                ·
                  refine ⟨3647888892043161910661557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4863851856057549214215409 3647888892043161910661557)
                  ·
                    refine ⟨341989583629046429124521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3647888892043161910661557 341989583629046429124521)
                    ·
                      rfl

theorem cell23_1998067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 5].length) (baseStart_1998067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998067 prefixEnd_1998067 := by exact prefixLift 1998067
  have htrace : WordTrace (prefixWord ++ tailWord_1998067) baseStart_1998067 baseEnd_1998067 := by
    simpa [prefixWord, tailWord_1998067, baseEnd_1998067] using wordTrace_append hprefix tailTrace_1998067
  have hstable : (prefixWord ++ tailWord_1998067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998067).length < 2 ^ (prefixWord ++ tailWord_1998067).sum := by decide
  have hdescent : baseEnd_1998067 < baseStart_1998067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998082 : List Nat := [3, 4, 1, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_1998082 : Nat := 118140960795 + 1998082 * 2 ^ 59
def prefixEnd_1998082 : Nat := 4983230072969 + 3 ^ 40 * 1998082 * 2
def baseEnd_1998082 : Nat := 1025976453096956728685995

theorem tailTrace_1998082 : CollatzResearch.WordTrace tailWord_1998082 prefixEnd_1998082 1025976453096956728685995 := by
  unfold tailWord_1998082
  simp only [CollatzResearch.WordTrace]
  refine ⟨18219009386824408520697125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48584025031531756055192333 18219009386824408520697125)
  ·
    refine ⟨3416064260029576597630711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18219009386824408520697125 3416064260029576597630711)
    ·
      refine ⟨5124096390044364896446067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3416064260029576597630711 5124096390044364896446067)
      ·
        refine ⟨7686144585066547344669101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5124096390044364896446067 7686144585066547344669101)
        ·
          refine ⟨2882304219399955254250913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7686144585066547344669101 2882304219399955254250913)
          ·
            refine ⟨2161728164549966440688185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2882304219399955254250913 2161728164549966440688185)
            ·
              refine ⟨1621296123412474830516139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161728164549966440688185 1621296123412474830516139)
              ·
                refine ⟨2431944185118712245774209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1621296123412474830516139 2431944185118712245774209)
                ·
                  refine ⟨1823958138839034184330657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2431944185118712245774209 1823958138839034184330657)
                  ·
                    refine ⟨1367968604129275638247993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1823958138839034184330657 1367968604129275638247993)
                    ·
                      refine ⟨1025976453096956728685995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1367968604129275638247993 1025976453096956728685995)
                      ·
                        rfl

theorem cell23_1998082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_1998082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998082 prefixEnd_1998082 := by exact prefixLift 1998082
  have htrace : WordTrace (prefixWord ++ tailWord_1998082) baseStart_1998082 baseEnd_1998082 := by
    simpa [prefixWord, tailWord_1998082, baseEnd_1998082] using wordTrace_append hprefix tailTrace_1998082
  have hstable : (prefixWord ++ tailWord_1998082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998082).length < 2 ^ (prefixWord ++ tailWord_1998082).sum := by decide
  have hdescent : baseEnd_1998082 < baseStart_1998082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998097 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 5, 4]
def baseStart_1998097 : Nat := 118140960795 + 1998097 * 2 ^ 59
def prefixEnd_1998097 : Nat := 4983230072969 + 3 ^ 40 * 1998097 * 2
def baseEnd_1998097 : Nat := 341994718435591389999475

theorem tailTrace_1998097 : CollatzResearch.WordTrace tailWord_1998097 prefixEnd_1998097 341994718435591389999475 := by
  unfold tailWord_1998097
  simp only [CollatzResearch.WordTrace]
  refine ⟨72876584642243291644584545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48584389761495527763056363 72876584642243291644584545)
  ·
    refine ⟨54657438481682468733438409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72876584642243291644584545 54657438481682468733438409)
    ·
      refine ⟨40993078861261851550078807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54657438481682468733438409 40993078861261851550078807)
      ·
        refine ⟨61489618291892777325118211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40993078861261851550078807 61489618291892777325118211)
        ·
          refine ⟨92234427437839165987677317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61489618291892777325118211 92234427437839165987677317)
          ·
            refine ⟨17293955144594843622689497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92234427437839165987677317 17293955144594843622689497)
            ·
              refine ⟨12970466358446132717017123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17293955144594843622689497 12970466358446132717017123)
              ·
                refine ⟨19455699537669199075525685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12970466358446132717017123 19455699537669199075525685)
                ·
                  refine ⟨1823971831656487413330533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19455699537669199075525685 1823971831656487413330533)
                  ·
                    refine ⟨341994718435591389999475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1823971831656487413330533 341994718435591389999475)
                    ·
                      rfl

theorem cell23_1998097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_1998097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998097 prefixEnd_1998097 := by exact prefixLift 1998097
  have htrace : WordTrace (prefixWord ++ tailWord_1998097) baseStart_1998097 baseEnd_1998097 := by
    simpa [prefixWord, tailWord_1998097, baseEnd_1998097] using wordTrace_append hprefix tailTrace_1998097
  have hstable : (prefixWord ++ tailWord_1998097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998097).length < 2 ^ (prefixWord ++ tailWord_1998097).sum := by decide
  have hdescent : baseEnd_1998097 < baseStart_1998097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998104 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 2, 1, 4]
def baseStart_1998104 : Nat := 118140960795 + 1998104 * 2 ^ 59
def prefixEnd_1998104 : Nat := 4983230072969 + 3 ^ 40 * 1998104 * 2
def baseEnd_1998104 : Nat := 1025987749671355642610893

theorem tailTrace_1998104 : CollatzResearch.WordTrace tailWord_1998104 prefixEnd_1998104 1025987749671355642610893 := by
  unfold tailWord_1998104
  simp only [CollatzResearch.WordTrace]
  refine ⟨36438419976608965920044683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48584559968811954560059577 36438419976608965920044683)
  ·
    refine ⟨54657629964913448880067025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36438419976608965920044683 54657629964913448880067025)
    ·
      refine ⟨40993222473685086660050269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54657629964913448880067025 40993222473685086660050269)
      ·
        refine ⟨15372458427631907497518851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40993222473685086660050269 15372458427631907497518851)
        ·
          refine ⟨23058687641447861246278277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15372458427631907497518851 23058687641447861246278277)
          ·
            refine ⟨4323503932771473983677177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23058687641447861246278277 4323503932771473983677177)
            ·
              refine ⟨3242627949578605487757883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4323503932771473983677177 3242627949578605487757883)
              ·
                refine ⟨4863941924367908231636825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3242627949578605487757883 4863941924367908231636825)
                ·
                  refine ⟨3647956443275931173727619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4863941924367908231636825 3647956443275931173727619)
                  ·
                    refine ⟨5471934664913896760591429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3647956443275931173727619 5471934664913896760591429)
                    ·
                      refine ⟨1025987749671355642610893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5471934664913896760591429 1025987749671355642610893)
                      ·
                        rfl

theorem cell23_1998104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_1998104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998104 prefixEnd_1998104 := by exact prefixLift 1998104
  have htrace : WordTrace (prefixWord ++ tailWord_1998104) baseStart_1998104 baseEnd_1998104 := by
    simpa [prefixWord, tailWord_1998104, baseEnd_1998104] using wordTrace_append hprefix tailTrace_1998104
  have hstable : (prefixWord ++ tailWord_1998104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998104).length < 2 ^ (prefixWord ++ tailWord_1998104).sum := by decide
  have hdescent : baseEnd_1998104 < baseStart_1998104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998131 : List Nat := [1, 1, 1, 2, 5, 3, 1, 4, 1, 4]
def baseStart_1998131 : Nat := 118140960795 + 1998131 * 2 ^ 59
def prefixEnd_1998131 : Nat := 4983230072969 + 3 ^ 40 * 1998131 * 2
def baseEnd_1998131 : Nat := 342000537883009012324423

theorem tailTrace_1998131 : CollatzResearch.WordTrace tailWord_1998131 prefixEnd_1998131 342000537883009012324423 := by
  unfold tailWord_1998131
  simp only [CollatzResearch.WordTrace]
  refine ⟨72877824724120115451322247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48585216482746743634214831 72877824724120115451322247)
  ·
    refine ⟨109316737086180173176983371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72877824724120115451322247 109316737086180173176983371)
    ·
      refine ⟨163975105629270259765475057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109316737086180173176983371 163975105629270259765475057)
      ·
        refine ⟨122981329221952694824106293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163975105629270259765475057 122981329221952694824106293)
        ·
          refine ⟨11529499614558065139759965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122981329221952694824106293 11529499614558065139759965)
          ·
            refine ⟨4323562355459274427409987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11529499614558065139759965 4323562355459274427409987)
            ·
              refine ⟨6485343533188911641114981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323562355459274427409987 6485343533188911641114981)
              ·
                refine ⟨1216001912472920932709059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6485343533188911641114981 1216001912472920932709059)
                ·
                  refine ⟨1824002868709381399063589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216001912472920932709059 1824002868709381399063589)
                  ·
                    refine ⟨342000537883009012324423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1824002868709381399063589 342000537883009012324423)
                    ·
                      rfl

theorem cell23_1998131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 1, 4].length) (baseStart_1998131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998131 prefixEnd_1998131 := by exact prefixLift 1998131
  have htrace : WordTrace (prefixWord ++ tailWord_1998131) baseStart_1998131 baseEnd_1998131 := by
    simpa [prefixWord, tailWord_1998131, baseEnd_1998131] using wordTrace_append hprefix tailTrace_1998131
  have hstable : (prefixWord ++ tailWord_1998131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998131).length < 2 ^ (prefixWord ++ tailWord_1998131).sum := by decide
  have hdescent : baseEnd_1998131 < baseStart_1998131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998188 : List Nat := [2, 2, 1, 1, 5, 1, 2, 4, 1, 1, 3]
def baseStart_1998188 : Nat := 118140960795 + 1998188 * 2 ^ 59
def prefixEnd_1998188 : Nat := 4983230072969 + 3 ^ 40 * 1998188 * 2
def baseEnd_1998188 : Nat := 1026030882046333313960507

theorem tailTrace_1998188 : CollatzResearch.WordTrace tailWord_1998188 prefixEnd_1998188 1026030882046333313960507 := by
  unfold tailWord_1998188
  simp only [CollatzResearch.WordTrace]
  refine ⟨36439951842456807093073609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48586602456609076124098145 36439951842456807093073609)
  ·
    refine ⟨27329963881842605319805207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36439951842456807093073609 27329963881842605319805207)
    ·
      refine ⟨40994945822763907979707811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27329963881842605319805207 40994945822763907979707811)
      ·
        refine ⟨61492418734145861969561717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40994945822763907979707811 61492418734145861969561717)
        ·
          refine ⟨5764914256326174559646411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61492418734145861969561717 5764914256326174559646411)
          ·
            refine ⟨8647371384489261839469617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5764914256326174559646411 8647371384489261839469617)
            ·
              refine ⟨6485528538366946379602213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8647371384489261839469617 6485528538366946379602213)
              ·
                refine ⟨1216036600943802446175415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6485528538366946379602213 1216036600943802446175415)
                ·
                  refine ⟨1824054901415703669263123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216036600943802446175415 1824054901415703669263123)
                  ·
                    refine ⟨2736082352123555503894685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1824054901415703669263123 2736082352123555503894685)
                    ·
                      refine ⟨1026030882046333313960507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2736082352123555503894685 1026030882046333313960507)
                      ·
                        rfl

theorem cell23_1998188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 1, 1, 3].length) (baseStart_1998188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998188 prefixEnd_1998188 := by exact prefixLift 1998188
  have htrace : WordTrace (prefixWord ++ tailWord_1998188) baseStart_1998188 baseEnd_1998188 := by
    simpa [prefixWord, tailWord_1998188, baseEnd_1998188] using wordTrace_append hprefix tailTrace_1998188
  have hstable : (prefixWord ++ tailWord_1998188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998188).length < 2 ^ (prefixWord ++ tailWord_1998188).sum := by decide
  have hdescent : baseEnd_1998188 < baseStart_1998188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998211 : List Nat := [1, 1, 1, 3, 5, 2, 2, 2, 1, 1, 4]
def baseStart_1998211 : Nat := 118140960795 + 1998211 * 2 ^ 59
def prefixEnd_1998211 : Nat := 4983230072969 + 3 ^ 40 * 1998211 * 2
def baseEnd_1998211 : Nat := 1026042692101386723972901

theorem tailTrace_1998211 : CollatzResearch.WordTrace tailWord_1998211 prefixEnd_1998211 1026042692101386723972901 := by
  unfold tailWord_1998211
  simp only [CollatzResearch.WordTrace]
  refine ⟨72880742563830289114234487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48587161709220192742822991 72880742563830289114234487)
  ·
    refine ⟨109321113845745433671351731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72880742563830289114234487 109321113845745433671351731)
    ·
      refine ⟨163981670768618150507027597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109321113845745433671351731 163981670768618150507027597)
      ·
        refine ⟨61493126538231806440135349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163981670768618150507027597 61493126538231806440135349)
        ·
          refine ⟨5764980612959231853762689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61493126538231806440135349 5764980612959231853762689)
          ·
            refine ⟨4323735459719423890322017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5764980612959231853762689 4323735459719423890322017)
            ·
              refine ⟨3242801594789567917741513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4323735459719423890322017 3242801594789567917741513)
              ·
                refine ⟨2432101196092175938306135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3242801594789567917741513 2432101196092175938306135)
                ·
                  refine ⟨3648151794138263907459203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2432101196092175938306135 3648151794138263907459203)
                  ·
                    refine ⟨5472227691207395861188805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3648151794138263907459203 5472227691207395861188805)
                    ·
                      refine ⟨1026042692101386723972901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5472227691207395861188805 1026042692101386723972901)
                      ·
                        rfl

theorem cell23_1998211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_1998211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998211 prefixEnd_1998211 := by exact prefixLift 1998211
  have htrace : WordTrace (prefixWord ++ tailWord_1998211) baseStart_1998211 baseEnd_1998211 := by
    simpa [prefixWord, tailWord_1998211, baseEnd_1998211] using wordTrace_append hprefix tailTrace_1998211
  have hstable : (prefixWord ++ tailWord_1998211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998211).length < 2 ^ (prefixWord ++ tailWord_1998211).sum := by decide
  have hdescent : baseEnd_1998211 < baseStart_1998211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998222 : List Nat := [4, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3]
def baseStart_1998222 : Nat := 118140960795 + 1998222 * 2 ^ 59
def prefixEnd_1998222 : Nat := 4983230072969 + 3 ^ 40 * 1998222 * 2
def baseEnd_1998222 : Nat := 1026048340388586180935351

theorem tailTrace_1998222 : CollatzResearch.WordTrace tailWord_1998222 prefixEnd_1998222 1026048340388586180935351 := by
  unfold tailWord_1998222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9110142970848804749110615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48587429177860291995256613 9110142970848804749110615)
  ·
    refine ⟨13665214456273207123665923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9110142970848804749110615 13665214456273207123665923)
    ·
      refine ⟨20497821684409810685498885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13665214456273207123665923 20497821684409810685498885)
      ·
        refine ⟨3843341565826839503531041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20497821684409810685498885 3843341565826839503531041)
        ·
          refine ⟨2882506174370129627648281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3843341565826839503531041 2882506174370129627648281)
          ·
            refine ⟨2161879630777597220736211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2882506174370129627648281 2161879630777597220736211)
            ·
              refine ⟨3242819446166395831104317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2161879630777597220736211 3242819446166395831104317)
              ·
                refine ⟨1216057292312398436664119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3242819446166395831104317 1216057292312398436664119)
                ·
                  refine ⟨1824085938468597654996179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216057292312398436664119 1824085938468597654996179)
                  ·
                    refine ⟨2736128907702896482494269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1824085938468597654996179 2736128907702896482494269)
                    ·
                      refine ⟨1026048340388586180935351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2736128907702896482494269 1026048340388586180935351)
                      ·
                        rfl

theorem cell23_1998222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_1998222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998222 prefixEnd_1998222 := by exact prefixLift 1998222
  have htrace : WordTrace (prefixWord ++ tailWord_1998222) baseStart_1998222 baseEnd_1998222 := by
    simpa [prefixWord, tailWord_1998222, baseEnd_1998222] using wordTrace_append hprefix tailTrace_1998222
  have hstable : (prefixWord ++ tailWord_1998222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998222).length < 2 ^ (prefixWord ++ tailWord_1998222).sum := by decide
  have hdescent : baseEnd_1998222 < baseStart_1998222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998265 : List Nat := [1, 2, 1, 4, 5, 1, 1, 2, 1, 2, 3]
def baseStart_1998265 : Nat := 118140960795 + 1998265 * 2 ^ 59
def prefixEnd_1998265 : Nat := 4983230072969 + 3 ^ 40 * 1998265 * 2
def baseEnd_1998265 : Nat := 1026070420056729512697653

theorem tailTrace_1998265 : CollatzResearch.WordTrace tailWord_1998265 prefixEnd_1998265 1026070420056729512697653 := by
  unfold tailWord_1998265
  simp only [CollatzResearch.WordTrace]
  refine ⟨72882712105634656336700249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48588474737089770891133499 72882712105634656336700249)
  ·
    refine ⟨54662034079225992252525187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72882712105634656336700249 54662034079225992252525187)
    ·
      refine ⟨81993051118838988378787781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54662034079225992252525187 81993051118838988378787781)
      ·
        refine ⟨15373697084782310321022709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81993051118838988378787781 15373697084782310321022709)
        ·
          refine ⟨1441284101698341592595879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15373697084782310321022709 1441284101698341592595879)
          ·
            refine ⟨2161926152547512388893819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441284101698341592595879 2161926152547512388893819)
            ·
              refine ⟨3242889228821268583340729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2161926152547512388893819 3242889228821268583340729)
              ·
                refine ⟨2432166921615951437505547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3242889228821268583340729 2432166921615951437505547)
                ·
                  refine ⟨3648250382423927156258321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2432166921615951437505547 3648250382423927156258321)
                  ·
                    refine ⟨2736187786817945367193741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3648250382423927156258321 2736187786817945367193741)
                    ·
                      refine ⟨1026070420056729512697653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2736187786817945367193741 1026070420056729512697653)
                      ·
                        rfl

theorem cell23_1998265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_1998265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998265 prefixEnd_1998265 := by exact prefixLift 1998265
  have htrace : WordTrace (prefixWord ++ tailWord_1998265) baseStart_1998265 baseEnd_1998265 := by
    simpa [prefixWord, tailWord_1998265, baseEnd_1998265] using wordTrace_append hprefix tailTrace_1998265
  have hstable : (prefixWord ++ tailWord_1998265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998265).length < 2 ^ (prefixWord ++ tailWord_1998265).sum := by decide
  have hdescent : baseEnd_1998265 < baseStart_1998265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998318 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_1998318 : Nat := 118140960795 + 1998318 * 2 ^ 59
def prefixEnd_1998318 : Nat := 4983230072969 + 3 ^ 40 * 1998318 * 2
def baseEnd_1998318 : Nat := 1026097634531417805334909

theorem tailTrace_1998318 : CollatzResearch.WordTrace tailWord_1998318 prefixEnd_1998318 1026097634531417805334909 := by
  unfold tailWord_1998318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9110580646805330798547451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48589763449628430925586405 9110580646805330798547451)
  ·
    refine ⟨13665870970207996197821177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9110580646805330798547451 13665870970207996197821177)
    ·
      refine ⟨10249403227655997148365883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13665870970207996197821177 10249403227655997148365883)
      ·
        refine ⟨15374104841483995722548825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10249403227655997148365883 15374104841483995722548825)
        ·
          refine ⟨11530578631112996791911619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15374104841483995722548825 11530578631112996791911619)
          ·
            refine ⟨17295867946669495187867429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11530578631112996791911619 17295867946669495187867429)
            ·
              refine ⟨3242975240000530347725143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17295867946669495187867429 3242975240000530347725143)
              ·
                refine ⟨4864462860000795521587715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3242975240000530347725143 4864462860000795521587715)
                ·
                  refine ⟨7296694290001193282381573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864462860000795521587715 7296694290001193282381573)
                  ·
                    refine ⟨1368130179375223740446545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7296694290001193282381573 1368130179375223740446545)
                    ·
                      refine ⟨1026097634531417805334909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1368130179375223740446545 1026097634531417805334909)
                      ·
                        rfl

theorem cell23_1998318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_1998318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998318 prefixEnd_1998318 := by exact prefixLift 1998318
  have htrace : WordTrace (prefixWord ++ tailWord_1998318) baseStart_1998318 baseEnd_1998318 := by
    simpa [prefixWord, tailWord_1998318, baseEnd_1998318] using wordTrace_append hprefix tailTrace_1998318
  have hstable : (prefixWord ++ tailWord_1998318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998318).length < 2 ^ (prefixWord ++ tailWord_1998318).sum := by decide
  have hdescent : baseEnd_1998318 < baseStart_1998318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998364 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1998364 : Nat := 118140960795 + 1998364 * 2 ^ 59
def prefixEnd_1998364 : Nat := 4983230072969 + 3 ^ 40 * 1998364 * 2
def baseEnd_1998364 : Nat := 1026121254641524625359697

theorem tailTrace_1998364 : CollatzResearch.WordTrace tailWord_1998364 prefixEnd_1998364 1026121254641524625359697 := by
  unfold tailWord_1998364
  simp only [CollatzResearch.WordTrace]
  refine ⟨36443161466137998122277073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48590881954850664163036097 36443161466137998122277073)
  ·
    refine ⟨27332371099603498591707805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36443161466137998122277073 27332371099603498591707805)
    ·
      refine ⟨10249639162351311971890427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27332371099603498591707805 10249639162351311971890427)
      ·
        refine ⟨15374458743526967957835641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10249639162351311971890427 15374458743526967957835641)
        ·
          refine ⟨11530844057645225968376731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15374458743526967957835641 11530844057645225968376731)
          ·
            refine ⟨17296266086467838952565097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11530844057645225968376731 17296266086467838952565097)
            ·
              refine ⟨12972199564850879214423823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17296266086467838952565097 12972199564850879214423823)
              ·
                refine ⟨19458299347276318821635735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12972199564850879214423823 19458299347276318821635735)
                ·
                  refine ⟨29187449020914478232453603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19458299347276318821635735 29187449020914478232453603)
                  ·
                    refine ⟨43781173531371717348680405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29187449020914478232453603 43781173531371717348680405)
                    ·
                      refine ⟨1026121254641524625359697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43781173531371717348680405 1026121254641524625359697)
                      ·
                        rfl

theorem cell23_1998364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1998364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998364 prefixEnd_1998364 := by exact prefixLift 1998364
  have htrace : WordTrace (prefixWord ++ tailWord_1998364) baseStart_1998364 baseEnd_1998364 := by
    simpa [prefixWord, tailWord_1998364, baseEnd_1998364] using wordTrace_append hprefix tailTrace_1998364
  have hstable : (prefixWord ++ tailWord_1998364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998364).length < 2 ^ (prefixWord ++ tailWord_1998364).sum := by decide
  have hdescent : baseEnd_1998364 < baseStart_1998364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998418 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_1998418 : Nat := 118140960795 + 1998418 * 2 ^ 59
def prefixEnd_1998418 : Nat := 4983230072969 + 3 ^ 40 * 1998418 * 2
def baseEnd_1998418 : Nat := 342049660865622471361483

theorem tailTrace_1998418 : CollatzResearch.WordTrace tailWord_1998418 prefixEnd_1998418 342049660865622471361483 := by
  unfold tailWord_1998418
  simp only [CollatzResearch.WordTrace]
  refine ⟨18222073118520090866754977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48592194982720242311346605 18222073118520090866754977)
  ·
    refine ⟨13666554838890068150066233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18222073118520090866754977 13666554838890068150066233)
    ·
      refine ⟨10249916129167551112549675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13666554838890068150066233 10249916129167551112549675)
      ·
        refine ⟨15374874193751326668824513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10249916129167551112549675 15374874193751326668824513)
        ·
          refine ⟨11531155645313495001618385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15374874193751326668824513 11531155645313495001618385)
          ·
            refine ⟨8648366733985121251213789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11531155645313495001618385 8648366733985121251213789)
            ·
              refine ⟨3243137525244420469205171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8648366733985121251213789 3243137525244420469205171)
              ·
                refine ⟨4864706287866630703807757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243137525244420469205171 4864706287866630703807757)
                ·
                  refine ⟨1824264857949986513927909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4864706287866630703807757 1824264857949986513927909)
                  ·
                    refine ⟨342049660865622471361483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1824264857949986513927909 342049660865622471361483)
                    ·
                      rfl

theorem cell23_1998418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_1998418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998418 prefixEnd_1998418 := by exact prefixLift 1998418
  have htrace : WordTrace (prefixWord ++ tailWord_1998418) baseStart_1998418 baseEnd_1998418 := by
    simpa [prefixWord, tailWord_1998418, baseEnd_1998418] using wordTrace_append hprefix tailTrace_1998418
  have hstable : (prefixWord ++ tailWord_1998418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998418).length < 2 ^ (prefixWord ++ tailWord_1998418).sum := by decide
  have hdescent : baseEnd_1998418 < baseStart_1998418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998445 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_1998445 : Nat := 118140960795 + 1998445 * 2 ^ 59
def prefixEnd_1998445 : Nat := 4983230072969 + 3 ^ 40 * 1998445 * 2
def baseEnd_1998445 : Nat := 1026162846574538808446825

theorem tailTrace_1998445 : CollatzResearch.WordTrace tailWord_1998445 prefixEnd_1998445 1026162846574538808446825 := by
  unfold tailWord_1998445
  simp only [CollatzResearch.WordTrace]
  refine ⟨72889277244982547078252789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48592851496655031385501859 72889277244982547078252789)
  ·
    refine ⟨6833369741717113788586199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72889277244982547078252789 6833369741717113788586199)
    ·
      refine ⟨10250054612575670682879299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6833369741717113788586199 10250054612575670682879299)
      ·
        refine ⟨15375081918863506024318949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10250054612575670682879299 15375081918863506024318949)
        ·
          refine ⟨2882827859786907379559803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15375081918863506024318949 2882827859786907379559803)
          ·
            refine ⟨4324241789680361069339705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2882827859786907379559803 4324241789680361069339705)
            ·
              refine ⟨3243181342260270802004779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4324241789680361069339705 3243181342260270802004779)
              ·
                refine ⟨4864772013390406203007169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243181342260270802004779 4864772013390406203007169)
                ·
                  refine ⟨3648579010042804652255377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4864772013390406203007169 3648579010042804652255377)
                  ·
                    refine ⟨2736434257532103489191533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3648579010042804652255377 2736434257532103489191533)
                    ·
                      refine ⟨1026162846574538808446825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2736434257532103489191533 1026162846574538808446825)
                      ·
                        rfl

theorem cell23_1998445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_1998445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998445 prefixEnd_1998445 := by exact prefixLift 1998445
  have htrace : WordTrace (prefixWord ++ tailWord_1998445) baseStart_1998445 baseEnd_1998445 := by
    simpa [prefixWord, tailWord_1998445, baseEnd_1998445] using wordTrace_append hprefix tailTrace_1998445
  have hstable : (prefixWord ++ tailWord_1998445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998445).length < 2 ^ (prefixWord ++ tailWord_1998445).sum := by decide
  have hdescent : baseEnd_1998445 < baseStart_1998445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998451 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 5, 5, 2]
def baseStart_1998451 : Nat := 118140960795 + 1998451 * 2 ^ 59
def prefixEnd_1998451 : Nat := 4983230072969 + 3 ^ 40 * 1998451 * 2
def baseEnd_1998451 : Nat := 1026165927458465784971797

theorem tailTrace_1998451 : CollatzResearch.WordTrace tailWord_1998451 prefixEnd_1998451 1026165927458465784971797 := by
  unfold tailWord_1998451
  simp only [CollatzResearch.WordTrace]
  refine ⟨72889496082960810102971207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48592997388640540068647471 72889496082960810102971207)
  ·
    refine ⟨109334244124441215154456811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72889496082960810102971207 109334244124441215154456811)
    ·
      refine ⟨164001366186661822731685217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109334244124441215154456811 164001366186661822731685217)
      ·
        refine ⟨123001024639996367048763913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164001366186661822731685217 123001024639996367048763913)
        ·
          refine ⟨92250768479997275286572935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123001024639996367048763913 92250768479997275286572935)
          ·
            refine ⟨138376152719995912929859403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92250768479997275286572935 138376152719995912929859403)
            ·
              refine ⟨207564229079993869394789105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138376152719995912929859403 207564229079993869394789105)
              ·
                refine ⟨155673171809995402046091829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207564229079993869394789105 155673171809995402046091829)
                ·
                  refine ⟨14594359857187068941821109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155673171809995402046091829 14594359857187068941821109)
                  ·
                    refine ⟨1368221236611287713295729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14594359857187068941821109 1368221236611287713295729)
                    ·
                      refine ⟨1026165927458465784971797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1368221236611287713295729 1026165927458465784971797)
                      ·
                        rfl

theorem cell23_1998451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 5, 2].length) (baseStart_1998451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998451 prefixEnd_1998451 := by exact prefixLift 1998451
  have htrace : WordTrace (prefixWord ++ tailWord_1998451) baseStart_1998451 baseEnd_1998451 := by
    simpa [prefixWord, tailWord_1998451, baseEnd_1998451] using wordTrace_append hprefix tailTrace_1998451
  have hstable : (prefixWord ++ tailWord_1998451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998451).length < 2 ^ (prefixWord ++ tailWord_1998451).sum := by decide
  have hdescent : baseEnd_1998451 < baseStart_1998451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998475 : List Nat := [1, 1, 1, 1, 4, 1, 5, 4, 1, 1, 3]
def baseStart_1998475 : Nat := 118140960795 + 1998475 * 2 ^ 59
def prefixEnd_1998475 : Nat := 4983230072969 + 3 ^ 40 * 1998475 * 2
def baseEnd_1998475 : Nat := 1026178250994173691071687

theorem tailTrace_1998475 : CollatzResearch.WordTrace tailWord_1998475 prefixEnd_1998475 1026178250994173691071687 := by
  unfold tailWord_1998475
  simp only [CollatzResearch.WordTrace]
  refine ⟨72890371434873862201844879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48593580956582574801229919 72890371434873862201844879)
  ·
    refine ⟨109335557152310793302767319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72890371434873862201844879 109335557152310793302767319)
    ·
      refine ⟨164003335728466189954150979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109335557152310793302767319 164003335728466189954150979)
      ·
        refine ⟨246005003592699284931226469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164003335728466189954150979 246005003592699284931226469)
        ·
          refine ⟨46125938173631115924604963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246005003592699284931226469 46125938173631115924604963)
          ·
            refine ⟨69188907260446673886907445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46125938173631115924604963 69188907260446673886907445)
            ·
              refine ⟨6486460055666875676897573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69188907260446673886907445 6486460055666875676897573)
              ·
                refine ⟨1216211260437539189418295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6486460055666875676897573 1216211260437539189418295)
                ·
                  refine ⟨1824316890656308784127443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216211260437539189418295 1824316890656308784127443)
                  ·
                    refine ⟨2736475335984463176191165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1824316890656308784127443 2736475335984463176191165)
                    ·
                      refine ⟨1026178250994173691071687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2736475335984463176191165 1026178250994173691071687)
                      ·
                        rfl

theorem cell23_1998475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 1, 1, 3].length) (baseStart_1998475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998475 prefixEnd_1998475 := by exact prefixLift 1998475
  have htrace : WordTrace (prefixWord ++ tailWord_1998475) baseStart_1998475 baseEnd_1998475 := by
    simpa [prefixWord, tailWord_1998475, baseEnd_1998475] using wordTrace_append hprefix tailTrace_1998475
  have hstable : (prefixWord ++ tailWord_1998475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998475).length < 2 ^ (prefixWord ++ tailWord_1998475).sum := by decide
  have hdescent : baseEnd_1998475 < baseStart_1998475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998511 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 4]
def baseStart_1998511 : Nat := 118140960795 + 1998511 * 2 ^ 59
def prefixEnd_1998511 : Nat := 4983230072969 + 3 ^ 40 * 1998511 * 2
def baseEnd_1998511 : Nat := 1026196736297735550221521

theorem tailTrace_1998511 : CollatzResearch.WordTrace tailWord_1998511 prefixEnd_1998511 1026196736297735550221521 := by
  unfold tailWord_1998511
  simp only [CollatzResearch.WordTrace]
  refine ⟨72891684462743440350155387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48594456308495626900103591 72891684462743440350155387)
  ·
    refine ⟨109337526694115160525233081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72891684462743440350155387 109337526694115160525233081)
    ·
      refine ⟨82003145020586370393924811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109337526694115160525233081 82003145020586370393924811)
      ·
        refine ⟨123004717530879555590887217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82003145020586370393924811 123004717530879555590887217)
        ·
          refine ⟨92253538148159666693165413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123004717530879555590887217 92253538148159666693165413)
          ·
            refine ⟨17297538402779937504968515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92253538148159666693165413 17297538402779937504968515)
            ·
              refine ⟨25946307604169906257452773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17297538402779937504968515 25946307604169906257452773)
              ·
                refine ⟨4864932675781857423272395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25946307604169906257452773 4864932675781857423272395)
                ·
                  refine ⟨7297399013672786134908593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864932675781857423272395 7297399013672786134908593)
                  ·
                    refine ⟨5473049260254589601181445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7297399013672786134908593 5473049260254589601181445)
                    ·
                      refine ⟨1026196736297735550221521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5473049260254589601181445 1026196736297735550221521)
                      ·
                        rfl

theorem cell23_1998511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_1998511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998511 prefixEnd_1998511 := by exact prefixLift 1998511
  have htrace : WordTrace (prefixWord ++ tailWord_1998511) baseStart_1998511 baseEnd_1998511 := by
    simpa [prefixWord, tailWord_1998511, baseEnd_1998511] using wordTrace_append hprefix tailTrace_1998511
  have hstable : (prefixWord ++ tailWord_1998511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998511).length < 2 ^ (prefixWord ++ tailWord_1998511).sum := by decide
  have hdescent : baseEnd_1998511 < baseStart_1998511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998532 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_1998532 : Nat := 118140960795 + 1998532 * 2 ^ 59
def prefixEnd_1998532 : Nat := 4983230072969 + 3 ^ 40 * 1998532 * 2
def baseEnd_1998532 : Nat := 1026207519391479968058925

theorem tailTrace_1998532 : CollatzResearch.WordTrace tailWord_1998532 prefixEnd_1998532 1026207519391479968058925 := by
  unfold tailWord_1998532
  simp only [CollatzResearch.WordTrace]
  refine ⟨36446225197833680468334925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48594966930444907291113233 36446225197833680468334925)
  ·
    refine ⟨13667334449187630175625597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36446225197833680468334925 13667334449187630175625597)
    ·
      refine ⟨5125250418445361315859599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13667334449187630175625597 5125250418445361315859599)
      ·
        refine ⟨7687875627668041973789399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5125250418445361315859599 7687875627668041973789399)
        ·
          refine ⟨11531813441502062960684099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7687875627668041973789399 11531813441502062960684099)
          ·
            refine ⟨17297720162253094441026149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11531813441502062960684099 17297720162253094441026149)
            ·
              refine ⟨3243322530422455207692403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17297720162253094441026149 3243322530422455207692403)
              ·
                refine ⟨4864983795633682811538605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243322530422455207692403 4864983795633682811538605)
                ·
                  refine ⟨1824368923362631054326977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4864983795633682811538605 1824368923362631054326977)
                  ·
                    refine ⟨1368276692521973290745233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1824368923362631054326977 1368276692521973290745233)
                    ·
                      refine ⟨1026207519391479968058925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1368276692521973290745233 1026207519391479968058925)
                      ·
                        rfl

theorem cell23_1998532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_1998532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998532 prefixEnd_1998532 := by exact prefixLift 1998532
  have htrace : WordTrace (prefixWord ++ tailWord_1998532) baseStart_1998532 baseEnd_1998532 := by
    simpa [prefixWord, tailWord_1998532, baseEnd_1998532] using wordTrace_append hprefix tailTrace_1998532
  have hstable : (prefixWord ++ tailWord_1998532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998532).length < 2 ^ (prefixWord ++ tailWord_1998532).sum := by decide
  have hdescent : baseEnd_1998532 < baseStart_1998532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998575 : List Nat := [1, 1, 2, 1, 5, 1, 1, 5, 1, 3, 2]
def baseStart_1998575 : Nat := 118140960795 + 1998575 * 2 ^ 59
def prefixEnd_1998575 : Nat := 4983230072969 + 3 ^ 40 * 1998575 * 2
def baseEnd_1998575 : Nat := 1026229599059623299821227

theorem tailTrace_1998575 : CollatzResearch.WordTrace tailWord_1998575 prefixEnd_1998575 1026229599059623299821227 := by
  unfold tailWord_1998575
  simp only [CollatzResearch.WordTrace]
  refine ⟨72894018734511579280485179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48596012489674386186990119 72894018734511579280485179)
  ·
    refine ⟨109341028101767368920727769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72894018734511579280485179 109341028101767368920727769)
    ·
      refine ⟨82005771076325526690545827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109341028101767368920727769 82005771076325526690545827)
      ·
        refine ⟨123008656614488290035818741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82005771076325526690545827 123008656614488290035818741)
        ·
          refine ⟨11532061557608277190858007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123008656614488290035818741 11532061557608277190858007)
          ·
            refine ⟨17298092336412415786287011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11532061557608277190858007 17298092336412415786287011)
            ·
              refine ⟨25947138504618623679430517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17298092336412415786287011 25947138504618623679430517)
              ·
                refine ⟨2432544234807995969946611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25947138504618623679430517 2432544234807995969946611)
                ·
                  refine ⟨3648816352211993954919917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2432544234807995969946611 3648816352211993954919917)
                  ·
                    refine ⟨1368306132079497733094969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3648816352211993954919917 1368306132079497733094969)
                    ·
                      refine ⟨1026229599059623299821227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1368306132079497733094969 1026229599059623299821227)
                      ·
                        rfl

theorem cell23_1998575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 3, 2].length) (baseStart_1998575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998575 prefixEnd_1998575 := by exact prefixLift 1998575
  have htrace : WordTrace (prefixWord ++ tailWord_1998575) baseStart_1998575 baseEnd_1998575 := by
    simpa [prefixWord, tailWord_1998575, baseEnd_1998575] using wordTrace_append hprefix tailTrace_1998575
  have hstable : (prefixWord ++ tailWord_1998575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998575).length < 2 ^ (prefixWord ++ tailWord_1998575).sum := by decide
  have hdescent : baseEnd_1998575 < baseStart_1998575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998601 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 1, 4, 4]
def baseStart_1998601 : Nat := 118140960795 + 1998601 * 2 ^ 59
def prefixEnd_1998601 : Nat := 4983230072969 + 3 ^ 40 * 1998601 * 2
def baseEnd_1998601 : Nat := 1026242949556640198096107

theorem tailTrace_1998601 : CollatzResearch.WordTrace tailWord_1998601 prefixEnd_1998601 1026242949556640198096107 := by
  unfold tailWord_1998601
  simp only [CollatzResearch.WordTrace]
  refine ⟨72894967032417385720931657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48596644688278257147287771 72894967032417385720931657)
  ·
    refine ⟨54671225274313039290698743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72894967032417385720931657 54671225274313039290698743)
    ·
      refine ⟨82006837911469558936048115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54671225274313039290698743 82006837911469558936048115)
      ·
        refine ⟨123010256867204338404072173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82006837911469558936048115 123010256867204338404072173)
        ·
          refine ⟨46128846325201626901527065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123010256867204338404072173 46128846325201626901527065)
          ·
            refine ⟨34596634743901220176145299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46128846325201626901527065 34596634743901220176145299)
            ·
              refine ⟨51894952115851830264217949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34596634743901220176145299 51894952115851830264217949)
              ·
                refine ⟨19460607043444436349081731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51894952115851830264217949 19460607043444436349081731)
                ·
                  refine ⟨29190910565166654523622597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19460607043444436349081731 29190910565166654523622597)
                  ·
                    refine ⟨5473295730968747723179237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29190910565166654523622597 5473295730968747723179237)
                    ·
                      refine ⟨1026242949556640198096107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5473295730968747723179237 1026242949556640198096107)
                      ·
                        rfl

theorem cell23_1998601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_1998601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998601 prefixEnd_1998601 := by exact prefixLift 1998601
  have htrace : WordTrace (prefixWord ++ tailWord_1998601) baseStart_1998601 baseEnd_1998601 := by
    simpa [prefixWord, tailWord_1998601, baseEnd_1998601] using wordTrace_append hprefix tailTrace_1998601
  have hstable : (prefixWord ++ tailWord_1998601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998601).length < 2 ^ (prefixWord ++ tailWord_1998601).sum := by decide
  have hdescent : baseEnd_1998601 < baseStart_1998601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998655 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 3]
def baseStart_1998655 : Nat := 118140960795 + 1998655 * 2 ^ 59
def prefixEnd_1998655 : Nat := 4983230072969 + 3 ^ 40 * 1998655 * 2
def baseEnd_1998655 : Nat := 1026270677511982986820859

theorem tailTrace_1998655 : CollatzResearch.WordTrace tailWord_1998655 prefixEnd_1998655 1026270677511982986820859 := by
  unfold tailWord_1998655
  simp only [CollatzResearch.WordTrace]
  refine ⟨72896936574221752943397419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48597957716147835295598279 72896936574221752943397419)
  ·
    refine ⟨109345404861332629415096129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72896936574221752943397419 109345404861332629415096129)
    ·
      refine ⟨82009053645999472061322097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109345404861332629415096129 82009053645999472061322097)
      ·
        refine ⟨61506790234499604045991573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82009053645999472061322097 61506790234499604045991573)
        ·
          refine ⟨2883130792242168939655855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61506790234499604045991573 2883130792242168939655855)
          ·
            refine ⟨4324696188363253409483783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883130792242168939655855 4324696188363253409483783)
            ·
              refine ⟨6487044282544880114225675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4324696188363253409483783 6487044282544880114225675)
              ·
                refine ⟨9730566423817320171338513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6487044282544880114225675 9730566423817320171338513)
                ·
                  refine ⟨7297924817862990128503885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9730566423817320171338513 7297924817862990128503885)
                  ·
                    refine ⟨2736721806698621298188957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7297924817862990128503885 2736721806698621298188957)
                    ·
                      refine ⟨1026270677511982986820859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2736721806698621298188957 1026270677511982986820859)
                      ·
                        rfl

theorem cell23_1998655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_1998655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998655 prefixEnd_1998655 := by exact prefixLift 1998655
  have htrace : WordTrace (prefixWord ++ tailWord_1998655) baseStart_1998655 baseEnd_1998655 := by
    simpa [prefixWord, tailWord_1998655, baseEnd_1998655] using wordTrace_append hprefix tailTrace_1998655
  have hstable : (prefixWord ++ tailWord_1998655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998655).length < 2 ^ (prefixWord ++ tailWord_1998655).sum := by decide
  have hdescent : baseEnd_1998655 < baseStart_1998655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998662 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_1998662 : Nat := 118140960795 + 1998662 * 2 ^ 59
def prefixEnd_1998662 : Nat := 4983230072969 + 3 ^ 40 * 1998662 * 2
def baseEnd_1998662 : Nat := 114030474652951606603703

theorem tailTrace_1998662 : CollatzResearch.WordTrace tailWord_1998662 prefixEnd_1998662 114030474652951606603703 := by
  unfold tailWord_1998662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2278037246412387285590695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48598127923464262092601493 2278037246412387285590695)
  ·
    refine ⟨3417055869618580928386043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2278037246412387285590695 3417055869618580928386043)
    ·
      refine ⟨5125583804427871392579065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3417055869618580928386043 5125583804427871392579065)
      ·
        refine ⟨3844187853320903544434299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5125583804427871392579065 3844187853320903544434299)
        ·
          refine ⟨5766281779981355316651449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844187853320903544434299 5766281779981355316651449)
          ·
            refine ⟨4324711334986016487488587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5766281779981355316651449 4324711334986016487488587)
            ·
              refine ⟨6487067002479024731232881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4324711334986016487488587 6487067002479024731232881)
              ·
                refine ⟨4865300251859268548424661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6487067002479024731232881 4865300251859268548424661)
                ·
                  refine ⟨114030474652951606603703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4865300251859268548424661 114030474652951606603703)
                  ·
                    rfl

theorem cell23_1998662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_1998662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998662 prefixEnd_1998662 := by exact prefixLift 1998662
  have htrace : WordTrace (prefixWord ++ tailWord_1998662) baseStart_1998662 baseEnd_1998662 := by
    simpa [prefixWord, tailWord_1998662, baseEnd_1998662] using wordTrace_append hprefix tailTrace_1998662
  have hstable : (prefixWord ++ tailWord_1998662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998662).length < 2 ^ (prefixWord ++ tailWord_1998662).sum := by decide
  have hdescent : baseEnd_1998662 < baseStart_1998662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998695 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_1998695 : Nat := 118140960795 + 1998695 * 2 ^ 59
def prefixEnd_1998695 : Nat := 4983230072969 + 3 ^ 40 * 1998695 * 2
def baseEnd_1998695 : Nat := 1026291216738162830320675

theorem tailTrace_1998695 : CollatzResearch.WordTrace tailWord_1998695 prefixEnd_1998695 1026291216738162830320675 := by
  unfold tailWord_1998695
  simp only [CollatzResearch.WordTrace]
  refine ⟨72898395494076839774853539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48598930329384559849902359 72898395494076839774853539)
  ·
    refine ⟨109347593241115259662280309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72898395494076839774853539 109347593241115259662280309)
    ·
      refine ⟨10251336866354555593338779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109347593241115259662280309 10251336866354555593338779)
      ·
        refine ⟨15377005299531833390008169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10251336866354555593338779 15377005299531833390008169)
        ·
          refine ⟨11532753974648875042506127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15377005299531833390008169 11532753974648875042506127)
          ·
            refine ⟨17299130961973312563759191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11532753974648875042506127 17299130961973312563759191)
            ·
              refine ⟨25948696442959968845638787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17299130961973312563759191 25948696442959968845638787)
              ·
                refine ⟨38923044664439953268458181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25948696442959968845638787 38923044664439953268458181)
                ·
                  refine ⟨7298070874582491237835909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38923044664439953268458181 7298070874582491237835909)
                  ·
                    refine ⟨1368388288984217107094233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7298070874582491237835909 1368388288984217107094233)
                    ·
                      refine ⟨1026291216738162830320675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1368388288984217107094233 1026291216738162830320675)
                      ·
                        rfl

theorem cell23_1998695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_1998695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998695 prefixEnd_1998695 := by exact prefixLift 1998695
  have htrace : WordTrace (prefixWord ++ tailWord_1998695) baseStart_1998695 baseEnd_1998695 := by
    simpa [prefixWord, tailWord_1998695, baseEnd_1998695] using wordTrace_append hprefix tailTrace_1998695
  have hstable : (prefixWord ++ tailWord_1998695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998695).length < 2 ^ (prefixWord ++ tailWord_1998695).sum := by decide
  have hdescent : baseEnd_1998695 < baseStart_1998695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998705 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 3, 4]
def baseStart_1998705 : Nat := 118140960795 + 1998705 * 2 ^ 59
def prefixEnd_1998705 : Nat := 4983230072969 + 3 ^ 40 * 1998705 * 2
def baseEnd_1998705 : Nat := 342098783848235930398543

theorem tailTrace_1998705 : CollatzResearch.WordTrace tailWord_1998705 prefixEnd_1998705 342098783848235930398543 := by
  unfold tailWord_1998705
  simp only [CollatzResearch.WordTrace]
  refine ⟨72898760224040611482717569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48599173482693740988478379 72898760224040611482717569)
  ·
    refine ⟨54674070168030458612038177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72898760224040611482717569 54674070168030458612038177)
    ·
      refine ⟨41005552626022843959028633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54674070168030458612038177 41005552626022843959028633)
      ·
        refine ⟨30754164469517132969271475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41005552626022843959028633 30754164469517132969271475)
        ·
          refine ⟨46131246704275699453907213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30754164469517132969271475 46131246704275699453907213)
          ·
            refine ⟨17299217514103387295215205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46131246704275699453907213 17299217514103387295215205)
            ·
              refine ⟨3243603283894385117852851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17299217514103387295215205 3243603283894385117852851)
              ·
                refine ⟨4865404925841577676779277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243603283894385117852851 4865404925841577676779277)
                ·
                  refine ⟨1824526847190591628792229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4865404925841577676779277 1824526847190591628792229)
                  ·
                    refine ⟨342098783848235930398543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1824526847190591628792229 342098783848235930398543)
                    ·
                      rfl

theorem cell23_1998705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_1998705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998705 prefixEnd_1998705 := by exact prefixLift 1998705
  have htrace : WordTrace (prefixWord ++ tailWord_1998705) baseStart_1998705 baseEnd_1998705 := by
    simpa [prefixWord, tailWord_1998705, baseEnd_1998705] using wordTrace_append hprefix tailTrace_1998705
  have hstable : (prefixWord ++ tailWord_1998705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998705).length < 2 ^ (prefixWord ++ tailWord_1998705).sum := by decide
  have hdescent : baseEnd_1998705 < baseStart_1998705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998745 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 5, 1, 3]
def baseStart_1998745 : Nat := 118140960795 + 1998745 * 2 ^ 59
def prefixEnd_1998745 : Nat := 4983230072969 + 3 ^ 40 * 1998745 * 2
def baseEnd_1998745 : Nat := 1026316890770887634695445

theorem tailTrace_1998745 : CollatzResearch.WordTrace tailWord_1998745 prefixEnd_1998745 1026316890770887634695445 := by
  unfold tailWord_1998745
  simp only [CollatzResearch.WordTrace]
  refine ⟨72900219143895698314173689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48600146095930465542782459 72900219143895698314173689)
  ·
    refine ⟨54675164357921773735630267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72900219143895698314173689 54675164357921773735630267)
    ·
      refine ⟨82012746536882660603445401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54675164357921773735630267 82012746536882660603445401)
      ·
        refine ⟨61509559902661995452584051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82012746536882660603445401 61509559902661995452584051)
        ·
          refine ⟨92264339853992993178876077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61509559902661995452584051 92264339853992993178876077)
          ·
            refine ⟨34599127445247372442078529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92264339853992993178876077 34599127445247372442078529)
            ·
              refine ⟨25949345583935529331558897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34599127445247372442078529 25949345583935529331558897)
              ·
                refine ⟨19462009187951646998669173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25949345583935529331558897 19462009187951646998669173)
                ·
                  refine ⟨1824563361370466906125235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19462009187951646998669173 1824563361370466906125235)
                  ·
                    refine ⟨2736845042055700359187853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1824563361370466906125235 2736845042055700359187853)
                    ·
                      refine ⟨1026316890770887634695445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2736845042055700359187853 1026316890770887634695445)
                      ·
                        rfl

theorem cell23_1998745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_1998745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998745 prefixEnd_1998745 := by exact prefixLift 1998745
  have htrace : WordTrace (prefixWord ++ tailWord_1998745) baseStart_1998745 baseEnd_1998745 := by
    simpa [prefixWord, tailWord_1998745, baseEnd_1998745] using wordTrace_append hprefix tailTrace_1998745
  have hstable : (prefixWord ++ tailWord_1998745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998745).length < 2 ^ (prefixWord ++ tailWord_1998745).sum := by decide
  have hdescent : baseEnd_1998745 < baseStart_1998745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998782 : List Nat := [4, 2, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_1998782 : Nat := 118140960795 + 1998782 * 2 ^ 59
def prefixEnd_1998782 : Nat := 4983230072969 + 3 ^ 40 * 1998782 * 2
def baseEnd_1998782 : Nat := 342111963185034663310925

theorem tailTrace_1998782 : CollatzResearch.WordTrace tailWord_1998782 prefixEnd_1998782 342111963185034663310925 := by
  unfold tailWord_1998782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9112696080595206704158825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48601045763174435755513733 9112696080595206704158825)
  ·
    refine ⟨6834522060446405028119119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9112696080595206704158825 6834522060446405028119119)
    ·
      refine ⟨10251783090669607542178679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6834522060446405028119119 10251783090669607542178679)
      ·
        refine ⟨15377674636004411313268019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10251783090669607542178679 15377674636004411313268019)
        ·
          refine ⟨23066511954006616969902029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15377674636004411313268019 23066511954006616969902029)
          ·
            refine ⟨8649941982752481363713261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23066511954006616969902029 8649941982752481363713261)
            ·
              refine ⟨3243728243532180511392473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8649941982752481363713261 3243728243532180511392473)
              ·
                refine ⟨2432796182649135383544355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3243728243532180511392473 2432796182649135383544355)
                ·
                  refine ⟨3649194273973703075316533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2432796182649135383544355 3649194273973703075316533)
                  ·
                    refine ⟨342111963185034663310925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3649194273973703075316533 342111963185034663310925)
                    ·
                      rfl

theorem cell23_1998782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_1998782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998782 prefixEnd_1998782 := by exact prefixLift 1998782
  have htrace : WordTrace (prefixWord ++ tailWord_1998782) baseStart_1998782 baseEnd_1998782 := by
    simpa [prefixWord, tailWord_1998782, baseEnd_1998782] using wordTrace_append hprefix tailTrace_1998782
  have hstable : (prefixWord ++ tailWord_1998782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998782).length < 2 ^ (prefixWord ++ tailWord_1998782).sum := by decide
  have hdescent : baseEnd_1998782 < baseStart_1998782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998828 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_1998828 : Nat := 118140960795 + 1998828 * 2 ^ 59
def prefixEnd_1998828 : Nat := 4983230072969 + 3 ^ 40 * 1998828 * 2
def baseEnd_1998828 : Nat := 1026359509665210809957563

theorem tailTrace_1998828 : CollatzResearch.WordTrace tailWord_1998828 prefixEnd_1998828 1026359509665210809957563 := by
  unfold tailWord_1998828
  simp only [CollatzResearch.WordTrace]
  refine ⟨36451623201297501744722569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48602164268396668992963425 36451623201297501744722569)
  ·
    refine ⟨27338717400973126308541927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36451623201297501744722569 27338717400973126308541927)
    ·
      refine ⟨41008076101459689462812891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27338717400973126308541927 41008076101459689462812891)
      ·
        refine ⟨61512114152189534194219337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41008076101459689462812891 61512114152189534194219337)
        ·
          refine ⟨46134085614142150645664503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61512114152189534194219337 46134085614142150645664503)
          ·
            refine ⟨69201128421213225968496755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46134085614142150645664503 69201128421213225968496755)
            ·
              refine ⟨103801692631819838952745133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69201128421213225968496755 103801692631819838952745133)
              ·
                refine ⟨38925634736932439607279425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103801692631819838952745133 38925634736932439607279425)
                ·
                  refine ⟨29194226052699329705459569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38925634736932439607279425 29194226052699329705459569)
                  ·
                    refine ⟨21895669539524497279094677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29194226052699329705459569 21895669539524497279094677)
                    ·
                      refine ⟨1026359509665210809957563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21895669539524497279094677 1026359509665210809957563)
                      ·
                        rfl

theorem cell23_1998828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_1998828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998828 prefixEnd_1998828 := by exact prefixLift 1998828
  have htrace : WordTrace (prefixWord ++ tailWord_1998828) baseStart_1998828 baseEnd_1998828 := by
    simpa [prefixWord, tailWord_1998828, baseEnd_1998828] using wordTrace_append hprefix tailTrace_1998828
  have hstable : (prefixWord ++ tailWord_1998828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998828).length < 2 ^ (prefixWord ++ tailWord_1998828).sum := by decide
  have hdescent : baseEnd_1998828 < baseStart_1998828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998829 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_1998829 : Nat := 118140960795 + 1998829 * 2 ^ 59
def prefixEnd_1998829 : Nat := 4983230072969 + 3 ^ 40 * 1998829 * 2
def baseEnd_1998829 : Nat := 342120007715288435348353

theorem tailTrace_1998829 : CollatzResearch.WordTrace tailWord_1998829 prefixEnd_1998829 342120007715288435348353 := by
  unfold tailWord_1998829
  simp only [CollatzResearch.WordTrace]
  refine ⟨72903282875591380660231541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48602188583727587106821027 72903282875591380660231541)
  ·
    refine ⟨6834682769586691936896707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72903282875591380660231541 6834682769586691936896707)
    ·
      refine ⟨10252024154380037905345061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6834682769586691936896707 10252024154380037905345061)
      ·
        refine ⟨1922254528946257107252199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10252024154380037905345061 1922254528946257107252199)
        ·
          refine ⟨2883381793419385660878299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922254528946257107252199 2883381793419385660878299)
          ·
            refine ⟨4325072690129078491317449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883381793419385660878299 4325072690129078491317449)
            ·
              refine ⟨3243804517596808868488087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4325072690129078491317449 3243804517596808868488087)
              ·
                refine ⟨4865706776395213302732131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243804517596808868488087 4865706776395213302732131)
                ·
                  refine ⟨7298560164592819954098197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865706776395213302732131 7298560164592819954098197)
                  ·
                    refine ⟨342120007715288435348353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7298560164592819954098197 342120007715288435348353)
                    ·
                      rfl

theorem cell23_1998829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_1998829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998829 prefixEnd_1998829 := by exact prefixLift 1998829
  have htrace : WordTrace (prefixWord ++ tailWord_1998829) baseStart_1998829 baseEnd_1998829 := by
    simpa [prefixWord, tailWord_1998829, baseEnd_1998829] using wordTrace_append hprefix tailTrace_1998829
  have hstable : (prefixWord ++ tailWord_1998829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998829).length < 2 ^ (prefixWord ++ tailWord_1998829).sum := by decide
  have hdescent : baseEnd_1998829 < baseStart_1998829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998869 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 4, 1, 3]
def baseStart_1998869 : Nat := 118140960795 + 1998869 * 2 ^ 59
def prefixEnd_1998869 : Nat := 4983230072969 + 3 ^ 40 * 1998869 * 2
def baseEnd_1998869 : Nat := 1026380562372045149544875

theorem tailTrace_1998869 : CollatzResearch.WordTrace tailWord_1998869 prefixEnd_1998869 1026380562372045149544875 := by
  unfold tailWord_1998869
  simp only [CollatzResearch.WordTrace]
  refine ⟨72904741795446467491687661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48603161196964311661125107 72904741795446467491687661)
  ·
    refine ⟨27339278173292425309382873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72904741795446467491687661 27339278173292425309382873)
    ·
      refine ⟨20504458629969318982037155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27339278173292425309382873 20504458629969318982037155)
      ·
        refine ⟨30756687944953978473055733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20504458629969318982037155 30756687944953978473055733)
        ·
          refine ⟨2883439494839435481848975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30756687944953978473055733 2883439494839435481848975)
          ·
            refine ⟨4325159242259153222773463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883439494839435481848975 4325159242259153222773463)
            ·
              refine ⟨6487738863388729834160195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4325159242259153222773463 6487738863388729834160195)
              ·
                refine ⟨9731608295083094751240293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6487738863388729834160195 9731608295083094751240293)
                ·
                  refine ⟨1824676555328080265857555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9731608295083094751240293 1824676555328080265857555)
                  ·
                    refine ⟨2737014832992120398786333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1824676555328080265857555 2737014832992120398786333)
                    ·
                      refine ⟨1026380562372045149544875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2737014832992120398786333 1026380562372045149544875)
                      ·
                        rfl

theorem cell23_1998869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_1998869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998869 prefixEnd_1998869 := by exact prefixLift 1998869
  have htrace : WordTrace (prefixWord ++ tailWord_1998869) baseStart_1998869 baseEnd_1998869 := by
    simpa [prefixWord, tailWord_1998869, baseEnd_1998869] using wordTrace_append hprefix tailTrace_1998869
  have hstable : (prefixWord ++ tailWord_1998869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998869).length < 2 ^ (prefixWord ++ tailWord_1998869).sum := by decide
  have hdescent : baseEnd_1998869 < baseStart_1998869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998885 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 2, 6]
def baseStart_1998885 : Nat := 118140960795 + 1998885 * 2 ^ 59
def prefixEnd_1998885 : Nat := 4983230072969 + 3 ^ 40 * 1998885 * 2
def baseEnd_1998885 : Nat := 342129592687505695648267

theorem tailTrace_1998885 : CollatzResearch.WordTrace tailWord_1998885 prefixEnd_1998885 342129592687505695648267 := by
  unfold tailWord_1998885
  simp only [CollatzResearch.WordTrace]
  refine ⟨72905325363388502224270109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48603550242259001482846739 72905325363388502224270109)
  ·
    refine ⟨27339497011270688334101291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72905325363388502224270109 27339497011270688334101291)
    ·
      refine ⟨41009245516906032501151937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27339497011270688334101291 41009245516906032501151937)
      ·
        refine ⟨30756934137679524375863953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41009245516906032501151937 30756934137679524375863953)
        ·
          refine ⟨23067700603259643281897965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30756934137679524375863953 23067700603259643281897965)
          ·
            refine ⟨8650387726222366230711737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23067700603259643281897965 8650387726222366230711737)
            ·
              refine ⟨6487790794666774673033803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8650387726222366230711737 6487790794666774673033803)
              ·
                refine ⟨9731686192000162009550705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6487790794666774673033803 9731686192000162009550705)
                ·
                  refine ⟨7298764644000121507163029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9731686192000162009550705 7298764644000121507163029)
                  ·
                    refine ⟨342129592687505695648267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7298764644000121507163029 342129592687505695648267)
                    ·
                      rfl

theorem cell23_1998885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_1998885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998885 prefixEnd_1998885 := by exact prefixLift 1998885
  have htrace : WordTrace (prefixWord ++ tailWord_1998885) baseStart_1998885 baseEnd_1998885 := by
    simpa [prefixWord, tailWord_1998885, baseEnd_1998885] using wordTrace_append hprefix tailTrace_1998885
  have hstable : (prefixWord ++ tailWord_1998885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998885).length < 2 ^ (prefixWord ++ tailWord_1998885).sum := by decide
  have hdescent : baseEnd_1998885 < baseStart_1998885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998892 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 1, 4, 2]
def baseStart_1998892 : Nat := 118140960795 + 1998892 * 2 ^ 59
def prefixEnd_1998892 : Nat := 4983230072969 + 3 ^ 40 * 1998892 * 2
def baseEnd_1998892 : Nat := 1026392372427098559557269

theorem tailTrace_1998892 : CollatzResearch.WordTrace tailWord_1998892 prefixEnd_1998892 1026392372427098559557269 := by
  unfold tailWord_1998892
  simp only [CollatzResearch.WordTrace]
  refine ⟨36452790337181571209887465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48603720449575428279849953 36452790337181571209887465)
  ·
    refine ⟨27339592752886178407415599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36452790337181571209887465 27339592752886178407415599)
    ·
      refine ⟨41009389129329267611123399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27339592752886178407415599 41009389129329267611123399)
      ·
        refine ⟨61514083693993901416685099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41009389129329267611123399 61514083693993901416685099)
        ·
          refine ⟨92271125540990852125027649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61514083693993901416685099 92271125540990852125027649)
          ·
            refine ⟨69203344155743139093770737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92271125540990852125027649 69203344155743139093770737)
            ·
              refine ⟨51902508116807354320328053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69203344155743139093770737 51902508116807354320328053)
              ·
                refine ⟨4865860135950689467530755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51902508116807354320328053 4865860135950689467530755)
                ·
                  refine ⟨7298790203926034201296133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865860135950689467530755 7298790203926034201296133)
                  ·
                    refine ⟨1368523163236131412743025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7298790203926034201296133 1368523163236131412743025)
                    ·
                      refine ⟨1026392372427098559557269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1368523163236131412743025 1026392372427098559557269)
                      ·
                        rfl

theorem cell23_1998892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 4, 2].length) (baseStart_1998892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998892 prefixEnd_1998892 := by exact prefixLift 1998892
  have htrace : WordTrace (prefixWord ++ tailWord_1998892) baseStart_1998892 baseEnd_1998892 := by
    simpa [prefixWord, tailWord_1998892, baseEnd_1998892] using wordTrace_append hprefix tailTrace_1998892
  have hstable : (prefixWord ++ tailWord_1998892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998892).length < 2 ^ (prefixWord ++ tailWord_1998892).sum := by decide
  have hdescent : baseEnd_1998892 < baseStart_1998892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998909 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 6, 2, 2]
def baseStart_1998909 : Nat := 118140960795 + 1998909 * 2 ^ 59
def prefixEnd_1998909 : Nat := 4983230072969 + 3 ^ 40 * 1998909 * 2
def baseEnd_1998909 : Nat := 1026401101598224993044691

theorem tailTrace_1998909 : CollatzResearch.WordTrace tailWord_1998909 prefixEnd_1998909 1026401101598224993044691 := by
  unfold tailWord_1998909
  simp only [CollatzResearch.WordTrace]
  refine ⟨72906200715301554323143781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48604133810201036215429187 72906200715301554323143781)
  ·
    refine ⟨13669912634119041435589459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72906200715301554323143781 13669912634119041435589459)
    ·
      refine ⟨20504868951178562153384189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13669912634119041435589459 20504868951178562153384189)
      ·
        refine ⟨7689325856691960807519071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20504868951178562153384189 7689325856691960807519071)
        ·
          refine ⟨11533988785037941211278607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7689325856691960807519071 11533988785037941211278607)
          ·
            refine ⟨17300983177556911816917911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11533988785037941211278607 17300983177556911816917911)
            ·
              refine ⟨25951474766335367725376867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17300983177556911816917911 25951474766335367725376867)
              ·
                refine ⟨38927212149503051588065301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25951474766335367725376867 38927212149503051588065301)
                ·
                  refine ⟨1824713069507955543190561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38927212149503051588065301 1824713069507955543190561)
                  ·
                    refine ⟨1368534802130966657392921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1824713069507955543190561 1368534802130966657392921)
                    ·
                      refine ⟨1026401101598224993044691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1368534802130966657392921 1026401101598224993044691)
                      ·
                        rfl

theorem cell23_1998909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_1998909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998909 prefixEnd_1998909 := by exact prefixLift 1998909
  have htrace : WordTrace (prefixWord ++ tailWord_1998909) baseStart_1998909 baseEnd_1998909 := by
    simpa [prefixWord, tailWord_1998909, baseEnd_1998909] using wordTrace_append hprefix tailTrace_1998909
  have hstable : (prefixWord ++ tailWord_1998909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998909).length < 2 ^ (prefixWord ++ tailWord_1998909).sum := by decide
  have hdescent : baseEnd_1998909 < baseStart_1998909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998945 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 6, 5]
def baseStart_1998945 : Nat := 118140960795 + 1998945 * 2 ^ 59
def prefixEnd_1998945 : Nat := 4983230072969 + 3 ^ 40 * 1998945 * 2
def baseEnd_1998945 : Nat := 342139862300595617398175

theorem tailTrace_1998945 : CollatzResearch.WordTrace tailWord_1998945 prefixEnd_1998945 342139862300595617398175 := by
  unfold tailWord_1998945
  simp only [CollatzResearch.WordTrace]
  refine ⟨72907513743171132471454289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48605009162114088314302859 72907513743171132471454289)
  ·
    refine ⟨54680635307378349353590717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72907513743171132471454289 54680635307378349353590717)
    ·
      refine ⟨20505238240266881007596519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54680635307378349353590717 20505238240266881007596519)
      ·
        refine ⟨30757857360400321511394779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20505238240266881007596519 30757857360400321511394779)
        ·
          refine ⟨46136786040600482267092169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30757857360400321511394779 46136786040600482267092169)
          ·
            refine ⟨34602589530450361700319127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46136786040600482267092169 34602589530450361700319127)
            ·
              refine ⟨51903884295675542550478691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34602589530450361700319127 51903884295675542550478691)
              ·
                refine ⟨77855826443513313825718037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51903884295675542550478691 77855826443513313825718037)
                ·
                  refine ⟨3649491864539686585580533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77855826443513313825718037 3649491864539686585580533)
                  ·
                    refine ⟨342139862300595617398175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3649491864539686585580533 342139862300595617398175)
                    ·
                      rfl

theorem cell23_1998945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_1998945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998945 prefixEnd_1998945 := by exact prefixLift 1998945
  have htrace : WordTrace (prefixWord ++ tailWord_1998945) baseStart_1998945 baseEnd_1998945 := by
    simpa [prefixWord, tailWord_1998945, baseEnd_1998945] using wordTrace_append hprefix tailTrace_1998945
  have hstable : (prefixWord ++ tailWord_1998945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998945).length < 2 ^ (prefixWord ++ tailWord_1998945).sum := by decide
  have hdescent : baseEnd_1998945 < baseStart_1998945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998962 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_1998962 : Nat := 118140960795 + 1998962 * 2 ^ 59
def prefixEnd_1998962 : Nat := 4983230072969 + 3 ^ 40 * 1998962 * 2
def baseEnd_1998962 : Nat := 342142772024304428560649

theorem tailTrace_1998962 : CollatzResearch.WordTrace tailWord_1998962 prefixEnd_1998962 342142772024304428560649 := by
  unfold tailWord_1998962
  simp only [CollatzResearch.WordTrace]
  refine ⟨18227033446027386093705785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48605422522739696249882093 18227033446027386093705785)
  ·
    refine ⟨13670275084520539570279339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18227033446027386093705785 13670275084520539570279339)
    ·
      refine ⟨20505412626780809355419009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13670275084520539570279339 20505412626780809355419009)
      ·
        refine ⟨15379059470085607016564257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20505412626780809355419009 15379059470085607016564257)
        ·
          refine ⟨11534294602564205262423193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15379059470085607016564257 11534294602564205262423193)
          ·
            refine ⟨8650720951923153946817395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11534294602564205262423193 8650720951923153946817395)
            ·
              refine ⟨12976081427884730920226093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8650720951923153946817395 12976081427884730920226093)
              ·
                refine ⟨4866030535456774095084785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12976081427884730920226093 4866030535456774095084785)
                ·
                  refine ⟨3649522901592580571313589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4866030535456774095084785 3649522901592580571313589)
                  ·
                    refine ⟨342142772024304428560649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3649522901592580571313589 342142772024304428560649)
                    ·
                      rfl

theorem cell23_1998962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_1998962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998962 prefixEnd_1998962 := by exact prefixLift 1998962
  have htrace : WordTrace (prefixWord ++ tailWord_1998962) baseStart_1998962 baseEnd_1998962 := by
    simpa [prefixWord, tailWord_1998962, baseEnd_1998962] using wordTrace_append hprefix tailTrace_1998962
  have hstable : (prefixWord ++ tailWord_1998962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998962).length < 2 ^ (prefixWord ++ tailWord_1998962).sum := by decide
  have hdescent : baseEnd_1998962 < baseStart_1998962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998985 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 2, 3, 5]
def baseStart_1998985 : Nat := 118140960795 + 1998985 * 2 ^ 59
def prefixEnd_1998985 : Nat := 4983230072969 + 3 ^ 40 * 1998985 * 2
def baseEnd_1998985 : Nat := 1026440126127966695694341

theorem tailTrace_1998985 : CollatzResearch.WordTrace tailWord_1998985 prefixEnd_1998985 1026440126127966695694341 := by
  unfold tailWord_1998985
  simp only [CollatzResearch.WordTrace]
  refine ⟨72908972663026219302910409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48605981775350812868606939 72908972663026219302910409)
  ·
    refine ⟨54681729497269664477182807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72908972663026219302910409 54681729497269664477182807)
    ·
      refine ⟨82022594245904496715774211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54681729497269664477182807 82022594245904496715774211)
      ·
        refine ⟨123033891368856745073661317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82022594245904496715774211 123033891368856745073661317)
        ·
          refine ⟨23068854631660639701311497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123033891368856745073661317 23068854631660639701311497)
          ·
            refine ⟨17301640973745479775983623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23068854631660639701311497 17301640973745479775983623)
            ·
              refine ⟨25952461460618219663975435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17301640973745479775983623 25952461460618219663975435)
              ·
                refine ⟨38928692190927329495963153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25952461460618219663975435 38928692190927329495963153)
                ·
                  refine ⟨29196519143195497121972365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38928692190927329495963153 29196519143195497121972365)
                  ·
                    refine ⟨10948694678698311420739637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29196519143195497121972365 10948694678698311420739637)
                    ·
                      refine ⟨1026440126127966695694341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10948694678698311420739637 1026440126127966695694341)
                      ·
                        rfl

theorem cell23_1998985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_1998985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998985 prefixEnd_1998985 := by exact prefixLift 1998985
  have htrace : WordTrace (prefixWord ++ tailWord_1998985) baseStart_1998985 baseEnd_1998985 := by
    simpa [prefixWord, tailWord_1998985, baseEnd_1998985] using wordTrace_append hprefix tailTrace_1998985
  have hstable : (prefixWord ++ tailWord_1998985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998985).length < 2 ^ (prefixWord ++ tailWord_1998985).sum := by decide
  have hdescent : baseEnd_1998985 < baseStart_1998985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998992 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 3, 4]
def baseStart_1998992 : Nat := 118140960795 + 1998992 * 2 ^ 59
def prefixEnd_1998992 : Nat := 4983230072969 + 3 ^ 40 * 1998992 * 2
def baseEnd_1998992 : Nat := 342147906830849389435603

theorem tailTrace_1998992 : CollatzResearch.WordTrace tailWord_1998992 prefixEnd_1998992 342147906830849389435603 := by
  unfold tailWord_1998992
  simp only [CollatzResearch.WordTrace]
  refine ⟨36454613987000429749207615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48606151982667239665610153 36454613987000429749207615)
  ·
    refine ⟨54681920980500644623811423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36454613987000429749207615 54681920980500644623811423)
    ·
      refine ⟨82022881470750966935717135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54681920980500644623811423 82022881470750966935717135)
      ·
        refine ⟨123034322206126450403575703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82022881470750966935717135 123034322206126450403575703)
        ·
          refine ⟨184551483309189675605363555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123034322206126450403575703 184551483309189675605363555)
          ·
            refine ⟨276827224963784513408045333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184551483309189675605363555 276827224963784513408045333)
            ·
              refine ⟨12976276170177399066002125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 276827224963784513408045333 12976276170177399066002125)
              ·
                refine ⟨4866103563816524649750797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12976276170177399066002125 4866103563816524649750797)
                ·
                  refine ⟨1824788836431196743656549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4866103563816524649750797 1824788836431196743656549)
                  ·
                    refine ⟨342147906830849389435603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1824788836431196743656549 342147906830849389435603)
                    ·
                      rfl

theorem cell23_1998992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 3, 4].length) (baseStart_1998992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998992 prefixEnd_1998992 := by exact prefixLift 1998992
  have htrace : WordTrace (prefixWord ++ tailWord_1998992) baseStart_1998992 baseEnd_1998992 := by
    simpa [prefixWord, tailWord_1998992, baseEnd_1998992] using wordTrace_append hprefix tailTrace_1998992
  have hstable : (prefixWord ++ tailWord_1998992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998992).length < 2 ^ (prefixWord ++ tailWord_1998992).sum := by decide
  have hdescent : baseEnd_1998992 < baseStart_1998992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998995 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 4]
def baseStart_1998995 : Nat := 118140960795 + 1998995 * 2 ^ 59
def prefixEnd_1998995 : Nat := 4983230072969 + 3 ^ 40 * 1998995 * 2
def baseEnd_1998995 : Nat := 1026445260934511656569295

theorem tailTrace_1998995 : CollatzResearch.WordTrace tailWord_1998995 prefixEnd_1998995 1026445260934511656569295 := by
  unfold tailWord_1998995
  simp only [CollatzResearch.WordTrace]
  refine ⟨72909337392989991010774439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48606224928659994007182959 72909337392989991010774439)
  ·
    refine ⟨109364006089484986516161659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72909337392989991010774439 109364006089484986516161659)
    ·
      refine ⟨164046009134227479774242489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109364006089484986516161659 164046009134227479774242489)
      ·
        refine ⟨123034506850670609830681867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164046009134227479774242489 123034506850670609830681867)
        ·
          refine ⟨184551760276005914746022801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123034506850670609830681867 184551760276005914746022801)
          ·
            refine ⟨138413820207004436059517101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184551760276005914746022801 138413820207004436059517101)
            ·
              refine ⟨51905182577626663522318913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138413820207004436059517101 51905182577626663522318913)
              ·
                refine ⟨38928886933219997641739185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51905182577626663522318913 38928886933219997641739185)
                ·
                  refine ⟨29196665199914998231304389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38928886933219997641739185 29196665199914998231304389)
                  ·
                    refine ⟨5474374724984062168369573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29196665199914998231304389 5474374724984062168369573)
                    ·
                      refine ⟨1026445260934511656569295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5474374724984062168369573 1026445260934511656569295)
                      ·
                        rfl

theorem cell23_1998995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_1998995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1998995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1998995 prefixEnd_1998995 := by exact prefixLift 1998995
  have htrace : WordTrace (prefixWord ++ tailWord_1998995) baseStart_1998995 baseEnd_1998995 := by
    simpa [prefixWord, tailWord_1998995, baseEnd_1998995] using wordTrace_append hprefix tailTrace_1998995
  have hstable : (prefixWord ++ tailWord_1998995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998995).length < 2 ^ (prefixWord ++ tailWord_1998995).sum := by decide
  have hdescent : baseEnd_1998995 < baseStart_1998995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
