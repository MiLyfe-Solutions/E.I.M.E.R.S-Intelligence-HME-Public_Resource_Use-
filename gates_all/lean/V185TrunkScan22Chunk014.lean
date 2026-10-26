import V185TrunkScan22Chunk013

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_122906 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 1, 5]
def baseStart_122906 : Nat := 118140960795 + 122906 * 2 ^ 59
def prefixEnd_122906 : Nat := 4983230072969 + 3 ^ 40 * 122906 * 2
def baseEnd_122906 : Nat := 42073235547734242273181

theorem tailTrace_122906 : CollatzResearch.WordTrace tailWord_122906 prefixEnd_122906 42073235547734242273181 := by
  unfold tailWord_122906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1120687523185006879689143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2988500061826685012504381 1120687523185006879689143)
  ·
    refine ⟨1681031284777510319533715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1120687523185006879689143 1681031284777510319533715)
    ·
      refine ⟨2521546927166265479300573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1681031284777510319533715 2521546927166265479300573)
      ·
        refine ⟨945580097687349554737715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2521546927166265479300573 945580097687349554737715)
        ·
          refine ⟨1418370146531024332106573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945580097687349554737715 1418370146531024332106573)
          ·
            refine ⟨531888804949134124539965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1418370146531024332106573 531888804949134124539965)
            ·
              refine ⟨199458301855925296702487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 531888804949134124539965 199458301855925296702487)
              ·
                refine ⟨299187452783887945053731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199458301855925296702487 299187452783887945053731)
                ·
                  refine ⟨448781179175831917580597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299187452783887945053731 448781179175831917580597)
                  ·
                    refine ⟨42073235547734242273181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 448781179175831917580597 42073235547734242273181)
                    ·
                      rfl

theorem cell22_122906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_122906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122906 prefixEnd_122906 := by exact prefixLift 122906
  have htrace : WordTrace (prefixWord ++ tailWord_122906) baseStart_122906 baseEnd_122906 := by
    simpa [prefixWord, tailWord_122906, baseEnd_122906] using wordTrace_append hprefix tailTrace_122906
  have hstable : (prefixWord ++ tailWord_122906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122906).length < 2 ^ (prefixWord ++ tailWord_122906).sum := by decide
  have hdescent : baseEnd_122906 < baseStart_122906 := by decide
  rcases family_descends (prefixWord ++ tailWord_122906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122936 : List Nat := [2, 1, 2, 1, 6, 2, 8]
def baseStart_122936 : Nat := 118140960795 + 122936 * 2 ^ 59
def prefixEnd_122936 : Nat := 4983230072969 + 3 ^ 40 * 122936 * 2
def baseEnd_122936 : Nat := 1558648339289783852707

theorem tailTrace_122936 : CollatzResearch.WordTrace tailWord_122936 prefixEnd_122936 1558648339289783852707 := by
  unfold tailWord_122936
  simp only [CollatzResearch.WordTrace]
  refine ⟨2241922141315671321174331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2989229521754228428232441 2241922141315671321174331)
  ·
    refine ⟨3362883211973506981761497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2241922141315671321174331 3362883211973506981761497)
    ·
      refine ⟨2522162408980130236321123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3362883211973506981761497 2522162408980130236321123)
      ·
        refine ⟨3783243613470195354481685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522162408980130236321123 3783243613470195354481685)
        ·
          refine ⟨177339544381415407241329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3783243613470195354481685 177339544381415407241329)
          ·
            refine ⟨133004658286061555430997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177339544381415407241329 133004658286061555430997)
            ·
              refine ⟨1558648339289783852707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 133004658286061555430997 1558648339289783852707)
              ·
                rfl

theorem cell22_122936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 8].length) (baseStart_122936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122936 prefixEnd_122936 := by exact prefixLift 122936
  have htrace : WordTrace (prefixWord ++ tailWord_122936) baseStart_122936 baseEnd_122936 := by
    simpa [prefixWord, tailWord_122936, baseEnd_122936] using wordTrace_append hprefix tailTrace_122936
  have hstable : (prefixWord ++ tailWord_122936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122936).length < 2 ^ (prefixWord ++ tailWord_122936).sum := by decide
  have hdescent : baseEnd_122936 < baseStart_122936 := by decide
  rcases family_descends (prefixWord ++ tailWord_122936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122942 : List Nat := [4, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_122942 : Nat := 118140960795 + 122942 * 2 ^ 59
def prefixEnd_122942 : Nat := 4983230072969 + 3 ^ 40 * 122942 * 2
def baseEnd_122942 : Nat := 14028519694480716124357

theorem tailTrace_122942 : CollatzResearch.WordTrace tailWord_122942 prefixEnd_122942 14028519694480716124357 := by
  unfold tailWord_122942
  simp only [CollatzResearch.WordTrace]
  refine ⟨560507890076200708383385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2989375413739737111378053 560507890076200708383385)
  ·
    refine ⟨420380917557150531287539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 560507890076200708383385 420380917557150531287539)
    ·
      refine ⟨630571376335725796931309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420380917557150531287539 630571376335725796931309)
      ·
        refine ⟨236464266125897173849241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 630571376335725796931309 236464266125897173849241)
        ·
          refine ⟨177348199594422880386931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236464266125897173849241 177348199594422880386931)
          ·
            refine ⟨266022299391634320580397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177348199594422880386931 266022299391634320580397)
            ·
              refine ⟨99758362271862870217649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266022299391634320580397 99758362271862870217649)
              ·
                refine ⟨74818771703897152663237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99758362271862870217649 74818771703897152663237)
                ·
                  refine ⟨14028519694480716124357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74818771703897152663237 14028519694480716124357)
                  ·
                    rfl

theorem cell22_122942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_122942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122942 prefixEnd_122942 := by exact prefixLift 122942
  have htrace : WordTrace (prefixWord ++ tailWord_122942) baseStart_122942 baseEnd_122942 := by
    simpa [prefixWord, tailWord_122942, baseEnd_122942] using wordTrace_append hprefix tailTrace_122942
  have hstable : (prefixWord ++ tailWord_122942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122942).length < 2 ^ (prefixWord ++ tailWord_122942).sum := by decide
  have hdescent : baseEnd_122942 < baseStart_122942 := by decide
  rcases family_descends (prefixWord ++ tailWord_122942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122949 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_122949 : Nat := 118140960795 + 122949 * 2 ^ 59
def prefixEnd_122949 : Nat := 4983230072969 + 3 ^ 40 * 122949 * 2
def baseEnd_122949 : Nat := 42087955326496463448049

theorem tailTrace_122949 : CollatzResearch.WordTrace tailWord_122949 prefixEnd_122949 42087955326496463448049 := by
  unfold tailWord_122949
  simp only [CollatzResearch.WordTrace]
  refine ⟨4484318431584245862571901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2989545621056163908381267 4484318431584245862571901)
  ·
    refine ⟨1681619411844092198464463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4484318431584245862571901 1681619411844092198464463)
    ·
      refine ⟨2522429117766138297696695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1681619411844092198464463 2522429117766138297696695)
      ·
        refine ⟨3783643676649207446545043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522429117766138297696695 3783643676649207446545043)
        ·
          refine ⟨5675465514973811169817565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783643676649207446545043 5675465514973811169817565)
          ·
            refine ⟨2128299568115179188681587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5675465514973811169817565 2128299568115179188681587)
            ·
              refine ⟨3192449352172768783022381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128299568115179188681587 3192449352172768783022381)
              ·
                refine ⟨1197168507064788293633393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3192449352172768783022381 1197168507064788293633393)
                ·
                  refine ⟨897876380298591220225045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1197168507064788293633393 897876380298591220225045)
                  ·
                    refine ⟨42087955326496463448049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 897876380298591220225045 42087955326496463448049)
                    ·
                      rfl

theorem cell22_122949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_122949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122949 prefixEnd_122949 := by exact prefixLift 122949
  have htrace : WordTrace (prefixWord ++ tailWord_122949) baseStart_122949 baseEnd_122949 := by
    simpa [prefixWord, tailWord_122949, baseEnd_122949] using wordTrace_append hprefix tailTrace_122949
  have hstable : (prefixWord ++ tailWord_122949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122949).length < 2 ^ (prefixWord ++ tailWord_122949).sum := by decide
  have hdescent : baseEnd_122949 < baseStart_122949 := by decide
  rcases family_descends (prefixWord ++ tailWord_122949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122998 : List Nat := [5, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_122998 : Nat := 118140960795 + 122998 * 2 ^ 59
def prefixEnd_122998 : Nat := 4983230072969 + 3 ^ 40 * 122998 * 2
def baseEnd_122998 : Nat := 14034909675958889657633

theorem tailTrace_122998 : CollatzResearch.WordTrace tailWord_122998 prefixEnd_122998 14034909675958889657633 := by
  unfold tailWord_122998
  simp only [CollatzResearch.WordTrace]
  refine ⟨280381600525420451944103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2990737072271151487403765 280381600525420451944103)
  ·
    refine ⟨420572400788130677916155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280381600525420451944103 420572400788130677916155)
    ·
      refine ⟨630858601182196016874233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420572400788130677916155 630858601182196016874233)
      ·
        refine ⟨473143950886647012655675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630858601182196016874233 473143950886647012655675)
        ·
          refine ⟨709715926329970518983513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473143950886647012655675 709715926329970518983513)
          ·
            refine ⟨532286944747477889237635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 709715926329970518983513 532286944747477889237635)
            ·
              refine ⟨798430417121216833856453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532286944747477889237635 798430417121216833856453)
              ·
                refine ⟨149705703210228156348085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 798430417121216833856453 149705703210228156348085)
                ·
                  refine ⟨14034909675958889657633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149705703210228156348085 14034909675958889657633)
                  ·
                    rfl

theorem cell22_122998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_122998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_122998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_122998 prefixEnd_122998 := by exact prefixLift 122998
  have htrace : WordTrace (prefixWord ++ tailWord_122998) baseStart_122998 baseEnd_122998 := by
    simpa [prefixWord, tailWord_122998, baseEnd_122998] using wordTrace_append hprefix tailTrace_122998
  have hstable : (prefixWord ++ tailWord_122998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122998).length < 2 ^ (prefixWord ++ tailWord_122998).sum := by decide
  have hdescent : baseEnd_122998 < baseStart_122998 := by decide
  rcases family_descends (prefixWord ++ tailWord_122998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123011 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 3, 4]
def baseStart_123011 : Nat := 118140960795 + 123011 * 2 ^ 59
def prefixEnd_123011 : Nat := 4983230072969 + 3 ^ 40 * 123011 * 2
def baseEnd_123011 : Nat := 42109179193548968397859

theorem tailTrace_123011 : CollatzResearch.WordTrace tailWord_123011 prefixEnd_123011 42109179193548968397859 := by
  unfold tailWord_123011
  simp only [CollatzResearch.WordTrace]
  refine ⟨4486579757359630451328887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2991053171573086967552591 4486579757359630451328887)
  ·
    refine ⟨6729869636039445676993331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4486579757359630451328887 6729869636039445676993331)
    ·
      refine ⟨10094804454059168515489997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6729869636039445676993331 10094804454059168515489997)
      ·
        refine ⟨3785551670272188193308749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10094804454059168515489997 3785551670272188193308749)
        ·
          refine ⟨1419581876352070572490781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3785551670272188193308749 1419581876352070572490781)
          ·
            refine ⟨532343203632026464684043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1419581876352070572490781 532343203632026464684043)
            ·
              refine ⟨798514805448039697026065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532343203632026464684043 798514805448039697026065)
              ·
                refine ⟨598886104086029772769549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798514805448039697026065 598886104086029772769549)
                ·
                  refine ⟨224582289032261164788581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598886104086029772769549 224582289032261164788581)
                  ·
                    refine ⟨42109179193548968397859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 224582289032261164788581 42109179193548968397859)
                    ·
                      rfl

theorem cell22_123011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 4].length) (baseStart_123011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123011 prefixEnd_123011 := by exact prefixLift 123011
  have htrace : WordTrace (prefixWord ++ tailWord_123011) baseStart_123011 baseEnd_123011 := by
    simpa [prefixWord, tailWord_123011, baseEnd_123011] using wordTrace_append hprefix tailTrace_123011
  have hstable : (prefixWord ++ tailWord_123011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123011).length < 2 ^ (prefixWord ++ tailWord_123011).sum := by decide
  have hdescent : baseEnd_123011 < baseStart_123011 := by decide
  rcases family_descends (prefixWord ++ tailWord_123011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123058 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_123058 : Nat := 118140960795 + 123058 * 2 ^ 59
def prefixEnd_123058 : Nat := 4983230072969 + 3 ^ 40 * 123058 * 2
def baseEnd_123058 : Nat := 42125268254056512472715

theorem tailTrace_123058 : CollatzResearch.WordTrace tailWord_123058 prefixEnd_123058 42125268254056512472715 := by
  unfold tailWord_123058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1122073497047339369572457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2992195992126238318859885 1122073497047339369572457)
  ·
    refine ⟨841555122785504527179343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1122073497047339369572457 841555122785504527179343)
    ·
      refine ⟨1262332684178256790769015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 841555122785504527179343 1262332684178256790769015)
      ·
        refine ⟨1893499026267385186153523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1262332684178256790769015 1893499026267385186153523)
        ·
          refine ⟨2840248539401077779230285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1893499026267385186153523 2840248539401077779230285)
          ·
            refine ⟨1065093202275404167211357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2840248539401077779230285 1065093202275404167211357)
            ·
              refine ⟨399409950853276562704259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1065093202275404167211357 399409950853276562704259)
              ·
                refine ⟨599114926279914844056389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399409950853276562704259 599114926279914844056389)
                ·
                  refine ⟨112334048677484033260573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 599114926279914844056389 112334048677484033260573)
                  ·
                    refine ⟨42125268254056512472715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112334048677484033260573 42125268254056512472715)
                    ·
                      rfl

theorem cell22_123058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_123058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123058 prefixEnd_123058 := by exact prefixLift 123058
  have htrace : WordTrace (prefixWord ++ tailWord_123058) baseStart_123058 baseEnd_123058 := by
    simpa [prefixWord, tailWord_123058, baseEnd_123058] using wordTrace_append hprefix tailTrace_123058
  have hstable : (prefixWord ++ tailWord_123058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123058).length < 2 ^ (prefixWord ++ tailWord_123058).sum := by decide
  have hdescent : baseEnd_123058 < baseStart_123058 := by decide
  rcases family_descends (prefixWord ++ tailWord_123058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123094 : List Nat := [5, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_123094 : Nat := 118140960795 + 123094 * 2 ^ 59
def prefixEnd_123094 : Nat := 4983230072969 + 3 ^ 40 * 123094 * 2
def baseEnd_123094 : Nat := 14045863929921472857535

theorem tailTrace_123094 : CollatzResearch.WordTrace tailWord_123094 prefixEnd_123094 14045863929921472857535 := by
  unfold tailWord_123094
  simp only [CollatzResearch.WordTrace]
  refine ⟨280600438503683476662521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2993071344039290417733557 280600438503683476662521)
  ·
    refine ⟨210450328877762607496891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280600438503683476662521 210450328877762607496891)
    ·
      refine ⟨315675493316643911245337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210450328877762607496891 315675493316643911245337)
      ·
        refine ⟨236756619987482933434003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315675493316643911245337 236756619987482933434003)
        ·
          refine ⟨355134929981224400151005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236756619987482933434003 355134929981224400151005)
          ·
            refine ⟨133175598742959150056627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355134929981224400151005 133175598742959150056627)
            ·
              refine ⟨199763398114438725084941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133175598742959150056627 199763398114438725084941)
              ·
                refine ⟨74911274292914521906853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199763398114438725084941 74911274292914521906853)
                ·
                  refine ⟨14045863929921472857535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74911274292914521906853 14045863929921472857535)
                  ·
                    rfl

theorem cell22_123094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_123094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123094 prefixEnd_123094 := by exact prefixLift 123094
  have htrace : WordTrace (prefixWord ++ tailWord_123094) baseStart_123094 baseEnd_123094 := by
    simpa [prefixWord, tailWord_123094, baseEnd_123094] using wordTrace_append hprefix tailTrace_123094
  have hstable : (prefixWord ++ tailWord_123094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123094).length < 2 ^ (prefixWord ++ tailWord_123094).sum := by decide
  have hdescent : baseEnd_123094 < baseStart_123094 := by decide
  rcases family_descends (prefixWord ++ tailWord_123094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123116 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 7]
def baseStart_123116 : Nat := 118140960795 + 123116 * 2 ^ 59
def prefixEnd_123116 : Nat := 4983230072969 + 3 ^ 40 * 123116 * 2
def baseEnd_123116 : Nat := 14048374279787898174179

theorem tailTrace_123116 : CollatzResearch.WordTrace tailWord_123116 prefixEnd_123116 14048374279787898174179 := by
  unfold tailWord_123116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2245204710989616691950601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2993606281319488922600801 2245204710989616691950601)
  ·
    refine ⟨1683903533242212518962951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2245204710989616691950601 1683903533242212518962951)
    ·
      refine ⟨2525855299863318778444427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1683903533242212518962951 2525855299863318778444427)
      ·
        refine ⟨3788782949794978167666641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2525855299863318778444427 3788782949794978167666641)
        ·
          refine ⟨2841587212346233625749981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3788782949794978167666641 2841587212346233625749981)
          ·
            refine ⟨1065595204629837609656243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2841587212346233625749981 1065595204629837609656243)
            ·
              refine ⟨1598392806944756414484365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065595204629837609656243 1598392806944756414484365)
              ·
                refine ⟨599397302604283655431637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1598392806944756414484365 599397302604283655431637)
                ·
                  refine ⟨14048374279787898174179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 599397302604283655431637 14048374279787898174179)
                  ·
                    rfl

theorem cell22_123116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_123116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123116 prefixEnd_123116 := by exact prefixLift 123116
  have htrace : WordTrace (prefixWord ++ tailWord_123116) baseStart_123116 baseEnd_123116 := by
    simpa [prefixWord, tailWord_123116, baseEnd_123116] using wordTrace_append hprefix tailTrace_123116
  have hstable : (prefixWord ++ tailWord_123116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123116).length < 2 ^ (prefixWord ++ tailWord_123116).sum := by decide
  have hdescent : baseEnd_123116 < baseStart_123116 := by decide
  rcases family_descends (prefixWord ++ tailWord_123116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123120 : List Nat := [2, 1, 1, 1, 3, 1, 1, 8, 1, 3]
def baseStart_123120 : Nat := 118140960795 + 123120 * 2 ^ 59
def prefixEnd_123120 : Nat := 4983230072969 + 3 ^ 40 * 123120 * 2
def baseEnd_123120 : Nat := 42146492121109017422525

theorem tailTrace_123120 : CollatzResearch.WordTrace tailWord_123120 prefixEnd_123120 42146492121109017422525 := by
  unfold tailWord_123120
  simp only [CollatzResearch.WordTrace]
  refine ⟨2245277656982371033523407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2993703542643161378031209 2245277656982371033523407)
  ·
    refine ⟨3367916485473556550285111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2245277656982371033523407 3367916485473556550285111)
    ·
      refine ⟨5051874728210334825427667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3367916485473556550285111 5051874728210334825427667)
      ·
        refine ⟨7577812092315502238141501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5051874728210334825427667 7577812092315502238141501)
        ·
          refine ⟨2841679534618313339303063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7577812092315502238141501 2841679534618313339303063)
          ·
            refine ⟨4262519301927470008954595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841679534618313339303063 4262519301927470008954595)
            ·
              refine ⟨6393778952891205013431893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4262519301927470008954595 6393778952891205013431893)
              ·
                refine ⟨74927097104193808751155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6393778952891205013431893 74927097104193808751155)
                ·
                  refine ⟨112390645656290713126733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74927097104193808751155 112390645656290713126733)
                  ·
                    refine ⟨42146492121109017422525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112390645656290713126733 42146492121109017422525)
                    ·
                      rfl

theorem cell22_123120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 1, 3].length) (baseStart_123120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123120 prefixEnd_123120 := by exact prefixLift 123120
  have htrace : WordTrace (prefixWord ++ tailWord_123120) baseStart_123120 baseEnd_123120 := by
    simpa [prefixWord, tailWord_123120, baseEnd_123120] using wordTrace_append hprefix tailTrace_123120
  have hstable : (prefixWord ++ tailWord_123120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123120).length < 2 ^ (prefixWord ++ tailWord_123120).sum := by decide
  have hdescent : baseEnd_123120 < baseStart_123120 := by decide
  rcases family_descends (prefixWord ++ tailWord_123120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123163 : List Nat := [1, 1, 1, 1, 1, 1, 6, 5, 1, 4]
def baseStart_123163 : Nat := 118140960795 + 123163 * 2 ^ 59
def prefixEnd_123163 : Nat := 4983230072969 + 3 ^ 40 * 123163 * 2
def baseEnd_123163 : Nat := 42161211899871238597393

theorem tailTrace_123163 : CollatzResearch.WordTrace tailWord_123163 prefixEnd_123163 42161211899871238597393 := by
  unfold tailWord_123163
  simp only [CollatzResearch.WordTrace]
  refine ⟨4492123652808960410862143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2994749101872640273908095 4492123652808960410862143)
  ·
    refine ⟨6738185479213440616293215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4492123652808960410862143 6738185479213440616293215)
    ·
      refine ⟨10107278218820160924439823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6738185479213440616293215 10107278218820160924439823)
      ·
        refine ⟨15160917328230241386659735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10107278218820160924439823 15160917328230241386659735)
        ·
          refine ⟨22741375992345362079989603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15160917328230241386659735 22741375992345362079989603)
          ·
            refine ⟨34112063988518043119984405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22741375992345362079989603 34112063988518043119984405)
            ·
              refine ⟨1599002999461783271249269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34112063988518043119984405 1599002999461783271249269)
              ·
                refine ⟨149906531199542181679619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1599002999461783271249269 149906531199542181679619)
                ·
                  refine ⟨224859796799313272519429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149906531199542181679619 224859796799313272519429)
                  ·
                    refine ⟨42161211899871238597393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 224859796799313272519429 42161211899871238597393)
                    ·
                      rfl

theorem cell22_123163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 4].length) (baseStart_123163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123163 prefixEnd_123163 := by exact prefixLift 123163
  have htrace : WordTrace (prefixWord ++ tailWord_123163) baseStart_123163 baseEnd_123163 := by
    simpa [prefixWord, tailWord_123163, baseEnd_123163] using wordTrace_append hprefix tailTrace_123163
  have hstable : (prefixWord ++ tailWord_123163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123163).length < 2 ^ (prefixWord ++ tailWord_123163).sum := by decide
  have hdescent : baseEnd_123163 < baseStart_123163 := by decide
  rcases family_descends (prefixWord ++ tailWord_123163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123182 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_123182 : Nat := 118140960795 + 123182 * 2 ^ 59
def prefixEnd_123182 : Nat := 4983230072969 + 3 ^ 40 * 123182 * 2
def baseEnd_123182 : Nat := 42167715988161522372335

theorem tailTrace_123182 : CollatzResearch.WordTrace tailWord_123182 prefixEnd_123182 42167715988161522372335 := by
  unfold tailWord_123182
  simp only [CollatzResearch.WordTrace]
  refine ⟨561602079967515831975475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2995211093160084437202533 561602079967515831975475)
  ·
    refine ⟨842403119951273747963213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 561602079967515831975475 842403119951273747963213)
    ·
      refine ⟨315901169981727655486205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 842403119951273747963213 315901169981727655486205)
      ·
        refine ⟨118462938743147870807327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315901169981727655486205 118462938743147870807327)
        ·
          refine ⟨177694408114721806210991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118462938743147870807327 177694408114721806210991)
          ·
            refine ⟨266541612172082709316487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177694408114721806210991 266541612172082709316487)
            ·
              refine ⟨399812418258124063974731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266541612172082709316487 399812418258124063974731)
              ·
                refine ⟨599718627387186095962097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399812418258124063974731 599718627387186095962097)
                ·
                  refine ⟨449788970540389571971573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599718627387186095962097 449788970540389571971573)
                  ·
                    refine ⟨42167715988161522372335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 449788970540389571971573 42167715988161522372335)
                    ·
                      rfl

theorem cell22_123182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_123182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123182 prefixEnd_123182 := by exact prefixLift 123182
  have htrace : WordTrace (prefixWord ++ tailWord_123182) baseStart_123182 baseEnd_123182 := by
    simpa [prefixWord, tailWord_123182, baseEnd_123182] using wordTrace_append hprefix tailTrace_123182
  have hstable : (prefixWord ++ tailWord_123182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123182).length < 2 ^ (prefixWord ++ tailWord_123182).sum := by decide
  have hdescent : baseEnd_123182 < baseStart_123182 := by decide
  rcases family_descends (prefixWord ++ tailWord_123182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123244 : List Nat := [2, 2, 1, 1, 6, 1, 3, 1, 2, 3]
def baseStart_123244 : Nat := 118140960795 + 123244 * 2 ^ 59
def prefixEnd_123244 : Nat := 4983230072969 + 3 ^ 40 * 123244 * 2
def baseEnd_123244 : Nat := 42188939855214027322145

theorem tailTrace_123244 : CollatzResearch.WordTrace tailWord_123244 prefixEnd_123244 42188939855214027322145 := by
  unfold tailWord_123244
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247538982757755622280393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2996718643677007496373857 2247538982757755622280393)
  ·
    refine ⟨1685654237068316716710295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2247538982757755622280393 1685654237068316716710295)
    ·
      refine ⟨2528481355602475075065443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1685654237068316716710295 2528481355602475075065443)
      ·
        refine ⟨3792722033403712612598165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528481355602475075065443 3792722033403712612598165)
        ·
          refine ⟨177783845315799028715539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3792722033403712612598165 177783845315799028715539)
          ·
            refine ⟨266675767973698543073309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177783845315799028715539 266675767973698543073309)
            ·
              refine ⟨100003412990136953652491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266675767973698543073309 100003412990136953652491)
              ·
                refine ⟨150005119485205430478737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100003412990136953652491 150005119485205430478737)
                ·
                  refine ⟨112503839613904072859053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150005119485205430478737 112503839613904072859053)
                  ·
                    refine ⟨42188939855214027322145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112503839613904072859053 42188939855214027322145)
                    ·
                      rfl

theorem cell22_123244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_123244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123244 prefixEnd_123244 := by exact prefixLift 123244
  have htrace : WordTrace (prefixWord ++ tailWord_123244) baseStart_123244 baseEnd_123244 := by
    simpa [prefixWord, tailWord_123244, baseEnd_123244] using wordTrace_append hprefix tailTrace_123244
  have hstable : (prefixWord ++ tailWord_123244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123244).length < 2 ^ (prefixWord ++ tailWord_123244).sum := by decide
  have hdescent : baseEnd_123244 < baseStart_123244 := by decide
  rcases family_descends (prefixWord ++ tailWord_123244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123268 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 9]
def baseStart_123268 : Nat := 118140960795 + 123268 * 2 ^ 59
def prefixEnd_123268 : Nat := 4983230072969 + 3 ^ 40 * 123268 * 2
def baseEnd_123268 : Nat := 14065718515228654907357

theorem tailTrace_123268 : CollatzResearch.WordTrace tailWord_123268 prefixEnd_123268 14065718515228654907357 := by
  unfold tailWord_123268
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247976658714281671717229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2997302211619042228956305 2247976658714281671717229)
  ·
    refine ⟨842991247017855626893961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2247976658714281671717229 842991247017855626893961)
    ·
      refine ⟨632243435263391720170471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 842991247017855626893961 632243435263391720170471)
      ·
        refine ⟨948365152895087580255707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632243435263391720170471 948365152895087580255707)
        ·
          refine ⟨1422547729342631370383561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948365152895087580255707 1422547729342631370383561)
          ·
            refine ⟨1066910797006973527787671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1422547729342631370383561 1066910797006973527787671)
            ·
              refine ⟨1600366195510460291681507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066910797006973527787671 1600366195510460291681507)
              ·
                refine ⟨2400549293265690437522261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600366195510460291681507 2400549293265690437522261)
                ·
                  refine ⟨14065718515228654907357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2400549293265690437522261 14065718515228654907357)
                  ·
                    rfl

theorem cell22_123268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_123268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123268 prefixEnd_123268 := by exact prefixLift 123268
  have htrace : WordTrace (prefixWord ++ tailWord_123268) baseStart_123268 baseEnd_123268 := by
    simpa [prefixWord, tailWord_123268, baseEnd_123268] using wordTrace_append hprefix tailTrace_123268
  have hstable : (prefixWord ++ tailWord_123268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123268).length < 2 ^ (prefixWord ++ tailWord_123268).sum := by decide
  have hdescent : baseEnd_123268 < baseStart_123268 := by decide
  rcases family_descends (prefixWord ++ tailWord_123268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123289 : List Nat := [1, 2, 1, 2, 1, 4, 5, 2, 1, 3]
def baseStart_123289 : Nat := 118140960795 + 123289 * 2 ^ 59
def prefixEnd_123289 : Nat := 4983230072969 + 3 ^ 40 * 123289 * 2
def baseEnd_123289 : Nat := 42204344274848909947007

theorem tailTrace_123289 : CollatzResearch.WordTrace tailWord_123289 prefixEnd_123289 42204344274848909947007 := by
  unfold tailWord_123289
  simp only [CollatzResearch.WordTrace]
  refine ⟨4496719250352483929948921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2997812833568322619965947 4496719250352483929948921)
  ·
    refine ⟨3372539437764362947461691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4496719250352483929948921 3372539437764362947461691)
    ·
      refine ⟨5058809156646544421192537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3372539437764362947461691 5058809156646544421192537)
      ·
        refine ⟨3794106867484908315894403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5058809156646544421192537 3794106867484908315894403)
        ·
          refine ⟨5691160301227362473841605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3794106867484908315894403 5691160301227362473841605)
          ·
            refine ⟨1067092556480130463845301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5691160301227362473841605 1067092556480130463845301)
            ·
              refine ⟨100039927170012230985497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1067092556480130463845301 100039927170012230985497)
              ·
                refine ⟨75029945377509173239123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100039927170012230985497 75029945377509173239123)
                ·
                  refine ⟨112544918066263759858685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75029945377509173239123 112544918066263759858685)
                  ·
                    refine ⟨42204344274848909947007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112544918066263759858685 42204344274848909947007)
                    ·
                      rfl

theorem cell22_123289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 1, 3].length) (baseStart_123289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123289 prefixEnd_123289 := by exact prefixLift 123289
  have htrace : WordTrace (prefixWord ++ tailWord_123289) baseStart_123289 baseEnd_123289 := by
    simpa [prefixWord, tailWord_123289, baseEnd_123289] using wordTrace_append hprefix tailTrace_123289
  have hstable : (prefixWord ++ tailWord_123289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123289).length < 2 ^ (prefixWord ++ tailWord_123289).sum := by decide
  have hdescent : baseEnd_123289 < baseStart_123289 := by decide
  rcases family_descends (prefixWord ++ tailWord_123289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123343 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 3, 6]
def baseStart_123343 : Nat := 118140960795 + 123343 * 2 ^ 59
def prefixEnd_123343 : Nat := 4983230072969 + 3 ^ 40 * 123343 * 2
def baseEnd_123343 : Nat := 42222829578410769096841

theorem tailTrace_123343 : CollatzResearch.WordTrace tailWord_123343 prefixEnd_123343 42222829578410769096841 := by
  unfold tailWord_123343
  simp only [CollatzResearch.WordTrace]
  refine ⟨4498688792156851152414683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2999125861437900768276455 4498688792156851152414683)
  ·
    refine ⟨6748033188235276728622025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4498688792156851152414683 6748033188235276728622025)
    ·
      refine ⟨5061024891176457546466519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6748033188235276728622025 5061024891176457546466519)
      ·
        refine ⟨7591537336764686319699779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5061024891176457546466519 7591537336764686319699779)
        ·
          refine ⟨11387306005147029479549669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7591537336764686319699779 11387306005147029479549669)
          ·
            refine ⟨2135119875965068027415563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11387306005147029479549669 2135119875965068027415563)
            ·
              refine ⟨3202679813947602041123345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135119875965068027415563 3202679813947602041123345)
              ·
                refine ⟨2402009860460701530842509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3202679813947602041123345 2402009860460701530842509)
                ·
                  refine ⟨900753697672763074065941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2402009860460701530842509 900753697672763074065941)
                  ·
                    refine ⟨42222829578410769096841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 900753697672763074065941 42222829578410769096841)
                    ·
                      rfl

theorem cell22_123343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_123343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123343 prefixEnd_123343 := by exact prefixLift 123343
  have htrace : WordTrace (prefixWord ++ tailWord_123343) baseStart_123343 baseEnd_123343 := by
    simpa [prefixWord, tailWord_123343, baseEnd_123343] using wordTrace_append hprefix tailTrace_123343
  have hstable : (prefixWord ++ tailWord_123343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123343).length < 2 ^ (prefixWord ++ tailWord_123343).sum := by decide
  have hdescent : baseEnd_123343 < baseStart_123343 := by decide
  rcases family_descends (prefixWord ++ tailWord_123343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123345 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 4, 3]
def baseStart_123345 : Nat := 118140960795 + 123345 * 2 ^ 59
def prefixEnd_123345 : Nat := 4983230072969 + 3 ^ 40 * 123345 * 2
def baseEnd_123345 : Nat := 42223514219283430546835

theorem tailTrace_123345 : CollatzResearch.WordTrace tailWord_123345 prefixEnd_123345 42223514219283430546835 := by
  unfold tailWord_123345
  simp only [CollatzResearch.WordTrace]
  refine ⟨4498761738149605493987489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2999174492099736995991659 4498761738149605493987489)
  ·
    refine ⟨3374071303612204120490617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4498761738149605493987489 3374071303612204120490617)
    ·
      refine ⟨2530553477709153090367963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3374071303612204120490617 2530553477709153090367963)
      ·
        refine ⟨3795830216563729635551945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2530553477709153090367963 3795830216563729635551945)
        ·
          refine ⟨2846872662422797226663959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3795830216563729635551945 2846872662422797226663959)
          ·
            refine ⟨4270308993634195839995939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846872662422797226663959 4270308993634195839995939)
            ·
              refine ⟨6405463490451293759993909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4270308993634195839995939 6405463490451293759993909)
              ·
                refine ⟨600512202229808789999429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6405463490451293759993909 600512202229808789999429)
                ·
                  refine ⟨112596037918089148124893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600512202229808789999429 112596037918089148124893)
                  ·
                    refine ⟨42223514219283430546835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112596037918089148124893 42223514219283430546835)
                    ·
                      rfl

theorem cell22_123345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_123345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123345 prefixEnd_123345 := by exact prefixLift 123345
  have htrace : WordTrace (prefixWord ++ tailWord_123345) baseStart_123345 baseEnd_123345 := by
    simpa [prefixWord, tailWord_123345, baseEnd_123345] using wordTrace_append hprefix tailTrace_123345
  have hstable : (prefixWord ++ tailWord_123345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123345).length < 2 ^ (prefixWord ++ tailWord_123345).sum := by decide
  have hdescent : baseEnd_123345 < baseStart_123345 := by decide
  rcases family_descends (prefixWord ++ tailWord_123345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123381 : List Nat := [1, 3, 5, 1, 2, 1, 2, 3, 4]
def baseStart_123381 : Nat := 118140960795 + 123381 * 2 ^ 59
def prefixEnd_123381 : Nat := 4983230072969 + 3 ^ 40 * 123381 * 2
def baseEnd_123381 : Nat := 14078612584997112215575

theorem tailTrace_123381 : CollatzResearch.WordTrace tailWord_123381 prefixEnd_123381 14078612584997112215575 := by
  unfold tailWord_123381
  simp only [CollatzResearch.WordTrace]
  refine ⟨4500074766019183642297997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3000049844012789094865331 4500074766019183642297997)
  ·
    refine ⟨1687528037257193865861749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4500074766019183642297997 1687528037257193865861749)
    ·
      refine ⟨158205753492861924924539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1687528037257193865861749 158205753492861924924539)
      ·
        refine ⟨237308630239292887386809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158205753492861924924539 237308630239292887386809)
        ·
          refine ⟨177981472679469665540107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237308630239292887386809 177981472679469665540107)
          ·
            refine ⟨266972209019204498310161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177981472679469665540107 266972209019204498310161)
            ·
              refine ⟨200229156764403373732621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266972209019204498310161 200229156764403373732621)
              ·
                refine ⟨75085933786651265149733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200229156764403373732621 75085933786651265149733)
                ·
                  refine ⟨14078612584997112215575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75085933786651265149733 14078612584997112215575)
                  ·
                    rfl

theorem cell22_123381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_123381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123381 prefixEnd_123381 := by exact prefixLift 123381
  have htrace : WordTrace (prefixWord ++ tailWord_123381) baseStart_123381 baseEnd_123381 := by
    simpa [prefixWord, tailWord_123381, baseEnd_123381] using wordTrace_append hprefix tailTrace_123381
  have hstable : (prefixWord ++ tailWord_123381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123381).length < 2 ^ (prefixWord ++ tailWord_123381).sum := by decide
  have hdescent : baseEnd_123381 < baseStart_123381 := by decide
  rcases family_descends (prefixWord ++ tailWord_123381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123396 : List Nat := [2, 3, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_123396 : Nat := 118140960795 + 123396 * 2 ^ 59
def prefixEnd_123396 : Nat := 4983230072969 + 3 ^ 40 * 123396 * 2
def baseEnd_123396 : Nat := 42240972561536297521679

theorem tailTrace_123396 : CollatzResearch.WordTrace tailWord_123396 prefixEnd_123396 42240972561536297521679 := by
  unfold tailWord_123396
  simp only [CollatzResearch.WordTrace]
  refine ⟨2250310930482420602047021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3000414573976560802729361 2250310930482420602047021)
  ·
    refine ⟨843866598930907725767633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2250310930482420602047021 843866598930907725767633)
    ·
      refine ⟨632899949198180794325725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 843866598930907725767633 632899949198180794325725)
      ·
        refine ⟨237337480949317797872147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 632899949198180794325725 237337480949317797872147)
        ·
          refine ⟨356006221423976696808221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237337480949317797872147 356006221423976696808221)
          ·
            refine ⟨133502333033991261303083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356006221423976696808221 133502333033991261303083)
            ·
              refine ⟨200253499550986891954625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133502333033991261303083 200253499550986891954625)
              ·
                refine ⟨150190124663240168965969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200253499550986891954625 150190124663240168965969)
                ·
                  refine ⟨112642593497430126724477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150190124663240168965969 112642593497430126724477)
                  ·
                    refine ⟨42240972561536297521679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112642593497430126724477 42240972561536297521679)
                    ·
                      rfl

theorem cell22_123396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_123396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123396 prefixEnd_123396 := by exact prefixLift 123396
  have htrace : WordTrace (prefixWord ++ tailWord_123396) baseStart_123396 baseEnd_123396 := by
    simpa [prefixWord, tailWord_123396, baseEnd_123396] using wordTrace_append hprefix tailTrace_123396
  have hstable : (prefixWord ++ tailWord_123396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123396).length < 2 ^ (prefixWord ++ tailWord_123396).sum := by decide
  have hdescent : baseEnd_123396 < baseStart_123396 := by decide
  rcases family_descends (prefixWord ++ tailWord_123396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123398 : List Nat := [6, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_123398 : Nat := 118140960795 + 123398 * 2 ^ 59
def prefixEnd_123398 : Nat := 4983230072969 + 3 ^ 40 * 123398 * 2
def baseEnd_123398 : Nat := 14080552400802986323891

theorem tailTrace_123398 : CollatzResearch.WordTrace tailWord_123398 prefixEnd_123398 14080552400802986323891 := by
  unfold tailWord_123398
  simp only [CollatzResearch.WordTrace]
  refine ⟨140646712717424860802089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3000463204638397030444565 140646712717424860802089)
  ·
    refine ⟨105485034538068645601567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140646712717424860802089 105485034538068645601567)
    ·
      refine ⟨158227551807102968402351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105485034538068645601567 158227551807102968402351)
      ·
        refine ⟨237341327710654452603527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158227551807102968402351 237341327710654452603527)
        ·
          refine ⟨356011991565981678905291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237341327710654452603527 356011991565981678905291)
          ·
            refine ⟨534017987348972518357937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356011991565981678905291 534017987348972518357937)
            ·
              refine ⟨400513490511729388768453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534017987348972518357937 400513490511729388768453)
              ·
                refine ⟨75096279470949260394085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400513490511729388768453 75096279470949260394085)
                ·
                  refine ⟨14080552400802986323891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75096279470949260394085 14080552400802986323891)
                  ·
                    rfl

theorem cell22_123398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_123398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123398 prefixEnd_123398 := by exact prefixLift 123398
  have htrace : WordTrace (prefixWord ++ tailWord_123398) baseStart_123398 baseEnd_123398 := by
    simpa [prefixWord, tailWord_123398, baseEnd_123398] using wordTrace_append hprefix tailTrace_123398
  have hstable : (prefixWord ++ tailWord_123398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123398).length < 2 ^ (prefixWord ++ tailWord_123398).sum := by decide
  have hdescent : baseEnd_123398 < baseStart_123398 := by decide
  rcases family_descends (prefixWord ++ tailWord_123398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123484 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 3, 4]
def baseStart_123484 : Nat := 118140960795 + 123484 * 2 ^ 59
def prefixEnd_123484 : Nat := 4983230072969 + 3 ^ 40 * 123484 * 2
def baseEnd_123484 : Nat := 42271096759933401321409

theorem tailTrace_123484 : CollatzResearch.WordTrace tailWord_123484 prefixEnd_123484 42271096759933401321409 := by
  unfold tailWord_123484
  simp only [CollatzResearch.WordTrace]
  refine ⟨2251915742323016116648753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3002554323097354822198337 2251915742323016116648753)
  ·
    refine ⟨1688936806742262087486565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2251915742323016116648753 1688936806742262087486565)
    ·
      refine ⟨316675651264174141403731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1688936806742262087486565 316675651264174141403731)
      ·
        refine ⟨475013476896261212105597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316675651264174141403731 475013476896261212105597)
        ·
          refine ⟨178130053836097954539599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475013476896261212105597 178130053836097954539599)
          ·
            refine ⟨267195080754146931809399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178130053836097954539599 267195080754146931809399)
            ·
              refine ⟨400792621131220397714099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267195080754146931809399 400792621131220397714099)
              ·
                refine ⟨601188931696830596571149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400792621131220397714099 601188931696830596571149)
                ·
                  refine ⟨225445849386311473714181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601188931696830596571149 225445849386311473714181)
                  ·
                    refine ⟨42271096759933401321409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 225445849386311473714181 42271096759933401321409)
                    ·
                      rfl

theorem cell22_123484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_123484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123484 prefixEnd_123484 := by exact prefixLift 123484
  have htrace : WordTrace (prefixWord ++ tailWord_123484) baseStart_123484 baseEnd_123484 := by
    simpa [prefixWord, tailWord_123484, baseEnd_123484] using wordTrace_append hprefix tailTrace_123484
  have hstable : (prefixWord ++ tailWord_123484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123484).length < 2 ^ (prefixWord ++ tailWord_123484).sum := by decide
  have hdescent : baseEnd_123484 < baseStart_123484 := by decide
  rcases family_descends (prefixWord ++ tailWord_123484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123501 : List Nat := [1, 5, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_123501 : Nat := 118140960795 + 123501 * 2 ^ 59
def prefixEnd_123501 : Nat := 4983230072969 + 3 ^ 40 * 123501 * 2
def baseEnd_123501 : Nat := 42276916207351023646357

theorem tailTrace_123501 : CollatzResearch.WordTrace tailWord_123501 prefixEnd_123501 42276916207351023646357 := by
  unfold tailWord_123501
  simp only [CollatzResearch.WordTrace]
  refine ⟨4504451525584444136666357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3002967683722962757777571 4504451525584444136666357)
  ·
    refine ⟨422292330523541637812471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4504451525584444136666357 422292330523541637812471)
    ·
      refine ⟨633438495785312456718707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422292330523541637812471 633438495785312456718707)
      ·
        refine ⟨950157743677968685078061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633438495785312456718707 950157743677968685078061)
        ·
          refine ⟨356309153879238256904273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 950157743677968685078061 356309153879238256904273)
          ·
            refine ⟨267231865409428692678205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356309153879238256904273 267231865409428692678205)
            ·
              refine ⟨100211949528535759754327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267231865409428692678205 100211949528535759754327)
              ·
                refine ⟨150317924292803639631491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100211949528535759754327 150317924292803639631491)
                ·
                  refine ⟨225476886439205459447237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150317924292803639631491 225476886439205459447237)
                  ·
                    refine ⟨42276916207351023646357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 225476886439205459447237 42276916207351023646357)
                    ·
                      rfl

theorem cell22_123501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_123501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123501 prefixEnd_123501 := by exact prefixLift 123501
  have htrace : WordTrace (prefixWord ++ tailWord_123501) baseStart_123501 baseEnd_123501 := by
    simpa [prefixWord, tailWord_123501, baseEnd_123501] using wordTrace_append hprefix tailTrace_123501
  have hstable : (prefixWord ++ tailWord_123501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123501).length < 2 ^ (prefixWord ++ tailWord_123501).sum := by decide
  have hdescent : baseEnd_123501 < baseStart_123501 := by decide
  rcases family_descends (prefixWord ++ tailWord_123501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123634 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 6]
def baseStart_123634 : Nat := 118140960795 + 123634 * 2 ^ 59
def prefixEnd_123634 : Nat := 4983230072969 + 3 ^ 40 * 123634 * 2
def baseEnd_123634 : Nat := 14107481608461003356983

theorem tailTrace_123634 : CollatzResearch.WordTrace tailWord_123634 prefixEnd_123634 14107481608461003356983 := by
  unfold tailWord_123634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1127325608525651962814489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3006201622735071900838637 1127325608525651962814489)
  ·
    refine ⟨845494206394238972110867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1127325608525651962814489 845494206394238972110867)
    ·
      refine ⟨1268241309591358458166301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 845494206394238972110867 1268241309591358458166301)
      ·
        refine ⟨475590491096759421812363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1268241309591358458166301 475590491096759421812363)
        ·
          refine ⟨713385736645139132718545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475590491096759421812363 713385736645139132718545)
          ·
            refine ⟨535039302483854349538909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713385736645139132718545 535039302483854349538909)
            ·
              refine ⟨200639738431445381077091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 535039302483854349538909 200639738431445381077091)
              ·
                refine ⟨300959607647168071615637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200639738431445381077091 300959607647168071615637)
                ·
                  refine ⟨14107481608461003356983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 300959607647168071615637 14107481608461003356983)
                  ·
                    rfl

theorem cell22_123634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_123634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123634 prefixEnd_123634 := by exact prefixLift 123634
  have htrace : WordTrace (prefixWord ++ tailWord_123634) baseStart_123634 baseEnd_123634 := by
    simpa [prefixWord, tailWord_123634, baseEnd_123634] using wordTrace_append hprefix tailTrace_123634
  have hstable : (prefixWord ++ tailWord_123634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123634).length < 2 ^ (prefixWord ++ tailWord_123634).sum := by decide
  have hdescent : baseEnd_123634 < baseStart_123634 := by decide
  rcases family_descends (prefixWord ++ tailWord_123634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123647 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 6, 4]
def baseStart_123647 : Nat := 118140960795 + 123647 * 2 ^ 59
def prefixEnd_123647 : Nat := 4983230072969 + 3 ^ 40 * 123647 * 2
def baseEnd_123647 : Nat := 42326894991055309495909

theorem tailTrace_123647 : CollatzResearch.WordTrace tailWord_123647 prefixEnd_123647 42326894991055309495909 := by
  unfold tailWord_123647
  simp only [CollatzResearch.WordTrace]
  refine ⟨4509776583055511071481195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3006517722037007380987463 4509776583055511071481195)
  ·
    refine ⟨6764664874583266607221793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4509776583055511071481195 6764664874583266607221793)
    ·
      refine ⟨5073498655937449955416345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6764664874583266607221793 5073498655937449955416345)
      ·
        refine ⟨3805123991953087466562259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5073498655937449955416345 3805123991953087466562259)
        ·
          refine ⟨5707685987929631199843389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3805123991953087466562259 5707685987929631199843389)
          ·
            refine ⟨2140382245473611699941271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5707685987929631199843389 2140382245473611699941271)
            ·
              refine ⟨3210573368210417549911907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140382245473611699941271 3210573368210417549911907)
              ·
                refine ⟨4815860052315626324867861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3210573368210417549911907 4815860052315626324867861)
                ·
                  refine ⟨225743439952294983978181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4815860052315626324867861 225743439952294983978181)
                  ·
                    refine ⟨42326894991055309495909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 225743439952294983978181 42326894991055309495909)
                    ·
                      rfl

theorem cell22_123647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_123647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123647 prefixEnd_123647 := by exact prefixLift 123647
  have htrace : WordTrace (prefixWord ++ tailWord_123647) baseStart_123647 baseEnd_123647 := by
    simpa [prefixWord, tailWord_123647, baseEnd_123647] using wordTrace_append hprefix tailTrace_123647
  have hstable : (prefixWord ++ tailWord_123647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123647).length < 2 ^ (prefixWord ++ tailWord_123647).sum := by decide
  have hdescent : baseEnd_123647 < baseStart_123647 := by decide
  rcases family_descends (prefixWord ++ tailWord_123647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123692 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_123692 : Nat := 118140960795 + 123692 * 2 ^ 59
def prefixEnd_123692 : Nat := 4983230072969 + 3 ^ 40 * 123692 * 2
def baseEnd_123692 : Nat := 42342299410690192120771

theorem tailTrace_123692 : CollatzResearch.WordTrace tailWord_123692 prefixEnd_123692 42342299410690192120771 := by
  unfold tailWord_123692
  simp only [CollatzResearch.WordTrace]
  refine ⟨2255708933946241878434665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3007611911928322504579553 2255708933946241878434665)
  ·
    refine ⟨1691781700459681408825999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2255708933946241878434665 1691781700459681408825999)
    ·
      refine ⟨2537672550689522113238999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1691781700459681408825999 2537672550689522113238999)
      ·
        refine ⟨3806508826034283169858499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2537672550689522113238999 3806508826034283169858499)
        ·
          refine ⟨5709763239051424754787749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3806508826034283169858499 5709763239051424754787749)
          ·
            refine ⟨1070580607322142141522703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5709763239051424754787749 1070580607322142141522703)
            ·
              refine ⟨1605870910983213212284055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070580607322142141522703 1605870910983213212284055)
              ·
                refine ⟨2408806366474819818426083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605870910983213212284055 2408806366474819818426083)
                ·
                  refine ⟨3613209549712229727639125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408806366474819818426083 3613209549712229727639125)
                  ·
                    refine ⟨42342299410690192120771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3613209549712229727639125 42342299410690192120771)
                    ·
                      rfl

theorem cell22_123692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_123692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123692 prefixEnd_123692 := by exact prefixLift 123692
  have htrace : WordTrace (prefixWord ++ tailWord_123692) baseStart_123692 baseEnd_123692 := by
    simpa [prefixWord, tailWord_123692, baseEnd_123692] using wordTrace_append hprefix tailTrace_123692
  have hstable : (prefixWord ++ tailWord_123692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123692).length < 2 ^ (prefixWord ++ tailWord_123692).sum := by decide
  have hdescent : baseEnd_123692 < baseStart_123692 := by decide
  rcases family_descends (prefixWord ++ tailWord_123692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123711 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 3, 3]
def baseStart_123711 : Nat := 118140960795 + 123711 * 2 ^ 59
def prefixEnd_123711 : Nat := 4983230072969 + 3 ^ 40 * 123711 * 2
def baseEnd_123711 : Nat := 42348803498980475895713

theorem tailTrace_123711 : CollatzResearch.WordTrace tailWord_123711 prefixEnd_123711 42348803498980475895713 := by
  unfold tailWord_123711
  simp only [CollatzResearch.WordTrace]
  refine ⟨4512110854823650001810987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3008073903215766667873991 4512110854823650001810987)
  ·
    refine ⟨6768166282235475002716481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4512110854823650001810987 6768166282235475002716481)
    ·
      refine ⟨5076124711676606252037361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6768166282235475002716481 5076124711676606252037361)
      ·
        refine ⟨3807093533757454689028021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5076124711676606252037361 3807093533757454689028021)
        ·
          refine ⟨356915018789761377096377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3807093533757454689028021 356915018789761377096377)
          ·
            refine ⟨267686264092321032822283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356915018789761377096377 267686264092321032822283)
            ·
              refine ⟨401529396138481549233425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267686264092321032822283 401529396138481549233425)
              ·
                refine ⟨301147047103861161925069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401529396138481549233425 301147047103861161925069)
                ·
                  refine ⟨112930142663947935721901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301147047103861161925069 112930142663947935721901)
                  ·
                    refine ⟨42348803498980475895713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112930142663947935721901 42348803498980475895713)
                    ·
                      rfl

theorem cell22_123711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 3].length) (baseStart_123711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123711 prefixEnd_123711 := by exact prefixLift 123711
  have htrace : WordTrace (prefixWord ++ tailWord_123711) baseStart_123711 baseEnd_123711 := by
    simpa [prefixWord, tailWord_123711, baseEnd_123711] using wordTrace_append hprefix tailTrace_123711
  have hstable : (prefixWord ++ tailWord_123711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123711).length < 2 ^ (prefixWord ++ tailWord_123711).sum := by decide
  have hdescent : baseEnd_123711 < baseStart_123711 := by decide
  rcases family_descends (prefixWord ++ tailWord_123711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123713 : List Nat := [1, 2, 5, 3, 1, 1, 3, 6]
def baseStart_123713 : Nat := 118140960795 + 123713 * 2 ^ 59
def prefixEnd_123713 : Nat := 4983230072969 + 3 ^ 40 * 123713 * 2
def baseEnd_123713 : Nat := 4705498682205904149523

theorem tailTrace_123713 : CollatzResearch.WordTrace tailWord_123713 prefixEnd_123713 4705498682205904149523 := by
  unfold tailWord_123713
  simp only [CollatzResearch.WordTrace]
  refine ⟨4512183800816404343383793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3008122533877602895589195 4512183800816404343383793)
  ·
    refine ⟨3384137850612303257537845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4512183800816404343383793 3384137850612303257537845)
    ·
      refine ⟨317262923494903430394173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3384137850612303257537845 317262923494903430394173)
      ·
        refine ⟨118973596310588786397815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317262923494903430394173 118973596310588786397815)
        ·
          refine ⟨178460394465883179596723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118973596310588786397815 178460394465883179596723)
          ·
            refine ⟨267690591698824769395085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178460394465883179596723 267690591698824769395085)
            ·
              refine ⟨100383971887059288523157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267690591698824769395085 100383971887059288523157)
              ·
                refine ⟨4705498682205904149523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100383971887059288523157 4705498682205904149523)
                ·
                  rfl

theorem cell22_123713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 6].length) (baseStart_123713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123713 prefixEnd_123713 := by exact prefixLift 123713
  have htrace : WordTrace (prefixWord ++ tailWord_123713) baseStart_123713 baseEnd_123713 := by
    simpa [prefixWord, tailWord_123713, baseEnd_123713] using wordTrace_append hprefix tailTrace_123713
  have hstable : (prefixWord ++ tailWord_123713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123713).length < 2 ^ (prefixWord ++ tailWord_123713).sum := by decide
  have hdescent : baseEnd_123713 < baseStart_123713 := by decide
  rcases family_descends (prefixWord ++ tailWord_123713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123769 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 6]
def baseStart_123769 : Nat := 118140960795 + 123769 * 2 ^ 59
def prefixEnd_123769 : Nat := 4983230072969 + 3 ^ 40 * 123769 * 2
def baseEnd_123769 : Nat := 14122886028095885981845

theorem tailTrace_123769 : CollatzResearch.WordTrace tailWord_123769 prefixEnd_123769 14122886028095885981845 := by
  unfold tailWord_123769
  simp only [CollatzResearch.WordTrace]
  refine ⟨4514226288613525907422361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3009484192409017271614907 4514226288613525907422361)
  ·
    refine ⟨3385669716460144430566771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4514226288613525907422361 3385669716460144430566771)
    ·
      refine ⟨5078504574690216645850157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3385669716460144430566771 5078504574690216645850157)
      ·
        refine ⟨1904439215508831242193809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5078504574690216645850157 1904439215508831242193809)
        ·
          refine ⟨1428329411631623431645357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1904439215508831242193809 1428329411631623431645357)
          ·
            refine ⟨535623529361858786867009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1428329411631623431645357 535623529361858786867009)
            ·
              refine ⟨401717647021394090150257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535623529361858786867009 401717647021394090150257)
              ·
                refine ⟨301288235266045567612693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401717647021394090150257 301288235266045567612693)
                ·
                  refine ⟨14122886028095885981845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 301288235266045567612693 14122886028095885981845)
                  ·
                    rfl

theorem cell22_123769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 6].length) (baseStart_123769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123769 prefixEnd_123769 := by exact prefixLift 123769
  have htrace : WordTrace (prefixWord ++ tailWord_123769) baseStart_123769 baseEnd_123769 := by
    simpa [prefixWord, tailWord_123769, baseEnd_123769] using wordTrace_append hprefix tailTrace_123769
  have hstable : (prefixWord ++ tailWord_123769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123769).length < 2 ^ (prefixWord ++ tailWord_123769).sum := by decide
  have hdescent : baseEnd_123769 < baseStart_123769 := by decide
  rcases family_descends (prefixWord ++ tailWord_123769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123801 : List Nat := [1, 2, 1, 2, 1, 3, 1, 6, 2, 3]
def baseStart_123801 : Nat := 118140960795 + 123801 * 2 ^ 59
def prefixEnd_123801 : Nat := 4983230072969 + 3 ^ 40 * 123801 * 2
def baseEnd_123801 : Nat := 42379612338250241145437

theorem tailTrace_123801 : CollatzResearch.WordTrace tailWord_123801 prefixEnd_123801 42379612338250241145437 := by
  unfold tailWord_123801
  simp only [CollatzResearch.WordTrace]
  refine ⟨4515393424497595372587257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3010262282998396915058171 4515393424497595372587257)
  ·
    refine ⟨3386545068373196529440443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4515393424497595372587257 3386545068373196529440443)
    ·
      refine ⟨5079817602559794794160665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3386545068373196529440443 5079817602559794794160665)
      ·
        refine ⟨3809863201919846095620499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5079817602559794794160665 3809863201919846095620499)
        ·
          refine ⟨5714794802879769143430749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3809863201919846095620499 5714794802879769143430749)
          ·
            refine ⟨2143048051079913428786531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5714794802879769143430749 2143048051079913428786531)
            ·
              refine ⟨3214572076619870143179797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143048051079913428786531 3214572076619870143179797)
              ·
                refine ⟨150683066091556412961553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3214572076619870143179797 150683066091556412961553)
                ·
                  refine ⟨113012299568667309721165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150683066091556412961553 113012299568667309721165)
                  ·
                    refine ⟨42379612338250241145437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113012299568667309721165 42379612338250241145437)
                    ·
                      rfl

theorem cell22_123801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 3].length) (baseStart_123801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123801 prefixEnd_123801 := by exact prefixLift 123801
  have htrace : WordTrace (prefixWord ++ tailWord_123801) baseStart_123801 baseEnd_123801 := by
    simpa [prefixWord, tailWord_123801, baseEnd_123801] using wordTrace_append hprefix tailTrace_123801
  have hstable : (prefixWord ++ tailWord_123801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123801).length < 2 ^ (prefixWord ++ tailWord_123801).sum := by decide
  have hdescent : baseEnd_123801 < baseStart_123801 := by decide
  rcases family_descends (prefixWord ++ tailWord_123801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123940 : List Nat := [2, 3, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_123940 : Nat := 118140960795 + 123940 * 2 ^ 59
def prefixEnd_123940 : Nat := 4983230072969 + 3 ^ 40 * 123940 * 2
def baseEnd_123940 : Nat := 42427194878900211920011

theorem tailTrace_123940 : CollatzResearch.WordTrace tailWord_123940 prefixEnd_123940 42427194878900211920011 := by
  unfold tailWord_123940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2260231585497011055948637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3013642113996014741264849 2260231585497011055948637)
  ·
    refine ⟨847586844561379145980739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2260231585497011055948637 847586844561379145980739)
    ·
      refine ⟨1271380266842068718971109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 847586844561379145980739 1271380266842068718971109)
      ·
        refine ⟨238383800032887884807083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1271380266842068718971109 238383800032887884807083)
        ·
          refine ⟨357575700049331827210625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238383800032887884807083 357575700049331827210625)
          ·
            refine ⟨268181775036998870407969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357575700049331827210625 268181775036998870407969)
            ·
              refine ⟨201136331277749152805977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268181775036998870407969 201136331277749152805977)
              ·
                refine ⟨150852248458311864604483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201136331277749152805977 150852248458311864604483)
                ·
                  refine ⟨226278372687467796906725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150852248458311864604483 226278372687467796906725)
                  ·
                    refine ⟨42427194878900211920011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 226278372687467796906725 42427194878900211920011)
                    ·
                      rfl

theorem cell22_123940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_123940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_123940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_123940 prefixEnd_123940 := by exact prefixLift 123940
  have htrace : WordTrace (prefixWord ++ tailWord_123940) baseStart_123940 baseEnd_123940 := by
    simpa [prefixWord, tailWord_123940, baseEnd_123940] using wordTrace_append hprefix tailTrace_123940
  have hstable : (prefixWord ++ tailWord_123940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123940).length < 2 ^ (prefixWord ++ tailWord_123940).sum := by decide
  have hdescent : baseEnd_123940 < baseStart_123940 := by decide
  rcases family_descends (prefixWord ++ tailWord_123940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124015 : List Nat := [1, 1, 2, 1, 3, 3, 2, 5, 1, 3]
def baseStart_124015 : Nat := 118140960795 + 124015 * 2 ^ 59
def prefixEnd_124015 : Nat := 4983230072969 + 3 ^ 40 * 124015 * 2
def baseEnd_124015 : Nat := 42452868911625016294781

theorem tailTrace_124015 : CollatzResearch.WordTrace tailWord_124015 prefixEnd_124015 42452868911625016294781 := by
  unfold tailWord_124015
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523198645722309920877499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3015465763814873280584999 4523198645722309920877499)
  ·
    refine ⟨6784797968583464881316249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4523198645722309920877499 6784797968583464881316249)
    ·
      refine ⟨5088598476437598660987187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6784797968583464881316249 5088598476437598660987187)
      ·
        refine ⟨7632897714656397991480781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5088598476437598660987187 7632897714656397991480781)
        ·
          refine ⟨2862336642996149246805293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7632897714656397991480781 2862336642996149246805293)
          ·
            refine ⟨1073376241123555967551985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2862336642996149246805293 1073376241123555967551985)
            ·
              refine ⟨805032180842666975663989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073376241123555967551985 805032180842666975663989)
              ·
                refine ⟨75471766954000028968499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 805032180842666975663989 75471766954000028968499)
                ·
                  refine ⟨113207650431000043452749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75471766954000028968499 113207650431000043452749)
                  ·
                    refine ⟨42452868911625016294781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113207650431000043452749 42452868911625016294781)
                    ·
                      rfl

theorem cell22_124015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 1, 3].length) (baseStart_124015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124015 prefixEnd_124015 := by exact prefixLift 124015
  have htrace : WordTrace (prefixWord ++ tailWord_124015) baseStart_124015 baseEnd_124015 := by
    simpa [prefixWord, tailWord_124015, baseEnd_124015] using wordTrace_append hprefix tailTrace_124015
  have hstable : (prefixWord ++ tailWord_124015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124015).length < 2 ^ (prefixWord ++ tailWord_124015).sum := by decide
  have hdescent : baseEnd_124015 < baseStart_124015 := by decide
  rcases family_descends (prefixWord ++ tailWord_124015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124028 : List Nat := [2, 2, 2, 1, 1, 3, 4, 2, 5]
def baseStart_124028 : Nat := 118140960795 + 124028 * 2 ^ 59
def prefixEnd_124028 : Nat := 4983230072969 + 3 ^ 40 * 124028 * 2
def baseEnd_124028 : Nat := 14152439692432438573247

theorem tailTrace_124028 : CollatzResearch.WordTrace tailWord_124028 prefixEnd_124028 14152439692432438573247 := by
  unfold tailWord_124028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261836397337606570550369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3015781863116808760733825 2261836397337606570550369)
  ·
    refine ⟨1696377298003204927912777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2261836397337606570550369 1696377298003204927912777)
    ·
      refine ⟨1272282973502403695934583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1696377298003204927912777 1272282973502403695934583)
      ·
        refine ⟨1908424460253605543901875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272282973502403695934583 1908424460253605543901875)
        ·
          refine ⟨2862636690380408315852813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908424460253605543901875 2862636690380408315852813)
          ·
            refine ⟨1073488758892653118444805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2862636690380408315852813 1073488758892653118444805)
            ·
              refine ⟨201279142292372459708401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1073488758892653118444805 201279142292372459708401)
              ·
                refine ⟨150959356719279344781301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201279142292372459708401 150959356719279344781301)
                ·
                  refine ⟨14152439692432438573247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150959356719279344781301 14152439692432438573247)
                  ·
                    rfl

theorem cell22_124028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_124028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124028 prefixEnd_124028 := by exact prefixLift 124028
  have htrace : WordTrace (prefixWord ++ tailWord_124028) baseStart_124028 baseEnd_124028 := by
    simpa [prefixWord, tailWord_124028, baseEnd_124028] using wordTrace_append hprefix tailTrace_124028
  have hstable : (prefixWord ++ tailWord_124028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124028).length < 2 ^ (prefixWord ++ tailWord_124028).sum := by decide
  have hdescent : baseEnd_124028 < baseStart_124028 := by decide
  rcases family_descends (prefixWord ++ tailWord_124028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124032 : List Nat := [2, 1, 1, 2, 1, 3, 6, 2, 1, 3]
def baseStart_124032 : Nat := 118140960795 + 124032 * 2 ^ 59
def prefixEnd_124032 : Nat := 4983230072969 + 3 ^ 40 * 124032 * 2
def baseEnd_124032 : Nat := 42458688359042638619729

theorem tailTrace_124032 : CollatzResearch.WordTrace tailWord_124032 prefixEnd_124032 42458688359042638619729 := by
  unfold tailWord_124032
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261909343330360912123175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3015879124440481216164233 2261909343330360912123175)
  ·
    refine ⟨3392864014995541368184763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2261909343330360912123175 3392864014995541368184763)
    ·
      refine ⟨5089296022493312052277145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3392864014995541368184763 5089296022493312052277145)
      ·
        refine ⟨3816972016869984039207859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5089296022493312052277145 3816972016869984039207859)
        ·
          refine ⟨5725458025304976058811789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3816972016869984039207859 5725458025304976058811789)
          ·
            refine ⟨2147046759489366022054421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5725458025304976058811789 2147046759489366022054421)
            ·
              refine ⟨100642816851064032283801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2147046759489366022054421 100642816851064032283801)
              ·
                refine ⟨75482112638298024212851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100642816851064032283801 75482112638298024212851)
                ·
                  refine ⟨113223168957447036319277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75482112638298024212851 113223168957447036319277)
                  ·
                    refine ⟨42458688359042638619729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113223168957447036319277 42458688359042638619729)
                    ·
                      rfl

theorem cell22_124032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 1, 3].length) (baseStart_124032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124032 prefixEnd_124032 := by exact prefixLift 124032
  have htrace : WordTrace (prefixWord ++ tailWord_124032) baseStart_124032 baseEnd_124032 := by
    simpa [prefixWord, tailWord_124032, baseEnd_124032] using wordTrace_append hprefix tailTrace_124032
  have hstable : (prefixWord ++ tailWord_124032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124032).length < 2 ^ (prefixWord ++ tailWord_124032).sum := by decide
  have hdescent : baseEnd_124032 < baseStart_124032 := by decide
  rcases family_descends (prefixWord ++ tailWord_124032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124101 : List Nat := [1, 3, 1, 1, 1, 1, 3, 11]
def baseStart_124101 : Nat := 118140960795 + 124101 * 2 ^ 59
def prefixEnd_124101 : Nat := 4983230072969 + 3 ^ 40 * 124101 * 2
def baseEnd_124101 : Nat := 4720256496572162071613

theorem tailTrace_124101 : CollatzResearch.WordTrace tailWord_124101 prefixEnd_124101 4720256496572162071613 := by
  unfold tailWord_124101
  simp only [CollatzResearch.WordTrace]
  refine ⟨4526335323410746608508157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3017556882273831072338771 4526335323410746608508157)
  ·
    refine ⟨1697375746279029978190559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4526335323410746608508157 1697375746279029978190559)
    ·
      refine ⟨2546063619418544967285839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1697375746279029978190559 2546063619418544967285839)
      ·
        refine ⟨3819095429127817450928759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2546063619418544967285839 3819095429127817450928759)
        ·
          refine ⟨5728643143691726176393139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3819095429127817450928759 5728643143691726176393139)
          ·
            refine ⟨8592964715537589264589709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5728643143691726176393139 8592964715537589264589709)
            ·
              refine ⟨3222361768326595974221141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8592964715537589264589709 3222361768326595974221141)
              ·
                refine ⟨4720256496572162071613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 3222361768326595974221141 4720256496572162071613)
                ·
                  rfl

theorem cell22_124101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 11].length) (baseStart_124101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124101 prefixEnd_124101 := by exact prefixLift 124101
  have htrace : WordTrace (prefixWord ++ tailWord_124101) baseStart_124101 baseEnd_124101 := by
    simpa [prefixWord, tailWord_124101, baseEnd_124101] using wordTrace_append hprefix tailTrace_124101
  have hstable : (prefixWord ++ tailWord_124101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124101).length < 2 ^ (prefixWord ++ tailWord_124101).sum := by decide
  have hdescent : baseEnd_124101 < baseStart_124101 := by decide
  rcases family_descends (prefixWord ++ tailWord_124101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124135 : List Nat := [1, 1, 5, 3, 2, 2, 8]
def baseStart_124135 : Nat := 118140960795 + 124135 * 2 ^ 59
def prefixEnd_124135 : Nat := 4983230072969 + 3 ^ 40 * 124135 * 2
def baseEnd_124135 : Nat := 1573849902369803825719

theorem tailTrace_124135 : CollatzResearch.WordTrace tailWord_124135 prefixEnd_124135 1573849902369803825719 := by
  unfold tailWord_124135
  simp only [CollatzResearch.WordTrace]
  refine ⟨4527575405287570415245859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3018383603525046943497239 4527575405287570415245859)
  ·
    refine ⟨6791363107931355622868789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4527575405287570415245859 6791363107931355622868789)
    ·
      refine ⟨636690291368564589643949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6791363107931355622868789 636690291368564589643949)
      ·
        refine ⟨238758859263211721116481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 636690291368564589643949 238758859263211721116481)
        ·
          refine ⟨179069144447408790837361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238758859263211721116481 179069144447408790837361)
          ·
            refine ⟨134301858335556593128021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179069144447408790837361 134301858335556593128021)
            ·
              refine ⟨1573849902369803825719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 134301858335556593128021 1573849902369803825719)
              ·
                rfl

theorem cell22_124135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 8].length) (baseStart_124135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124135 prefixEnd_124135 := by exact prefixLift 124135
  have htrace : WordTrace (prefixWord ++ tailWord_124135) baseStart_124135 baseEnd_124135 := by
    simpa [prefixWord, tailWord_124135, baseEnd_124135] using wordTrace_append hprefix tailTrace_124135
  have hstable : (prefixWord ++ tailWord_124135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124135).length < 2 ^ (prefixWord ++ tailWord_124135).sum := by decide
  have hdescent : baseEnd_124135 < baseStart_124135 := by decide
  rcases family_descends (prefixWord ++ tailWord_124135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124156 : List Nat := [2, 2, 2, 1, 6, 1, 2, 1, 2, 3]
def baseStart_124156 : Nat := 118140960795 + 124156 * 2 ^ 59
def prefixEnd_124156 : Nat := 4983230072969 + 3 ^ 40 * 124156 * 2
def baseEnd_124156 : Nat := 42501136093147648519349

theorem tailTrace_124156 : CollatzResearch.WordTrace tailWord_124156 prefixEnd_124156 42501136093147648519349 := by
  unfold tailWord_124156
  simp only [CollatzResearch.WordTrace]
  refine ⟨2264170669105745500880161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3018894225474327334506881 2264170669105745500880161)
  ·
    refine ⟨1698128001829309125660121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2264170669105745500880161 1698128001829309125660121)
    ·
      refine ⟨1273596001371981844245091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1698128001829309125660121 1273596001371981844245091)
      ·
        refine ⟨1910394002057972766367637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1273596001371981844245091 1910394002057972766367637)
        ·
          refine ⟨89549718846467473423483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1910394002057972766367637 89549718846467473423483)
          ·
            refine ⟨134324578269701210135225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89549718846467473423483 134324578269701210135225)
            ·
              refine ⟨100743433702275907601419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134324578269701210135225 100743433702275907601419)
              ·
                refine ⟨151115150553413861402129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100743433702275907601419 151115150553413861402129)
                ·
                  refine ⟨113336362915060396051597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151115150553413861402129 113336362915060396051597)
                  ·
                    refine ⟨42501136093147648519349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113336362915060396051597 42501136093147648519349)
                    ·
                      rfl

theorem cell22_124156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_124156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124156 prefixEnd_124156 := by exact prefixLift 124156
  have htrace : WordTrace (prefixWord ++ tailWord_124156) baseStart_124156 baseEnd_124156 := by
    simpa [prefixWord, tailWord_124156, baseEnd_124156] using wordTrace_append hprefix tailTrace_124156
  have hstable : (prefixWord ++ tailWord_124156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124156).length < 2 ^ (prefixWord ++ tailWord_124156).sum := by decide
  have hdescent : baseEnd_124156 < baseStart_124156 := by decide
  rcases family_descends (prefixWord ++ tailWord_124156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124208 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 6]
def baseStart_124208 : Nat := 118140960795 + 124208 * 2 ^ 59
def prefixEnd_124208 : Nat := 4983230072969 + 3 ^ 40 * 124208 * 2
def baseEnd_124208 : Nat := 14172978918612282073063

theorem tailTrace_124208 : CollatzResearch.WordTrace tailWord_124208 prefixEnd_124208 14172978918612282073063 := by
  unfold tailWord_124208
  simp only [CollatzResearch.WordTrace]
  refine ⟨2265118967011551941326639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3020158622682069255102185 2265118967011551941326639)
  ·
    refine ⟨3397678450517327911989959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2265118967011551941326639 3397678450517327911989959)
    ·
      refine ⟨5096517675775991867984939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3397678450517327911989959 5096517675775991867984939)
      ·
        refine ⟨7644776513663987801977409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5096517675775991867984939 7644776513663987801977409)
        ·
          refine ⟨5733582385247990851483057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7644776513663987801977409 5733582385247990851483057)
          ·
            refine ⟨4300186788935993138612293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5733582385247990851483057 4300186788935993138612293)
            ·
              refine ⟨806285022925498713489805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4300186788935993138612293 806285022925498713489805)
              ·
                refine ⟨302356883597062017558677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 806285022925498713489805 302356883597062017558677)
                ·
                  refine ⟨14172978918612282073063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 302356883597062017558677 14172978918612282073063)
                  ·
                    rfl

theorem cell22_124208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 6].length) (baseStart_124208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124208 prefixEnd_124208 := by exact prefixLift 124208
  have htrace : WordTrace (prefixWord ++ tailWord_124208) baseStart_124208 baseEnd_124208 := by
    simpa [prefixWord, tailWord_124208, baseEnd_124208] using wordTrace_append hprefix tailTrace_124208
  have hstable : (prefixWord ++ tailWord_124208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124208).length < 2 ^ (prefixWord ++ tailWord_124208).sum := by decide
  have hdescent : baseEnd_124208 < baseStart_124208 := by decide
  rcases family_descends (prefixWord ++ tailWord_124208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124210 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_124210 : Nat := 118140960795 + 124210 * 2 ^ 59
def prefixEnd_124210 : Nat := 4983230072969 + 3 ^ 40 * 124210 * 2
def baseEnd_124210 : Nat := 42519621396709507669183

theorem tailTrace_124210 : CollatzResearch.WordTrace tailWord_124210 prefixEnd_124210 42519621396709507669183 := by
  unfold tailWord_124210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1132577720003964556056521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3020207253343905482817389 1132577720003964556056521)
  ·
    refine ⟨849433290002973417042391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1132577720003964556056521 849433290002973417042391)
    ·
      refine ⟨1274149935004460125563587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 849433290002973417042391 1274149935004460125563587)
      ·
        refine ⟨1911224902506690188345381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274149935004460125563587 1911224902506690188345381)
        ·
          refine ⟨358354669220004410314759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1911224902506690188345381 358354669220004410314759)
          ·
            refine ⟨537532003830006615472139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358354669220004410314759 537532003830006615472139)
            ·
              refine ⟨806298005745009923208209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537532003830006615472139 806298005745009923208209)
              ·
                refine ⟨604723504308757442406157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806298005745009923208209 604723504308757442406157)
                ·
                  refine ⟨226771314115784040902309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604723504308757442406157 226771314115784040902309)
                  ·
                    refine ⟨42519621396709507669183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 226771314115784040902309 42519621396709507669183)
                    ·
                      rfl

theorem cell22_124210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_124210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124210 prefixEnd_124210 := by exact prefixLift 124210
  have htrace : WordTrace (prefixWord ++ tailWord_124210) baseStart_124210 baseEnd_124210 := by
    simpa [prefixWord, tailWord_124210, baseEnd_124210] using wordTrace_append hprefix tailTrace_124210
  have hstable : (prefixWord ++ tailWord_124210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124210).length < 2 ^ (prefixWord ++ tailWord_124210).sum := by decide
  have hdescent : baseEnd_124210 < baseStart_124210 := by decide
  rcases family_descends (prefixWord ++ tailWord_124210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124225 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 8]
def baseStart_124225 : Nat := 118140960795 + 124225 * 2 ^ 59
def prefixEnd_124225 : Nat := 4983230072969 + 3 ^ 40 * 124225 * 2
def baseEnd_124225 : Nat := 14174918734418156181379

theorem tailTrace_124225 : CollatzResearch.WordTrace tailWord_124225 prefixEnd_124225 14174918734418156181379 := by
  unfold tailWord_124225
  simp only [CollatzResearch.WordTrace]
  refine ⟨4530857974961515786022129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3020571983307677190681419 4530857974961515786022129)
  ·
    refine ⟨3398143481221136839516597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4530857974961515786022129 3398143481221136839516597)
    ·
      refine ⟨318575951364481578704681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3398143481221136839516597 318575951364481578704681)
      ·
        refine ⟨238931963523361184028511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318575951364481578704681 238931963523361184028511)
        ·
          refine ⟨358397945285041776042767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238931963523361184028511 358397945285041776042767)
          ·
            refine ⟨537596917927562664064151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358397945285041776042767 537596917927562664064151)
            ·
              refine ⟨806395376891343996096227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537596917927562664064151 806395376891343996096227)
              ·
                refine ⟨1209593065337015994144341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806395376891343996096227 1209593065337015994144341)
                ·
                  refine ⟨14174918734418156181379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1209593065337015994144341 14174918734418156181379)
                  ·
                    rfl

theorem cell22_124225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 8].length) (baseStart_124225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124225 prefixEnd_124225 := by exact prefixLift 124225
  have htrace : WordTrace (prefixWord ++ tailWord_124225) baseStart_124225 baseEnd_124225 := by
    simpa [prefixWord, tailWord_124225, baseEnd_124225] using wordTrace_append hprefix tailTrace_124225
  have hstable : (prefixWord ++ tailWord_124225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124225).length < 2 ^ (prefixWord ++ tailWord_124225).sum := by decide
  have hdescent : baseEnd_124225 < baseStart_124225 := by decide
  rcases family_descends (prefixWord ++ tailWord_124225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124240 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 4, 3]
def baseStart_124240 : Nat := 118140960795 + 124240 * 2 ^ 59
def prefixEnd_124240 : Nat := 4983230072969 + 3 ^ 40 * 124240 * 2
def baseEnd_124240 : Nat := 42529891009799429419091

theorem tailTrace_124240 : CollatzResearch.WordTrace tailWord_124240 prefixEnd_124240 42529891009799429419091 := by
  unfold tailWord_124240
  simp only [CollatzResearch.WordTrace]
  refine ⟨2265702534953586673909087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3020936713271448898545449 2265702534953586673909087)
  ·
    refine ⟨3398553802430380010863631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2265702534953586673909087 3398553802430380010863631)
    ·
      refine ⟨5097830703645570016295447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3398553802430380010863631 5097830703645570016295447)
      ·
        refine ⟨7646746055468355024443171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5097830703645570016295447 7646746055468355024443171)
        ·
          refine ⟨11470119083202532536664757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7646746055468355024443171 11470119083202532536664757)
          ·
            refine ⟨1075323664050237425312321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11470119083202532536664757 1075323664050237425312321)
            ·
              refine ⟨806492748037678068984241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075323664050237425312321 806492748037678068984241)
              ·
                refine ⟨604869561028258551738181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806492748037678068984241 604869561028258551738181)
                ·
                  refine ⟨113413042692798478450909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 604869561028258551738181 113413042692798478450909)
                  ·
                    refine ⟨42529891009799429419091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113413042692798478450909 42529891009799429419091)
                    ·
                      rfl

theorem cell22_124240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 4, 3].length) (baseStart_124240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124240 prefixEnd_124240 := by exact prefixLift 124240
  have htrace : WordTrace (prefixWord ++ tailWord_124240) baseStart_124240 baseEnd_124240 := by
    simpa [prefixWord, tailWord_124240, baseEnd_124240] using wordTrace_append hprefix tailTrace_124240
  have hstable : (prefixWord ++ tailWord_124240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124240).length < 2 ^ (prefixWord ++ tailWord_124240).sum := by decide
  have hdescent : baseEnd_124240 < baseStart_124240 := by decide
  rcases family_descends (prefixWord ++ tailWord_124240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124274 : List Nat := [3, 2, 1, 2, 1, 2, 5, 1, 2, 3]
def baseStart_124274 : Nat := 118140960795 + 124274 * 2 ^ 59
def prefixEnd_124274 : Nat := 4983230072969 + 3 ^ 40 * 124274 * 2
def baseEnd_124274 : Nat := 42541529904634674068987

theorem tailTrace_124274 : CollatzResearch.WordTrace tailWord_124274 prefixEnd_124274 42541529904634674068987 := by
  unfold tailWord_124274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133161287945999288638969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3021763434522664769703917 1133161287945999288638969)
  ·
    refine ⟨849870965959499466479227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1133161287945999288638969 849870965959499466479227)
    ·
      refine ⟨1274806448939249199718841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 849870965959499466479227 1274806448939249199718841)
      ·
        refine ⟨956104836704436899789131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1274806448939249199718841 956104836704436899789131)
        ·
          refine ⟨1434157255056655349683697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956104836704436899789131 1434157255056655349683697)
          ·
            refine ⟨1075617941292491512262773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1434157255056655349683697 1075617941292491512262773)
            ·
              refine ⟨100839181996171079274635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1075617941292491512262773 100839181996171079274635)
              ·
                refine ⟨151258772994256618911953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100839181996171079274635 151258772994256618911953)
                ·
                  refine ⟨113444079745692464183965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151258772994256618911953 113444079745692464183965)
                  ·
                    refine ⟨42541529904634674068987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113444079745692464183965 42541529904634674068987)
                    ·
                      rfl

theorem cell22_124274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_124274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124274 prefixEnd_124274 := by exact prefixLift 124274
  have htrace : WordTrace (prefixWord ++ tailWord_124274) baseStart_124274 baseEnd_124274 := by
    simpa [prefixWord, tailWord_124274, baseEnd_124274] using wordTrace_append hprefix tailTrace_124274
  have hstable : (prefixWord ++ tailWord_124274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124274).length < 2 ^ (prefixWord ++ tailWord_124274).sum := by decide
  have hdescent : baseEnd_124274 < baseStart_124274 := by decide
  rcases family_descends (prefixWord ++ tailWord_124274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124319 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 3, 3]
def baseStart_124319 : Nat := 118140960795 + 124319 * 2 ^ 59
def prefixEnd_124319 : Nat := 4983230072969 + 3 ^ 40 * 124319 * 2
def baseEnd_124319 : Nat := 42556934324269556693849

theorem tailTrace_124319 : CollatzResearch.WordTrace tailWord_124319 prefixEnd_124319 42556934324269556693849 := by
  unfold tailWord_124319
  simp only [CollatzResearch.WordTrace]
  refine ⟨4534286436620969839944011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3022857624413979893296007 4534286436620969839944011)
  ·
    refine ⟨6801429654931454759916017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4534286436620969839944011 6801429654931454759916017)
    ·
      refine ⟨5101072241198591069937013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6801429654931454759916017 5101072241198591069937013)
      ·
        refine ⟨478225522612367912806595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5101072241198591069937013 478225522612367912806595)
        ·
          refine ⟨717338283918551869209893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478225522612367912806595 717338283918551869209893)
          ·
            refine ⟨134500928234728475476855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 717338283918551869209893 134500928234728475476855)
            ·
              refine ⟨201751392352092713215283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134500928234728475476855 201751392352092713215283)
              ·
                refine ⟨302627088528139069822925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201751392352092713215283 302627088528139069822925)
                ·
                  refine ⟨113485158198052151183597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302627088528139069822925 113485158198052151183597)
                  ·
                    refine ⟨42556934324269556693849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113485158198052151183597 42556934324269556693849)
                    ·
                      rfl

theorem cell22_124319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 3].length) (baseStart_124319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124319 prefixEnd_124319 := by exact prefixLift 124319
  have htrace : WordTrace (prefixWord ++ tailWord_124319) baseStart_124319 baseEnd_124319 := by
    simpa [prefixWord, tailWord_124319, baseEnd_124319] using wordTrace_append hprefix tailTrace_124319
  have hstable : (prefixWord ++ tailWord_124319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124319).length < 2 ^ (prefixWord ++ tailWord_124319).sum := by decide
  have hdescent : baseEnd_124319 < baseStart_124319 := by decide
  rcases family_descends (prefixWord ++ tailWord_124319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124332 : List Nat := [2, 2, 1, 1, 1, 1, 8, 1, 5]
def baseStart_124332 : Nat := 118140960795 + 124332 * 2 ^ 59
def prefixEnd_124332 : Nat := 4983230072969 + 3 ^ 40 * 124332 * 2
def baseEnd_124332 : Nat := 14187128163313952039603

theorem tailTrace_124332 : CollatzResearch.WordTrace tailWord_124332 prefixEnd_124332 14187128163313952039603 := by
  unfold tailWord_124332
  simp only [CollatzResearch.WordTrace]
  refine ⟨2267380292786936530083625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3023173723715915373444833 2267380292786936530083625)
  ·
    refine ⟨1700535219590202397562719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2267380292786936530083625 1700535219590202397562719)
    ·
      refine ⟨2550802829385303596344079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1700535219590202397562719 2550802829385303596344079)
      ·
        refine ⟨3826204244077955394516119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2550802829385303596344079 3826204244077955394516119)
        ·
          refine ⟨5739306366116933091774179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826204244077955394516119 5739306366116933091774179)
          ·
            refine ⟨8608959549175399637661269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739306366116933091774179 8608959549175399637661269)
            ·
              refine ⟨100886244716899214503843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 8608959549175399637661269 100886244716899214503843)
              ·
                refine ⟨151329367075348821755765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100886244716899214503843 151329367075348821755765)
                ·
                  refine ⟨14187128163313952039603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151329367075348821755765 14187128163313952039603)
                  ·
                    rfl

theorem cell22_124332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_124332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124332 prefixEnd_124332 := by exact prefixLift 124332
  have htrace : WordTrace (prefixWord ++ tailWord_124332) baseStart_124332 baseEnd_124332 := by
    simpa [prefixWord, tailWord_124332, baseEnd_124332] using wordTrace_append hprefix tailTrace_124332
  have hstable : (prefixWord ++ tailWord_124332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124332).length < 2 ^ (prefixWord ++ tailWord_124332).sum := by decide
  have hdescent : baseEnd_124332 < baseStart_124332 := by decide
  rcases family_descends (prefixWord ++ tailWord_124332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124392 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 1, 5]
def baseStart_124392 : Nat := 118140960795 + 124392 * 2 ^ 59
def prefixEnd_124392 : Nat := 4983230072969 + 3 ^ 40 * 124392 * 2
def baseEnd_124392 : Nat := 42581923716121699618625

theorem tailTrace_124392 : CollatzResearch.WordTrace tailWord_124392 prefixEnd_124392 42581923716121699618625 := by
  unfold tailWord_124392
  simp only [CollatzResearch.WordTrace]
  refine ⟨2268474482678251653675715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3024632643571002204900953 2268474482678251653675715)
  ·
    refine ⟨3402711724017377480513573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2268474482678251653675715 3402711724017377480513573)
    ·
      refine ⟨638008448253258277596295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3402711724017377480513573 638008448253258277596295)
      ·
        refine ⟨957012672379887416394443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638008448253258277596295 957012672379887416394443)
        ·
          refine ⟨1435519008569831124591665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957012672379887416394443 1435519008569831124591665)
          ·
            refine ⟨1076639256427373343443749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1435519008569831124591665 1076639256427373343443749)
            ·
              refine ⟨201869860580132501895703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1076639256427373343443749 201869860580132501895703)
              ·
                refine ⟨302804790870198752843555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201869860580132501895703 302804790870198752843555)
                ·
                  refine ⟨454207186305298129265333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302804790870198752843555 454207186305298129265333)
                  ·
                    refine ⟨42581923716121699618625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 454207186305298129265333 42581923716121699618625)
                    ·
                      rfl

theorem cell22_124392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_124392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124392 prefixEnd_124392 := by exact prefixLift 124392
  have htrace : WordTrace (prefixWord ++ tailWord_124392) baseStart_124392 baseEnd_124392 := by
    simpa [prefixWord, tailWord_124392, baseEnd_124392] using wordTrace_append hprefix tailTrace_124392
  have hstable : (prefixWord ++ tailWord_124392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124392).length < 2 ^ (prefixWord ++ tailWord_124392).sum := by decide
  have hdescent : baseEnd_124392 < baseStart_124392 := by decide
  rcases family_descends (prefixWord ++ tailWord_124392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124426 : List Nat := [3, 1, 2, 2, 2, 4, 1, 2, 2, 3]
def baseStart_124426 : Nat := 118140960795 + 124426 * 2 ^ 59
def prefixEnd_124426 : Nat := 4983230072969 + 3 ^ 40 * 124426 * 2
def baseEnd_124426 : Nat := 42593562610956944268521

theorem tailTrace_124426 : CollatzResearch.WordTrace tailWord_124426 prefixEnd_124426 42593562610956944268521 := by
  unfold tailWord_124426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1134547261808331778522283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3025459364822218076059421 1134547261808331778522283)
  ·
    refine ⟨1701820892712497667783425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1134547261808331778522283 1701820892712497667783425)
    ·
      refine ⟨1276365669534373250837569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1701820892712497667783425 1276365669534373250837569)
      ·
        refine ⟨957274252150779938128177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1276365669534373250837569 957274252150779938128177)
        ·
          refine ⟨717955689113084953596133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 957274252150779938128177 717955689113084953596133)
          ·
            refine ⟨134616691708703428799275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 717955689113084953596133 134616691708703428799275)
            ·
              refine ⟨201925037563055143198913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134616691708703428799275 201925037563055143198913)
              ·
                refine ⟨151443778172291357399185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201925037563055143198913 151443778172291357399185)
                ·
                  refine ⟨113582833629218518049389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151443778172291357399185 113582833629218518049389)
                  ·
                    refine ⟨42593562610956944268521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113582833629218518049389 42593562610956944268521)
                    ·
                      rfl

theorem cell22_124426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_124426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124426 prefixEnd_124426 := by exact prefixLift 124426
  have htrace : WordTrace (prefixWord ++ tailWord_124426) baseStart_124426 baseEnd_124426 := by
    simpa [prefixWord, tailWord_124426, baseEnd_124426] using wordTrace_append hprefix tailTrace_124426
  have hstable : (prefixWord ++ tailWord_124426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124426).length < 2 ^ (prefixWord ++ tailWord_124426).sum := by decide
  have hdescent : baseEnd_124426 < baseStart_124426 := by decide
  rcases family_descends (prefixWord ++ tailWord_124426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124456 : List Nat := [2, 1, 5, 2, 2, 2, 2, 6]
def baseStart_124456 : Nat := 118140960795 + 124456 * 2 ^ 59
def prefixEnd_124456 : Nat := 4983230072969 + 3 ^ 40 * 124456 * 2
def baseEnd_124456 : Nat := 4733759136005207335381

theorem tailTrace_124456 : CollatzResearch.WordTrace tailWord_124456 prefixEnd_124456 4733759136005207335381 := by
  unfold tailWord_124456
  simp only [CollatzResearch.WordTrace]
  refine ⟨2269641618562321118840611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3026188824749761491787481 2269641618562321118840611)
  ·
    refine ⟨3404462427843481678260917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2269641618562321118840611 3404462427843481678260917)
    ·
      refine ⟨319168352610326407336961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3404462427843481678260917 319168352610326407336961)
      ·
        refine ⟨239376264457744805502721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319168352610326407336961 239376264457744805502721)
        ·
          refine ⟨179532198343308604127041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239376264457744805502721 179532198343308604127041)
          ·
            refine ⟨134649148757481453095281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179532198343308604127041 134649148757481453095281)
            ·
              refine ⟨100986861568111089821461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134649148757481453095281 100986861568111089821461)
              ·
                refine ⟨4733759136005207335381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100986861568111089821461 4733759136005207335381)
                ·
                  rfl

theorem cell22_124456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 6].length) (baseStart_124456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124456 prefixEnd_124456 := by exact prefixLift 124456
  have htrace : WordTrace (prefixWord ++ tailWord_124456) baseStart_124456 baseEnd_124456 := by
    simpa [prefixWord, tailWord_124456, baseEnd_124456] using wordTrace_append hprefix tailTrace_124456
  have hstable : (prefixWord ++ tailWord_124456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124456).length < 2 ^ (prefixWord ++ tailWord_124456).sum := by decide
  have hdescent : baseEnd_124456 < baseStart_124456 := by decide
  rcases family_descends (prefixWord ++ tailWord_124456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124471 : List Nat := [1, 1, 3, 1, 2, 4, 3, 3, 1, 3]
def baseStart_124471 : Nat := 118140960795 + 124471 * 2 ^ 59
def prefixEnd_124471 : Nat := 4983230072969 + 3 ^ 40 * 124471 * 2
def baseEnd_124471 : Nat := 42608967030591826893383

theorem tailTrace_124471 : CollatzResearch.WordTrace tailWord_124471 prefixEnd_124471 42608967030591826893383 := by
  unfold tailWord_124471
  simp only [CollatzResearch.WordTrace]
  refine ⟨4539830332070299799477267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3026553554713533199651511 4539830332070299799477267)
  ·
    refine ⟨6809745498105449699215901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4539830332070299799477267 6809745498105449699215901)
    ·
      refine ⟨2553654561789543637205963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6809745498105449699215901 2553654561789543637205963)
      ·
        refine ⟨3830481842684315455808945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2553654561789543637205963 3830481842684315455808945)
        ·
          refine ⟨2872861382013236591856709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3830481842684315455808945 2872861382013236591856709)
          ·
            refine ⟨538661509127481860973133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2872861382013236591856709 538661509127481860973133)
            ·
              refine ⟨201998065922805697864925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 538661509127481860973133 201998065922805697864925)
              ·
                refine ⟨75749274721052136699347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201998065922805697864925 75749274721052136699347)
                ·
                  refine ⟨113623912081578205049021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75749274721052136699347 113623912081578205049021)
                  ·
                    refine ⟨42608967030591826893383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113623912081578205049021 42608967030591826893383)
                    ·
                      rfl

theorem cell22_124471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_124471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124471 prefixEnd_124471 := by exact prefixLift 124471
  have htrace : WordTrace (prefixWord ++ tailWord_124471) baseStart_124471 baseEnd_124471 := by
    simpa [prefixWord, tailWord_124471, baseEnd_124471] using wordTrace_append hprefix tailTrace_124471
  have hstable : (prefixWord ++ tailWord_124471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124471).length < 2 ^ (prefixWord ++ tailWord_124471).sum := by decide
  have hdescent : baseEnd_124471 < baseStart_124471 := by decide
  rcases family_descends (prefixWord ++ tailWord_124471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124497 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 3, 4]
def baseStart_124497 : Nat := 118140960795 + 124497 * 2 ^ 59
def prefixEnd_124497 : Nat := 4983230072969 + 3 ^ 40 * 124497 * 2
def baseEnd_124497 : Nat := 42617867361936425743303

theorem tailTrace_124497 : CollatzResearch.WordTrace tailWord_124497 prefixEnd_124497 42617867361936425743303 := by
  unfold tailWord_124497
  simp only [CollatzResearch.WordTrace]
  refine ⟨4540778629976106239923745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3027185753317404159949163 4540778629976106239923745)
  ·
    refine ⟨3405583972482079679942809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4540778629976106239923745 3405583972482079679942809)
    ·
      refine ⟨2554187979361559759957107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3405583972482079679942809 2554187979361559759957107)
      ·
        refine ⟨3831281969042339639935661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2554187979361559759957107 3831281969042339639935661)
        ·
          refine ⟨1436730738390877364975873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3831281969042339639935661 1436730738390877364975873)
          ·
            refine ⟨1077548053793158023731905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1436730738390877364975873 1077548053793158023731905)
            ·
              refine ⟨808161040344868517798929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1077548053793158023731905 808161040344868517798929)
              ·
                refine ⟨606120780258651388349197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808161040344868517798929 606120780258651388349197)
                ·
                  refine ⟨227295292596994270630949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 606120780258651388349197 227295292596994270630949)
                  ·
                    refine ⟨42617867361936425743303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227295292596994270630949 42617867361936425743303)
                    ·
                      rfl

theorem cell22_124497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_124497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124497 prefixEnd_124497 := by exact prefixLift 124497
  have htrace : WordTrace (prefixWord ++ tailWord_124497) baseStart_124497 baseEnd_124497 := by
    simpa [prefixWord, tailWord_124497, baseEnd_124497] using wordTrace_append hprefix tailTrace_124497
  have hstable : (prefixWord ++ tailWord_124497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124497).length < 2 ^ (prefixWord ++ tailWord_124497).sum := by decide
  have hdescent : baseEnd_124497 < baseStart_124497 := by decide
  rcases family_descends (prefixWord ++ tailWord_124497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124576 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 2, 4]
def baseStart_124576 : Nat := 118140960795 + 124576 * 2 ^ 59
def prefixEnd_124576 : Nat := 4983230072969 + 3 ^ 40 * 124576 * 2
def baseEnd_124576 : Nat := 42644910676406553018061

theorem tailTrace_124576 : CollatzResearch.WordTrace tailWord_124576 prefixEnd_124576 42644910676406553018061 := by
  unfold tailWord_124576
  simp only [CollatzResearch.WordTrace]
  refine ⟨2271829998344951366024791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3029106664459935154699721 2271829998344951366024791)
  ·
    refine ⟨3407744997517427049037187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2271829998344951366024791 3407744997517427049037187)
    ·
      refine ⟨5111617496276140573555781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3407744997517427049037187 5111617496276140573555781)
      ·
        refine ⟨958428280551776357541709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5111617496276140573555781 958428280551776357541709)
        ·
          refine ⟨359410605206916134078141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 958428280551776357541709 359410605206916134078141)
          ·
            refine ⟨134778976952593550279303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359410605206916134078141 134778976952593550279303)
            ·
              refine ⟨202168465428890325418955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134778976952593550279303 202168465428890325418955)
              ·
                refine ⟨303252698143335488128433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202168465428890325418955 303252698143335488128433)
                ·
                  refine ⟨227439523607501616096325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303252698143335488128433 227439523607501616096325)
                  ·
                    refine ⟨42644910676406553018061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227439523607501616096325 42644910676406553018061)
                    ·
                      rfl

theorem cell22_124576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 2, 4].length) (baseStart_124576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124576 prefixEnd_124576 := by exact prefixLift 124576
  have htrace : WordTrace (prefixWord ++ tailWord_124576) baseStart_124576 baseEnd_124576 := by
    simpa [prefixWord, tailWord_124576, baseEnd_124576] using wordTrace_append hprefix tailTrace_124576
  have hstable : (prefixWord ++ tailWord_124576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124576).length < 2 ^ (prefixWord ++ tailWord_124576).sum := by decide
  have hdescent : baseEnd_124576 < baseStart_124576 := by decide
  rcases family_descends (prefixWord ++ tailWord_124576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124606 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_124606 : Nat := 118140960795 + 124606 * 2 ^ 59
def prefixEnd_124606 : Nat := 4983230072969 + 3 ^ 40 * 124606 * 2
def baseEnd_124606 : Nat := 42655180289496474767969

theorem tailTrace_124606 : CollatzResearch.WordTrace tailWord_124606 prefixEnd_124606 42655180289496474767969 := by
  unfold tailWord_124606
  simp only [CollatzResearch.WordTrace]
  refine ⟨568094273322652231955209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3029836124387478570427781 568094273322652231955209)
  ·
    refine ⟨426070704991989173966407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 568094273322652231955209 426070704991989173966407)
    ·
      refine ⟨639106057487983760949611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426070704991989173966407 639106057487983760949611)
      ·
        refine ⟨958659086231975641424417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639106057487983760949611 958659086231975641424417)
        ·
          refine ⟨718994314673981731068313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 958659086231975641424417 718994314673981731068313)
          ·
            refine ⟨539245736005486298301235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718994314673981731068313 539245736005486298301235)
            ·
              refine ⟨808868604008229447451853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539245736005486298301235 808868604008229447451853)
              ·
                refine ⟨303325726503086042794445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 808868604008229447451853 303325726503086042794445)
                ·
                  refine ⟨113747147438657266047917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303325726503086042794445 113747147438657266047917)
                  ·
                    refine ⟨42655180289496474767969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113747147438657266047917 42655180289496474767969)
                    ·
                      rfl

theorem cell22_124606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_124606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124606 prefixEnd_124606 := by exact prefixLift 124606
  have htrace : WordTrace (prefixWord ++ tailWord_124606) baseStart_124606 baseEnd_124606 := by
    simpa [prefixWord, tailWord_124606, baseEnd_124606] using wordTrace_append hprefix tailTrace_124606
  have hstable : (prefixWord ++ tailWord_124606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124606).length < 2 ^ (prefixWord ++ tailWord_124606).sum := by decide
  have hdescent : baseEnd_124606 < baseStart_124606 := by decide
  rcases family_descends (prefixWord ++ tailWord_124606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124670 : List Nat := [4, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_124670 : Nat := 118140960795 + 124670 * 2 ^ 59
def prefixEnd_124670 : Nat := 4983230072969 + 3 ^ 40 * 124670 * 2
def baseEnd_124670 : Nat := 14225696265807213722591

theorem tailTrace_124670 : CollatzResearch.WordTrace tailWord_124670 prefixEnd_124670 14225696265807213722591 := by
  unfold tailWord_124670
  simp only [CollatzResearch.WordTrace]
  refine ⟨568386057293669598246433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3031392305566237857314309 568386057293669598246433)
  ·
    refine ⟨426289542970252198684825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 568386057293669598246433 426289542970252198684825)
    ·
      refine ⟨319717157227689149013619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426289542970252198684825 319717157227689149013619)
      ·
        refine ⟨479575735841533723520429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319717157227689149013619 479575735841533723520429)
        ·
          refine ⟨179840900940575146320161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479575735841533723520429 179840900940575146320161)
          ·
            refine ⟨134880675705431359740121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179840900940575146320161 134880675705431359740121)
            ·
              refine ⟨101160506779073519805091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134880675705431359740121 101160506779073519805091)
              ·
                refine ⟨151740760168610279707637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101160506779073519805091 151740760168610279707637)
                ·
                  refine ⟨14225696265807213722591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151740760168610279707637 14225696265807213722591)
                  ·
                    rfl

theorem cell22_124670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_124670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124670 prefixEnd_124670 := by exact prefixLift 124670
  have htrace : WordTrace (prefixWord ++ tailWord_124670) baseStart_124670 baseEnd_124670 := by
    simpa [prefixWord, tailWord_124670, baseEnd_124670] using wordTrace_append hprefix tailTrace_124670
  have hstable : (prefixWord ++ tailWord_124670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124670).length < 2 ^ (prefixWord ++ tailWord_124670).sum := by decide
  have hdescent : baseEnd_124670 < baseStart_124670 := by decide
  rcases family_descends (prefixWord ++ tailWord_124670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124741 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 3, 3]
def baseStart_124741 : Nat := 118140960795 + 124741 * 2 ^ 59
def prefixEnd_124741 : Nat := 4983230072969 + 3 ^ 40 * 124741 * 2
def baseEnd_124741 : Nat := 42701393548401122642555

theorem tailTrace_124741 : CollatzResearch.WordTrace tailWord_124741 prefixEnd_124741 42701393548401122642555 := by
  unfold tailWord_124741
  simp only [CollatzResearch.WordTrace]
  refine ⟨4549678041092135911806077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3033118694061423941204051 4549678041092135911806077)
  ·
    refine ⟨1706129265409550966927279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4549678041092135911806077 1706129265409550966927279)
    ·
      refine ⟨2559193898114326450390919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1706129265409550966927279 2559193898114326450390919)
      ·
        refine ⟨3838790847171489675586379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2559193898114326450390919 3838790847171489675586379)
        ·
          refine ⟨5758186270757234513379569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3838790847171489675586379 5758186270757234513379569)
          ·
            refine ⟨4318639703067925885034677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5758186270757234513379569 4318639703067925885034677)
            ·
              refine ⟨404872472162618051722001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4318639703067925885034677 404872472162618051722001)
              ·
                refine ⟨303654354121963538791501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404872472162618051722001 303654354121963538791501)
                ·
                  refine ⟨113870382795736327046813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303654354121963538791501 113870382795736327046813)
                  ·
                    refine ⟨42701393548401122642555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113870382795736327046813 42701393548401122642555)
                    ·
                      rfl

theorem cell22_124741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_124741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124741 prefixEnd_124741 := by exact prefixLift 124741
  have htrace : WordTrace (prefixWord ++ tailWord_124741) baseStart_124741 baseEnd_124741 := by
    simpa [prefixWord, tailWord_124741, baseEnd_124741] using wordTrace_append hprefix tailTrace_124741
  have hstable : (prefixWord ++ tailWord_124741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124741).length < 2 ^ (prefixWord ++ tailWord_124741).sum := by decide
  have hdescent : baseEnd_124741 < baseStart_124741 := by decide
  rcases family_descends (prefixWord ++ tailWord_124741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124769 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 4, 5]
def baseStart_124769 : Nat := 118140960795 + 124769 * 2 ^ 59
def prefixEnd_124769 : Nat := 4983230072969 + 3 ^ 40 * 124769 * 2
def baseEnd_124769 : Nat := 42710978520618382942469

theorem tailTrace_124769 : CollatzResearch.WordTrace tailWord_124769 prefixEnd_124769 42710978520618382942469 := by
  unfold tailWord_124769
  simp only [CollatzResearch.WordTrace]
  refine ⟨4550699284990696693825361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3033799523327131129216907 4550699284990696693825361)
  ·
    refine ⟨3413024463743022520369021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4550699284990696693825361 3413024463743022520369021)
    ·
      refine ⟨1279884173903633445138383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3413024463743022520369021 1279884173903633445138383)
      ·
        refine ⟨1919826260855450167707575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1279884173903633445138383 1919826260855450167707575)
        ·
          refine ⟨2879739391283175251561363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919826260855450167707575 2879739391283175251561363)
          ·
            refine ⟨4319609086924762877342045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879739391283175251561363 4319609086924762877342045)
            ·
              refine ⟨1619853407596786079003267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4319609086924762877342045 1619853407596786079003267)
              ·
                refine ⟨2429780111395179118504901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1619853407596786079003267 2429780111395179118504901)
                ·
                  refine ⟨455583770886596084719669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2429780111395179118504901 455583770886596084719669)
                  ·
                    refine ⟨42710978520618382942469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 455583770886596084719669 42710978520618382942469)
                    ·
                      rfl

theorem cell22_124769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_124769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124769 prefixEnd_124769 := by exact prefixLift 124769
  have htrace : WordTrace (prefixWord ++ tailWord_124769) baseStart_124769 baseEnd_124769 := by
    simpa [prefixWord, tailWord_124769, baseEnd_124769] using wordTrace_append hprefix tailTrace_124769
  have hstable : (prefixWord ++ tailWord_124769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124769).length < 2 ^ (prefixWord ++ tailWord_124769).sum := by decide
  have hdescent : baseEnd_124769 < baseStart_124769 := by decide
  rcases family_descends (prefixWord ++ tailWord_124769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124771 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 7]
def baseStart_124771 : Nat := 118140960795 + 124771 * 2 ^ 59
def prefixEnd_124771 : Nat := 4983230072969 + 3 ^ 40 * 124771 * 2
def baseEnd_124771 : Nat := 14237221053830348130821

theorem tailTrace_124771 : CollatzResearch.WordTrace tailWord_124771 prefixEnd_124771 14237221053830348130821 := by
  unfold tailWord_124771
  simp only [CollatzResearch.WordTrace]
  refine ⟨4550772230983451035398167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3033848153988967356932111 4550772230983451035398167)
  ·
    refine ⟨6826158346475176553097251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4550772230983451035398167 6826158346475176553097251)
    ·
      refine ⟨10239237519712764829645877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6826158346475176553097251 10239237519712764829645877)
      ·
        refine ⟨959928517473071702779301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10239237519712764829645877 959928517473071702779301)
        ·
          refine ⟨179986597026200944271119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 959928517473071702779301 179986597026200944271119)
          ·
            refine ⟨269979895539301416406679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179986597026200944271119 269979895539301416406679)
            ·
              refine ⟨404969843308952124610019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269979895539301416406679 404969843308952124610019)
              ·
                refine ⟨607454764963428186915029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404969843308952124610019 607454764963428186915029)
                ·
                  refine ⟨14237221053830348130821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 607454764963428186915029 14237221053830348130821)
                  ·
                    rfl

theorem cell22_124771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 7].length) (baseStart_124771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124771 prefixEnd_124771 := by exact prefixLift 124771
  have htrace : WordTrace (prefixWord ++ tailWord_124771) baseStart_124771 baseEnd_124771 := by
    simpa [prefixWord, tailWord_124771, baseEnd_124771] using wordTrace_append hprefix tailTrace_124771
  have hstable : (prefixWord ++ tailWord_124771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124771).length < 2 ^ (prefixWord ++ tailWord_124771).sum := by decide
  have hdescent : baseEnd_124771 < baseStart_124771 := by decide
  rcases family_descends (prefixWord ++ tailWord_124771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124859 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 1, 9]
def baseStart_124859 : Nat := 118140960795 + 124859 * 2 ^ 59
def prefixEnd_124859 : Nat := 4983230072969 + 3 ^ 40 * 124859 * 2
def baseEnd_124859 : Nat := 42741787359888148192193

theorem tailTrace_124859 : CollatzResearch.WordTrace tailWord_124859 prefixEnd_124859 42741787359888148192193 := by
  unfold tailWord_124859
  simp only [CollatzResearch.WordTrace]
  refine ⟨4553981854664642064601631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3035987903109761376401087 4553981854664642064601631)
  ·
    refine ⟨6830972781996963096902447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4553981854664642064601631 6830972781996963096902447)
    ·
      refine ⟨10246459172995444645353671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6830972781996963096902447 10246459172995444645353671)
      ·
        refine ⟨15369688759493166968030507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10246459172995444645353671 15369688759493166968030507)
        ·
          refine ⟨23054533139239750452045761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15369688759493166968030507 23054533139239750452045761)
          ·
            refine ⟨17290899854429812839034321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23054533139239750452045761 17290899854429812839034321)
            ·
              refine ⟨12968174890822359629275741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17290899854429812839034321 12968174890822359629275741)
              ·
                refine ⟨4863065584058384860978403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12968174890822359629275741 4863065584058384860978403)
                ·
                  refine ⟨7294598376087577291467605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4863065584058384860978403 7294598376087577291467605)
                  ·
                    refine ⟨42741787359888148192193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 7294598376087577291467605 42741787359888148192193)
                    ·
                      rfl

theorem cell22_124859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_124859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124859 prefixEnd_124859 := by exact prefixLift 124859
  have htrace : WordTrace (prefixWord ++ tailWord_124859) baseStart_124859 baseEnd_124859 := by
    simpa [prefixWord, tailWord_124859, baseEnd_124859] using wordTrace_append hprefix tailTrace_124859
  have hstable : (prefixWord ++ tailWord_124859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124859).length < 2 ^ (prefixWord ++ tailWord_124859).sum := by decide
  have hdescent : baseEnd_124859 < baseStart_124859 := by decide
  rcases family_descends (prefixWord ++ tailWord_124859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124861 : List Nat := [1, 4, 1, 2, 3, 1, 2, 8]
def baseStart_124861 : Nat := 118140960795 + 124861 * 2 ^ 59
def prefixEnd_124861 : Nat := 4983230072969 + 3 ^ 40 * 124861 * 2
def baseEnd_124861 : Nat := 4749163555640089960243

theorem tailTrace_124861 : CollatzResearch.WordTrace tailWord_124861 prefixEnd_124861 4749163555640089960243 := by
  unfold tailWord_124861
  simp only [CollatzResearch.WordTrace]
  refine ⟨4554054800657396406174437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3036036533771597604116291 4554054800657396406174437)
  ·
    refine ⟨853885275123261826157707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4554054800657396406174437 853885275123261826157707)
    ·
      refine ⟨1280827912684892739236561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 853885275123261826157707 1280827912684892739236561)
      ·
        refine ⟨960620934513669554427421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1280827912684892739236561 960620934513669554427421)
        ·
          refine ⟨360232850442626082910283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 960620934513669554427421 360232850442626082910283)
          ·
            refine ⟨540349275663939124365425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360232850442626082910283 540349275663939124365425)
            ·
              refine ⟨405261956747954343274069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540349275663939124365425 405261956747954343274069)
              ·
                refine ⟨4749163555640089960243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 405261956747954343274069 4749163555640089960243)
                ·
                  rfl

theorem cell22_124861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 8].length) (baseStart_124861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124861 prefixEnd_124861 := by exact prefixLift 124861
  have htrace : WordTrace (prefixWord ++ tailWord_124861) baseStart_124861 baseEnd_124861 := by
    simpa [prefixWord, tailWord_124861, baseEnd_124861] using wordTrace_append hprefix tailTrace_124861
  have hstable : (prefixWord ++ tailWord_124861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124861).length < 2 ^ (prefixWord ++ tailWord_124861).sum := by decide
  have hdescent : baseEnd_124861 < baseStart_124861 := by decide
  rcases family_descends (prefixWord ++ tailWord_124861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124882 : List Nat := [3, 2, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_124882 : Nat := 118140960795 + 124882 * 2 ^ 59
def prefixEnd_124882 : Nat := 4983230072969 + 3 ^ 40 * 124882 * 2
def baseEnd_124882 : Nat := 42749660729923754867123

theorem tailTrace_124882 : CollatzResearch.WordTrace tailWord_124882 prefixEnd_124882 42749660729923754867123 := by
  unfold tailWord_124882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1138705183395329248172225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3036547155720877995125933 1138705183395329248172225)
  ·
    refine ⟨854028887546496936129169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1138705183395329248172225 854028887546496936129169)
    ·
      refine ⟨640521665659872702096877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 854028887546496936129169 640521665659872702096877)
      ·
        refine ⟨240195624622452263286329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 640521665659872702096877 240195624622452263286329)
        ·
          refine ⟨180146718466839197464747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240195624622452263286329 180146718466839197464747)
          ·
            refine ⟨270220077700258796197121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180146718466839197464747 270220077700258796197121)
            ·
              refine ⟨202665058275194097147841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270220077700258796197121 202665058275194097147841)
              ·
                refine ⟨151998793706395572860881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202665058275194097147841 151998793706395572860881)
                ·
                  refine ⟨113999095279796679645661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151998793706395572860881 113999095279796679645661)
                  ·
                    refine ⟨42749660729923754867123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113999095279796679645661 42749660729923754867123)
                    ·
                      rfl

theorem cell22_124882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_124882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124882 prefixEnd_124882 := by exact prefixLift 124882
  have htrace : WordTrace (prefixWord ++ tailWord_124882) baseStart_124882 baseEnd_124882 := by
    simpa [prefixWord, tailWord_124882, baseEnd_124882] using wordTrace_append hprefix tailTrace_124882
  have hstable : (prefixWord ++ tailWord_124882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124882).length < 2 ^ (prefixWord ++ tailWord_124882).sum := by decide
  have hdescent : baseEnd_124882 < baseStart_124882 := by decide
  rcases family_descends (prefixWord ++ tailWord_124882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124910 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_124910 : Nat := 118140960795 + 124910 * 2 ^ 59
def prefixEnd_124910 : Nat := 4983230072969 + 3 ^ 40 * 124910 * 2
def baseEnd_124910 : Nat := 42759245702141015167037

theorem tailTrace_124910 : CollatzResearch.WordTrace tailWord_124910 prefixEnd_124910 42759245702141015167037 := by
  unfold tailWord_124910
  simp only [CollatzResearch.WordTrace]
  refine ⟨569480247184984721838523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3037227984986585183138789 569480247184984721838523)
  ·
    refine ⟨854220370777477082757785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 569480247184984721838523 854220370777477082757785)
    ·
      refine ⟨640665278083107812068339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 854220370777477082757785 640665278083107812068339)
      ·
        refine ⟨960997917124661718102509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640665278083107812068339 960997917124661718102509)
        ·
          refine ⟨360374218921748144288441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 960997917124661718102509 360374218921748144288441)
          ·
            refine ⟨270280664191311108216331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360374218921748144288441 270280664191311108216331)
            ·
              refine ⟨405420996286966662324497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270280664191311108216331 405420996286966662324497)
              ·
                refine ⟨304065747215224996743373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405420996286966662324497 304065747215224996743373)
                ·
                  refine ⟨114024655205709373778765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304065747215224996743373 114024655205709373778765)
                  ·
                    refine ⟨42759245702141015167037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114024655205709373778765 42759245702141015167037)
                    ·
                      rfl

theorem cell22_124910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_124910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124910 prefixEnd_124910 := by exact prefixLift 124910
  have htrace : WordTrace (prefixWord ++ tailWord_124910) baseStart_124910 baseEnd_124910 := by
    simpa [prefixWord, tailWord_124910, baseEnd_124910] using wordTrace_append hprefix tailTrace_124910
  have hstable : (prefixWord ++ tailWord_124910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124910).length < 2 ^ (prefixWord ++ tailWord_124910).sum := by decide
  have hdescent : baseEnd_124910 < baseStart_124910 := by decide
  rcases family_descends (prefixWord ++ tailWord_124910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124970 : List Nat := [3, 1, 4, 1, 2, 1, 1, 4, 1, 4]
def baseStart_124970 : Nat := 118140960795 + 124970 * 2 ^ 59
def prefixEnd_124970 : Nat := 4983230072969 + 3 ^ 40 * 124970 * 2
def baseEnd_124970 : Nat := 42779784928320858666853

theorem tailTrace_124970 : CollatzResearch.WordTrace tailWord_124970 prefixEnd_124970 42779784928320858666853 := by
  unfold tailWord_124970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139507589315627005473091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3038686904841672014594909 1139507589315627005473091)
  ·
    refine ⟨1709261383973440508209637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1139507589315627005473091 1709261383973440508209637)
    ·
      refine ⟨320486509495020095289307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1709261383973440508209637 320486509495020095289307)
      ·
        refine ⟨480729764242530142933961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320486509495020095289307 480729764242530142933961)
        ·
          refine ⟨360547323181897607200471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480729764242530142933961 360547323181897607200471)
          ·
            refine ⟨540820984772846410800707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360547323181897607200471 540820984772846410800707)
            ·
              refine ⟨811231477159269616201061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540820984772846410800707 811231477159269616201061)
              ·
                refine ⟨152105901967363053037699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 811231477159269616201061 152105901967363053037699)
                ·
                  refine ⟨228158852951044579556549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152105901967363053037699 228158852951044579556549)
                  ·
                    refine ⟨42779784928320858666853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 228158852951044579556549 42779784928320858666853)
                    ·
                      rfl

theorem cell22_124970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_124970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124970 prefixEnd_124970 := by exact prefixLift 124970
  have htrace : WordTrace (prefixWord ++ tailWord_124970) baseStart_124970 baseEnd_124970 := by
    simpa [prefixWord, tailWord_124970, baseEnd_124970] using wordTrace_append hprefix tailTrace_124970
  have hstable : (prefixWord ++ tailWord_124970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124970).length < 2 ^ (prefixWord ++ tailWord_124970).sum := by decide
  have hdescent : baseEnd_124970 < baseStart_124970 := by decide
  rcases family_descends (prefixWord ++ tailWord_124970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124983 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 4, 3]
def baseStart_124983 : Nat := 118140960795 + 124983 * 2 ^ 59
def prefixEnd_124983 : Nat := 4983230072969 + 3 ^ 40 * 124983 * 2
def baseEnd_124983 : Nat := 42784235093993158091813

theorem tailTrace_124983 : CollatzResearch.WordTrace tailWord_124983 prefixEnd_124983 42784235093993158091813 := by
  unfold tailWord_124983
  simp only [CollatzResearch.WordTrace]
  refine ⟨4558504506215411242115603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3039003004143607494743735 4558504506215411242115603)
  ·
    refine ⟨6837756759323116863173405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4558504506215411242115603 6837756759323116863173405)
    ·
      refine ⟨2564158784746168823690027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6837756759323116863173405 2564158784746168823690027)
      ·
        refine ⟨3846238177119253235535041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2564158784746168823690027 3846238177119253235535041)
        ·
          refine ⟨2884678632839439926651281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3846238177119253235535041 2884678632839439926651281)
          ·
            refine ⟨2163508974629579944988461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2884678632839439926651281 2163508974629579944988461)
            ·
              refine ⟨811315865486092479370673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2163508974629579944988461 811315865486092479370673)
              ·
                refine ⟨608486899114569359528005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811315865486092479370673 608486899114569359528005)
                ·
                  refine ⟨114091293583981754911501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 608486899114569359528005 114091293583981754911501)
                  ·
                    refine ⟨42784235093993158091813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114091293583981754911501 42784235093993158091813)
                    ·
                      rfl

theorem cell22_124983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_124983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_124983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_124983 prefixEnd_124983 := by exact prefixLift 124983
  have htrace : WordTrace (prefixWord ++ tailWord_124983) baseStart_124983 baseEnd_124983 := by
    simpa [prefixWord, tailWord_124983, baseEnd_124983] using wordTrace_append hprefix tailTrace_124983
  have hstable : (prefixWord ++ tailWord_124983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124983).length < 2 ^ (prefixWord ++ tailWord_124983).sum := by decide
  have hdescent : baseEnd_124983 < baseStart_124983 := by decide
  rcases family_descends (prefixWord ++ tailWord_124983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125013 : List Nat := [1, 3, 2, 2, 1, 4, 2, 7]
def baseStart_125013 : Nat := 118140960795 + 125013 * 2 ^ 59
def prefixEnd_125013 : Nat := 4983230072969 + 3 ^ 40 * 125013 * 2
def baseEnd_125013 : Nat := 4754944967453675537969

theorem tailTrace_125013 : CollatzResearch.WordTrace tailWord_125013 prefixEnd_125013 4754944967453675537969 := by
  unfold tailWord_125013
  simp only [CollatzResearch.WordTrace]
  refine ⟨4559598696106726365707693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3039732464071150910471795 4559598696106726365707693)
  ·
    refine ⟨1709849511040022387140385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4559598696106726365707693 1709849511040022387140385)
    ·
      refine ⟨1282387133280016790355289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1709849511040022387140385 1282387133280016790355289)
      ·
        refine ⟨961790349960012592766467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1282387133280016790355289 961790349960012592766467)
        ·
          refine ⟨1442685524940018889149701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961790349960012592766467 1442685524940018889149701)
          ·
            refine ⟨270503535926253541715569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1442685524940018889149701 270503535926253541715569)
            ·
              refine ⟨202877651944690156286677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270503535926253541715569 202877651944690156286677)
              ·
                refine ⟨4754944967453675537969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 202877651944690156286677 4754944967453675537969)
                ·
                  rfl

theorem cell22_125013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 7].length) (baseStart_125013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125013 prefixEnd_125013 := by exact prefixLift 125013
  have htrace : WordTrace (prefixWord ++ tailWord_125013) baseStart_125013 baseEnd_125013 := by
    simpa [prefixWord, tailWord_125013, baseEnd_125013] using wordTrace_append hprefix tailTrace_125013
  have hstable : (prefixWord ++ tailWord_125013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125013).length < 2 ^ (prefixWord ++ tailWord_125013).sum := by decide
  have hdescent : baseEnd_125013 < baseStart_125013 := by decide
  rcases family_descends (prefixWord ++ tailWord_125013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125109 : List Nat := [1, 3, 3, 4, 1, 2, 1, 2, 5]
def baseStart_125109 : Nat := 118140960795 + 125109 * 2 ^ 59
def prefixEnd_125109 : Nat := 4983230072969 + 3 ^ 40 * 125109 * 2
def baseEnd_125109 : Nat := 14275789156323609813809

theorem tailTrace_125109 : CollatzResearch.WordTrace tailWord_125109 prefixEnd_125109 14275789156323609813809 := by
  unfold tailWord_125109
  simp only [CollatzResearch.WordTrace]
  refine ⟨4563100103758934761202381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3042066735839289840801587 4563100103758934761202381)
  ·
    refine ⟨1711162538909600535450893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4563100103758934761202381 1711162538909600535450893)
    ·
      refine ⟨641685952091100200794085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1711162538909600535450893 641685952091100200794085)
      ·
        refine ⟨120316116017081287648891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 641685952091100200794085 120316116017081287648891)
        ·
          refine ⟨180474174025621931473337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120316116017081287648891 180474174025621931473337)
          ·
            refine ⟨135355630519216448605003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180474174025621931473337 135355630519216448605003)
            ·
              refine ⟨203033445778824672907505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135355630519216448605003 203033445778824672907505)
              ·
                refine ⟨152275084334118504680629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203033445778824672907505 152275084334118504680629)
                ·
                  refine ⟨14275789156323609813809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152275084334118504680629 14275789156323609813809)
                  ·
                    rfl

theorem cell22_125109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_125109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125109 prefixEnd_125109 := by exact prefixLift 125109
  have htrace : WordTrace (prefixWord ++ tailWord_125109) baseStart_125109 baseEnd_125109 := by
    simpa [prefixWord, tailWord_125109, baseEnd_125109] using wordTrace_append hprefix tailTrace_125109
  have hstable : (prefixWord ++ tailWord_125109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125109).length < 2 ^ (prefixWord ++ tailWord_125109).sum := by decide
  have hdescent : baseEnd_125109 < baseStart_125109 := by decide
  rcases family_descends (prefixWord ++ tailWord_125109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125120 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 6]
def baseStart_125120 : Nat := 118140960795 + 125120 * 2 ^ 59
def prefixEnd_125120 : Nat := 4983230072969 + 3 ^ 40 * 125120 * 2
def baseEnd_125120 : Nat := 14277044331256822472131

theorem tailTrace_125120 : CollatzResearch.WordTrace tailWord_125120 prefixEnd_125120 14277044331256822472131 := by
  unfold tailWord_125120
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281750653359541819926407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3042334204479389093235209 2281750653359541819926407)
  ·
    refine ⟨3422625980039312729889611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2281750653359541819926407 3422625980039312729889611)
    ·
      refine ⟨5133938970058969094834417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3422625980039312729889611 5133938970058969094834417)
      ·
        refine ⟨3850454227544226821125813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5133938970058969094834417 3850454227544226821125813)
        ·
          refine ⟨360980083832271264480545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3850454227544226821125813 360980083832271264480545)
          ·
            refine ⟨270735062874203448360409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360980083832271264480545 270735062874203448360409)
            ·
              refine ⟨203051297155652586270307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270735062874203448360409 203051297155652586270307)
              ·
                refine ⟨304576945733478879405461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203051297155652586270307 304576945733478879405461)
                ·
                  refine ⟨14277044331256822472131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 304576945733478879405461 14277044331256822472131)
                  ·
                    rfl

theorem cell22_125120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 6].length) (baseStart_125120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125120 prefixEnd_125120 := by exact prefixLift 125120
  have htrace : WordTrace (prefixWord ++ tailWord_125120) baseStart_125120 baseEnd_125120 := by
    simpa [prefixWord, tailWord_125120, baseEnd_125120] using wordTrace_append hprefix tailTrace_125120
  have hstable : (prefixWord ++ tailWord_125120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125120).length < 2 ^ (prefixWord ++ tailWord_125120).sum := by decide
  have hdescent : baseEnd_125120 < baseStart_125120 := by decide
  rcases family_descends (prefixWord ++ tailWord_125120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125186 : List Nat := [3, 4, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_125186 : Nat := 118140960795 + 125186 * 2 ^ 59
def prefixEnd_125186 : Nat := 4983230072969 + 3 ^ 40 * 125186 * 2
def baseEnd_125186 : Nat := 42853726142568295266191

theorem tailTrace_125186 : CollatzResearch.WordTrace tailWord_125186 prefixEnd_125186 42853726142568295266191 := by
  unfold tailWord_125186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1141477131119994227938853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3043939016319984607836941 1141477131119994227938853)
  ·
    refine ⟨214026962084998917738535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1141477131119994227938853 214026962084998917738535)
    ·
      refine ⟨321040443127498376607803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214026962084998917738535 321040443127498376607803)
      ·
        refine ⟨481560664691247564911705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321040443127498376607803 481560664691247564911705)
        ·
          refine ⟨361170498518435673683779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481560664691247564911705 361170498518435673683779)
          ·
            refine ⟨541755747777653510525669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361170498518435673683779 541755747777653510525669)
            ·
              refine ⟨101579202708310033223563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 541755747777653510525669 101579202708310033223563)
              ·
                refine ⟨152368804062465049835345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101579202708310033223563 152368804062465049835345)
                ·
                  refine ⟨114276603046848787376509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152368804062465049835345 114276603046848787376509)
                  ·
                    refine ⟨42853726142568295266191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114276603046848787376509 42853726142568295266191)
                    ·
                      rfl

theorem cell22_125186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_125186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125186 prefixEnd_125186 := by exact prefixLift 125186
  have htrace : WordTrace (prefixWord ++ tailWord_125186) baseStart_125186 baseEnd_125186 := by
    simpa [prefixWord, tailWord_125186, baseEnd_125186] using wordTrace_append hprefix tailTrace_125186
  have hstable : (prefixWord ++ tailWord_125186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125186).length < 2 ^ (prefixWord ++ tailWord_125186).sum := by decide
  have hdescent : baseEnd_125186 < baseStart_125186 := by decide
  rcases family_descends (prefixWord ++ tailWord_125186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125240 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 3, 4]
def baseStart_125240 : Nat := 118140960795 + 125240 * 2 ^ 59
def prefixEnd_125240 : Nat := 4983230072969 + 3 ^ 40 * 125240 * 2
def baseEnd_125240 : Nat := 42872211446130154416025

theorem tailTrace_125240 : CollatzResearch.WordTrace tailWord_125240 prefixEnd_125240 42872211446130154416025 := by
  unfold tailWord_125240
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283939033142172067110587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3045252044189562756147449 2283939033142172067110587)
  ·
    refine ⟨3425908549713258100665881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2283939033142172067110587 3425908549713258100665881)
    ·
      refine ⟨2569431412284943575499411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3425908549713258100665881 2569431412284943575499411)
      ·
        refine ⟨3854147118427415363249117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2569431412284943575499411 3854147118427415363249117)
        ·
          refine ⟨1445305169410280761218419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3854147118427415363249117 1445305169410280761218419)
          ·
            refine ⟨2167957754115421141827629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445305169410280761218419 2167957754115421141827629)
            ·
              refine ⟨812984157793282928185361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2167957754115421141827629 812984157793282928185361)
              ·
                refine ⟨609738118344962196139021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812984157793282928185361 609738118344962196139021)
                ·
                  refine ⟨228651794379360823552133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609738118344962196139021 228651794379360823552133)
                  ·
                    refine ⟨42872211446130154416025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 228651794379360823552133 42872211446130154416025)
                    ·
                      rfl

theorem cell22_125240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_125240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125240 prefixEnd_125240 := by exact prefixLift 125240
  have htrace : WordTrace (prefixWord ++ tailWord_125240) baseStart_125240 baseEnd_125240 := by
    simpa [prefixWord, tailWord_125240, baseEnd_125240] using wordTrace_append hprefix tailTrace_125240
  have hstable : (prefixWord ++ tailWord_125240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125240).length < 2 ^ (prefixWord ++ tailWord_125240).sum := by decide
  have hdescent : baseEnd_125240 < baseStart_125240 := by decide
  rcases family_descends (prefixWord ++ tailWord_125240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125255 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 6]
def baseStart_125255 : Nat := 118140960795 + 125255 * 2 ^ 59
def prefixEnd_125255 : Nat := 4983230072969 + 3 ^ 40 * 125255 * 2
def baseEnd_125255 : Nat := 14292448750891705096993

theorem tailTrace_125255 : CollatzResearch.WordTrace tailWord_125255 prefixEnd_125255 14292448750891705096993 := by
  unfold tailWord_125255
  simp only [CollatzResearch.WordTrace]
  refine ⟨4568425161230001696017219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3045616774153334464011479 4568425161230001696017219)
  ·
    refine ⟨6852637741845002544025829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4568425161230001696017219 6852637741845002544025829)
    ·
      refine ⟨1284869576595937977004843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6852637741845002544025829 1284869576595937977004843)
      ·
        refine ⟨1927304364893906965507265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284869576595937977004843 1927304364893906965507265)
        ·
          refine ⟨1445478273670430224130449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1927304364893906965507265 1445478273670430224130449)
          ·
            refine ⟨1084108705252822668097837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1445478273670430224130449 1084108705252822668097837)
            ·
              refine ⟨406540764469808500536689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1084108705252822668097837 406540764469808500536689)
              ·
                refine ⟨304905573352356375402517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406540764469808500536689 304905573352356375402517)
                ·
                  refine ⟨14292448750891705096993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 304905573352356375402517 14292448750891705096993)
                  ·
                    rfl

theorem cell22_125255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 6].length) (baseStart_125255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125255 prefixEnd_125255 := by exact prefixLift 125255
  have htrace : WordTrace (prefixWord ++ tailWord_125255) baseStart_125255 baseEnd_125255 := by
    simpa [prefixWord, tailWord_125255, baseEnd_125255] using wordTrace_append hprefix tailTrace_125255
  have hstable : (prefixWord ++ tailWord_125255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125255).length < 2 ^ (prefixWord ++ tailWord_125255).sum := by decide
  have hdescent : baseEnd_125255 < baseStart_125255 := by decide
  rcases family_descends (prefixWord ++ tailWord_125255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125278 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_125278 : Nat := 118140960795 + 125278 * 2 ^ 59
def prefixEnd_125278 : Nat := 4983230072969 + 3 ^ 40 * 125278 * 2
def baseEnd_125278 : Nat := 14295073207570240655303

theorem tailTrace_125278 : CollatzResearch.WordTrace tailWord_125278 prefixEnd_125278 14295073207570240655303 := by
  unfold tailWord_125278
  simp only [CollatzResearch.WordTrace]
  refine ⟨571158005018334578013061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3046176026764451082736325 571158005018334578013061)
  ·
    refine ⟨107092125940937733377449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 571158005018334578013061 107092125940937733377449)
    ·
      refine ⟨80319094455703300033087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107092125940937733377449 80319094455703300033087)
      ·
        refine ⟨120478641683554950049631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80319094455703300033087 120478641683554950049631)
        ·
          refine ⟨180717962525332425074447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120478641683554950049631 180717962525332425074447)
          ·
            refine ⟨271076943787998637611671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180717962525332425074447 271076943787998637611671)
            ·
              refine ⟨406615415681997956417507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271076943787998637611671 406615415681997956417507)
              ·
                refine ⟨609923123522996934626261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406615415681997956417507 609923123522996934626261)
                ·
                  refine ⟨14295073207570240655303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 609923123522996934626261 14295073207570240655303)
                  ·
                    rfl

theorem cell22_125278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_125278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125278 prefixEnd_125278 := by exact prefixLift 125278
  have htrace : WordTrace (prefixWord ++ tailWord_125278) baseStart_125278 baseEnd_125278 := by
    simpa [prefixWord, tailWord_125278, baseEnd_125278] using wordTrace_append hprefix tailTrace_125278
  have hstable : (prefixWord ++ tailWord_125278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125278).length < 2 ^ (prefixWord ++ tailWord_125278).sum := by decide
  have hdescent : baseEnd_125278 < baseStart_125278 := by decide
  rcases family_descends (prefixWord ++ tailWord_125278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125360 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 6, 5]
def baseStart_125360 : Nat := 118140960795 + 125360 * 2 ^ 59
def prefixEnd_125360 : Nat := 4983230072969 + 3 ^ 40 * 125360 * 2
def baseEnd_125360 : Nat := 42913289898489841415657

theorem tailTrace_125360 : CollatzResearch.WordTrace tailWord_125360 prefixEnd_125360 42913289898489841415657 := by
  unfold tailWord_125360
  simp only [CollatzResearch.WordTrace]
  refine ⟨2286127412924802314294767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3048169883899736419059689 2286127412924802314294767)
  ·
    refine ⟨3429191119387203471442151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2286127412924802314294767 3429191119387203471442151)
    ·
      refine ⟨5143786679080805207163227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3429191119387203471442151 5143786679080805207163227)
      ·
        refine ⟨7715680018621207810744841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5143786679080805207163227 7715680018621207810744841)
        ·
          refine ⟨5786760013965905858058631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7715680018621207810744841 5786760013965905858058631)
          ·
            refine ⟨8680140020948858787087947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5786760013965905858058631 8680140020948858787087947)
            ·
              refine ⟨13020210031423288180631921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8680140020948858787087947 13020210031423288180631921)
              ·
                refine ⟨9765157523567466135473941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13020210031423288180631921 9765157523567466135473941)
                ·
                  refine ⟨457741758917224975100341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9765157523567466135473941 457741758917224975100341)
                  ·
                    refine ⟨42913289898489841415657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 457741758917224975100341 42913289898489841415657)
                    ·
                      rfl

theorem cell22_125360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_125360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125360 prefixEnd_125360 := by exact prefixLift 125360
  have htrace : WordTrace (prefixWord ++ tailWord_125360) baseStart_125360 baseEnd_125360 := by
    simpa [prefixWord, tailWord_125360, baseEnd_125360] using wordTrace_append hprefix tailTrace_125360
  have hstable : (prefixWord ++ tailWord_125360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125360).length < 2 ^ (prefixWord ++ tailWord_125360).sum := by decide
  have hdescent : baseEnd_125360 < baseStart_125360 := by decide
  rcases family_descends (prefixWord ++ tailWord_125360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125362 : List Nat := [3, 2, 1, 1, 1, 1, 5, 3, 5]
def baseStart_125362 : Nat := 118140960795 + 125362 * 2 ^ 59
def prefixEnd_125362 : Nat := 4983230072969 + 3 ^ 40 * 125362 * 2
def baseEnd_125362 : Nat := 14304658179787500955217

theorem tailTrace_125362 : CollatzResearch.WordTrace tailWord_125362 prefixEnd_125362 14304658179787500955217 := by
  unfold tailWord_125362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1143081942960589742540585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3048218514561572646774893 1143081942960589742540585)
  ·
    refine ⟨857311457220442306905439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1143081942960589742540585 857311457220442306905439)
    ·
      refine ⟨1285967185830663460358159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 857311457220442306905439 1285967185830663460358159)
      ·
        refine ⟨1928950778745995190537239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285967185830663460358159 1928950778745995190537239)
        ·
          refine ⟨2893426168118992785805859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1928950778745995190537239 2893426168118992785805859)
          ·
            refine ⟨4340139252178489178708789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2893426168118992785805859 4340139252178489178708789)
            ·
              refine ⟨406888054891733360503949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4340139252178489178708789 406888054891733360503949)
              ·
                refine ⟨152583020584400010188981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406888054891733360503949 152583020584400010188981)
                ·
                  refine ⟨14304658179787500955217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152583020584400010188981 14304658179787500955217)
                  ·
                    rfl

theorem cell22_125362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_125362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125362 prefixEnd_125362 := by exact prefixLift 125362
  have htrace : WordTrace (prefixWord ++ tailWord_125362) baseStart_125362 baseEnd_125362 := by
    simpa [prefixWord, tailWord_125362, baseEnd_125362] using wordTrace_append hprefix tailTrace_125362
  have hstable : (prefixWord ++ tailWord_125362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125362).length < 2 ^ (prefixWord ++ tailWord_125362).sum := by decide
  have hdescent : baseEnd_125362 < baseStart_125362 := by decide
  rcases family_descends (prefixWord ++ tailWord_125362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125437 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_125437 : Nat := 118140960795 + 125437 * 2 ^ 59
def prefixEnd_125437 : Nat := 4983230072969 + 3 ^ 40 * 125437 * 2
def baseEnd_125437 : Nat := 42939648572087307240421

theorem tailTrace_125437 : CollatzResearch.WordTrace tailWord_125437 prefixEnd_125437 42939648572087307240421 := by
  unfold tailWord_125437
  simp only [CollatzResearch.WordTrace]
  refine ⟨4575063246570646779142565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3050042164380431186095043 4575063246570646779142565)
  ·
    refine ⟨857824358731996271089231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4575063246570646779142565 857824358731996271089231)
    ·
      refine ⟨1286736538097994406633847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 857824358731996271089231 1286736538097994406633847)
      ·
        refine ⟨1930104807146991609950771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286736538097994406633847 1930104807146991609950771)
        ·
          refine ⟨2895157210720487414926157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1930104807146991609950771 2895157210720487414926157)
          ·
            refine ⟨1085683954020182780597309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2895157210720487414926157 1085683954020182780597309)
            ·
              refine ⟨407131482757568542723991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1085683954020182780597309 407131482757568542723991)
              ·
                refine ⟨610697224136352814085987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407131482757568542723991 610697224136352814085987)
                ·
                  refine ⟨916045836204529221128981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610697224136352814085987 916045836204529221128981)
                  ·
                    refine ⟨42939648572087307240421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 916045836204529221128981 42939648572087307240421)
                    ·
                      rfl

theorem cell22_125437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_125437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125437 prefixEnd_125437 := by exact prefixLift 125437
  have htrace : WordTrace (prefixWord ++ tailWord_125437) baseStart_125437 baseEnd_125437 := by
    simpa [prefixWord, tailWord_125437, baseEnd_125437] using wordTrace_append hprefix tailTrace_125437
  have hstable : (prefixWord ++ tailWord_125437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125437).length < 2 ^ (prefixWord ++ tailWord_125437).sum := by decide
  have hdescent : baseEnd_125437 < baseStart_125437 := by decide
  rcases family_descends (prefixWord ++ tailWord_125437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125441 : List Nat := [1, 2, 4, 1, 3, 2, 2, 3, 4]
def baseStart_125441 : Nat := 118140960795 + 125441 * 2 ^ 59
def prefixEnd_125441 : Nat := 4983230072969 + 3 ^ 40 * 125441 * 2
def baseEnd_125441 : Nat := 14313672617944210046803

theorem tailTrace_125441 : CollatzResearch.WordTrace tailWord_125441 prefixEnd_125441 14313672617944210046803 := by
  unfold tailWord_125441
  simp only [CollatzResearch.WordTrace]
  refine ⟨4575209138556155462288177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3050139425704103641525451 4575209138556155462288177)
  ·
    refine ⟨3431406853917116596716133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4575209138556155462288177 3431406853917116596716133)
    ·
      refine ⟨643388785109459361884275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3431406853917116596716133 643388785109459361884275)
      ·
        refine ⟨965083177664189042826413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643388785109459361884275 965083177664189042826413)
        ·
          refine ⟨361906191624070891059905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 965083177664189042826413 361906191624070891059905)
          ·
            refine ⟨271429643718053168294929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361906191624070891059905 271429643718053168294929)
            ·
              refine ⟨203572232788539876221197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271429643718053168294929 203572232788539876221197)
              ·
                refine ⟨76339587295702453582949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203572232788539876221197 76339587295702453582949)
                ·
                  refine ⟨14313672617944210046803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76339587295702453582949 14313672617944210046803)
                  ·
                    rfl

theorem cell22_125441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 4].length) (baseStart_125441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125441 prefixEnd_125441 := by exact prefixLift 125441
  have htrace : WordTrace (prefixWord ++ tailWord_125441) baseStart_125441 baseEnd_125441 := by
    simpa [prefixWord, tailWord_125441, baseEnd_125441] using wordTrace_append hprefix tailTrace_125441
  have hstable : (prefixWord ++ tailWord_125441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125441).length < 2 ^ (prefixWord ++ tailWord_125441).sum := by decide
  have hdescent : baseEnd_125441 < baseStart_125441 := by decide
  rcases family_descends (prefixWord ++ tailWord_125441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125452 : List Nat := [2, 2, 1, 2, 4, 2, 9]
def baseStart_125452 : Nat := 118140960795 + 125452 * 2 ^ 59
def prefixEnd_125452 : Nat := 4983230072969 + 3 ^ 40 * 125452 * 2
def baseEnd_125452 : Nat := 1590547532541935856125

theorem tailTrace_125452 : CollatzResearch.WordTrace tailWord_125452 prefixEnd_125452 1590547532541935856125 := by
  unfold tailWord_125452
  simp only [CollatzResearch.WordTrace]
  refine ⟨2287805170758152170469305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3050406894344202893959073 2287805170758152170469305)
  ·
    refine ⟨1715853878068614127851979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2287805170758152170469305 1715853878068614127851979)
    ·
      refine ⟨2573780817102921191777969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1715853878068614127851979 2573780817102921191777969)
      ·
        refine ⟨1930335612827190893833477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2573780817102921191777969 1930335612827190893833477)
        ·
          refine ⟨361937927405098292593777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1930335612827190893833477 361937927405098292593777)
          ·
            refine ⟨271453445553823719445333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361937927405098292593777 271453445553823719445333)
            ·
              refine ⟨1590547532541935856125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 271453445553823719445333 1590547532541935856125)
              ·
                rfl

theorem cell22_125452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 9].length) (baseStart_125452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125452 prefixEnd_125452 := by exact prefixLift 125452
  have htrace : WordTrace (prefixWord ++ tailWord_125452) baseStart_125452 baseEnd_125452 := by
    simpa [prefixWord, tailWord_125452, baseEnd_125452] using wordTrace_append hprefix tailTrace_125452
  have hstable : (prefixWord ++ tailWord_125452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125452).length < 2 ^ (prefixWord ++ tailWord_125452).sum := by decide
  have hdescent : baseEnd_125452 < baseStart_125452 := by decide
  rcases family_descends (prefixWord ++ tailWord_125452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125492 : List Nat := [2, 5, 1, 3, 2, 1, 1, 3, 4]
def baseStart_125492 : Nat := 118140960795 + 125492 * 2 ^ 59
def prefixEnd_125492 : Nat := 4983230072969 + 3 ^ 40 * 125492 * 2
def baseEnd_125492 : Nat := 14319492065361832371751

theorem tailTrace_125492 : CollatzResearch.WordTrace tailWord_125492 prefixEnd_125492 14319492065361832371751 := by
  unfold tailWord_125492
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288534630685695586197365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3051379507580927448263153 2288534630685695586197365)
  ·
    refine ⟨214550121626783961206003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2288534630685695586197365 214550121626783961206003)
    ·
      refine ⟨321825182440175941809005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214550121626783961206003 321825182440175941809005)
      ·
        refine ⟨120684443415065978178377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321825182440175941809005 120684443415065978178377)
        ·
          refine ⟨90513332561299483633783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120684443415065978178377 90513332561299483633783)
          ·
            refine ⟨135769998841949225450675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90513332561299483633783 135769998841949225450675)
            ·
              refine ⟨203654998262923838176013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135769998841949225450675 203654998262923838176013)
              ·
                refine ⟨76370624348596439316005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203654998262923838176013 76370624348596439316005)
                ·
                  refine ⟨14319492065361832371751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76370624348596439316005 14319492065361832371751)
                  ·
                    rfl

theorem cell22_125492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_125492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125492 prefixEnd_125492 := by exact prefixLift 125492
  have htrace : WordTrace (prefixWord ++ tailWord_125492) baseStart_125492 baseEnd_125492 := by
    simpa [prefixWord, tailWord_125492, baseEnd_125492] using wordTrace_append hprefix tailTrace_125492
  have hstable : (prefixWord ++ tailWord_125492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125492).length < 2 ^ (prefixWord ++ tailWord_125492).sum := by decide
  have hdescent : baseEnd_125492 < baseStart_125492 := by decide
  rcases family_descends (prefixWord ++ tailWord_125492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125497 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 9]
def baseStart_125497 : Nat := 118140960795 + 125497 * 2 ^ 59
def prefixEnd_125497 : Nat := 4983230072969 + 3 ^ 40 * 125497 * 2
def baseEnd_125497 : Nat := 14320062599422383580079

theorem tailTrace_125497 : CollatzResearch.WordTrace tailWord_125497 prefixEnd_125497 14320062599422383580079 := by
  unfold tailWord_125497
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577251626353277026326745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3051501084235518017551163 4577251626353277026326745)
  ·
    refine ⟨3432938719764957769745059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4577251626353277026326745 3432938719764957769745059)
    ·
      refine ⟨5149408079647436654617589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3432938719764957769745059 5149408079647436654617589)
      ·
        refine ⟨482757007466947186370399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5149408079647436654617589 482757007466947186370399)
        ·
          refine ⟨724135511200420779555599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482757007466947186370399 724135511200420779555599)
          ·
            refine ⟨1086203266800631169333399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724135511200420779555599 1086203266800631169333399)
            ·
              refine ⟨1629304900200946754000099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086203266800631169333399 1629304900200946754000099)
              ·
                refine ⟨2443957350301420131000149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629304900200946754000099 2443957350301420131000149)
                ·
                  refine ⟨14320062599422383580079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2443957350301420131000149 14320062599422383580079)
                  ·
                    rfl

theorem cell22_125497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_125497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125497 prefixEnd_125497 := by exact prefixLift 125497
  have htrace : WordTrace (prefixWord ++ tailWord_125497) baseStart_125497 baseEnd_125497 := by
    simpa [prefixWord, tailWord_125497, baseEnd_125497] using wordTrace_append hprefix tailTrace_125497
  have hstable : (prefixWord ++ tailWord_125497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125497).length < 2 ^ (prefixWord ++ tailWord_125497).sum := by decide
  have hdescent : baseEnd_125497 < baseStart_125497 := by decide
  rcases family_descends (prefixWord ++ tailWord_125497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125512 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 4, 5]
def baseStart_125512 : Nat := 118140960795 + 125512 * 2 ^ 59
def prefixEnd_125512 : Nat := 4983230072969 + 3 ^ 40 * 125512 * 2
def baseEnd_125512 : Nat := 42965322604812111615191

theorem tailTrace_125512 : CollatzResearch.WordTrace tailWord_125512 prefixEnd_125512 42965322604812111615191 := by
  unfold tailWord_125512
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288899360649467294061395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3051865814199289725415193 2288899360649467294061395)
  ·
    refine ⟨3433349040974200941092093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2288899360649467294061395 3433349040974200941092093)
    ·
      refine ⟨1287505890365325352909535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3433349040974200941092093 1287505890365325352909535)
      ·
        refine ⟨1931258835547988029364303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287505890365325352909535 1931258835547988029364303)
        ·
          refine ⟨2896888253321982044046455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1931258835547988029364303 2896888253321982044046455)
          ·
            refine ⟨4345332379982973066069683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896888253321982044046455 4345332379982973066069683)
            ·
              refine ⟨6517998569974459599104525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4345332379982973066069683 6517998569974459599104525)
              ·
                refine ⟨2444249463740422349664197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6517998569974459599104525 2444249463740422349664197)
                ·
                  refine ⟨458296774451329190562037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2444249463740422349664197 458296774451329190562037)
                  ·
                    refine ⟨42965322604812111615191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 458296774451329190562037 42965322604812111615191)
                    ·
                      rfl

theorem cell22_125512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_125512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125512 prefixEnd_125512 := by exact prefixLift 125512
  have htrace : WordTrace (prefixWord ++ tailWord_125512) baseStart_125512 baseEnd_125512 := by
    simpa [prefixWord, tailWord_125512, baseEnd_125512] using wordTrace_append hprefix tailTrace_125512
  have hstable : (prefixWord ++ tailWord_125512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125512).length < 2 ^ (prefixWord ++ tailWord_125512).sum := by decide
  have hdescent : baseEnd_125512 < baseStart_125512 := by decide
  rcases family_descends (prefixWord ++ tailWord_125512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125591 : List Nat := [1, 1, 3, 3, 2, 1, 1, 5, 2, 3]
def baseStart_125591 : Nat := 118140960795 + 125591 * 2 ^ 59
def prefixEnd_125591 : Nat := 4983230072969 + 3 ^ 40 * 125591 * 2
def baseEnd_125591 : Nat := 42992365919282238889949

theorem tailTrace_125591 : CollatzResearch.WordTrace tailWord_125591 prefixEnd_125591 42992365919282238889949 := by
  unfold tailWord_125591
  simp only [CollatzResearch.WordTrace]
  refine ⟨4580680088012731080248627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3053786725341820720165751 4580680088012731080248627)
  ·
    refine ⟨6871020132019096620372941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4580680088012731080248627 6871020132019096620372941)
    ·
      refine ⟨2576632549507161232639853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6871020132019096620372941 2576632549507161232639853)
      ·
        refine ⟨966237206065185462239945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2576632549507161232639853 966237206065185462239945)
        ·
          refine ⟨724677904548889096679959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 966237206065185462239945 724677904548889096679959)
          ·
            refine ⟨1087016856823333645019939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724677904548889096679959 1087016856823333645019939)
            ·
              refine ⟨1630525285235000467529909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087016856823333645019939 1630525285235000467529909)
              ·
                refine ⟨152861745490781293830929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1630525285235000467529909 152861745490781293830929)
                ·
                  refine ⟨114646309118085970373197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152861745490781293830929 114646309118085970373197)
                  ·
                    refine ⟨42992365919282238889949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114646309118085970373197 42992365919282238889949)
                    ·
                      rfl

theorem cell22_125591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_125591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125591 prefixEnd_125591 := by exact prefixLift 125591
  have htrace : WordTrace (prefixWord ++ tailWord_125591) baseStart_125591 baseEnd_125591 := by
    simpa [prefixWord, tailWord_125591, baseEnd_125591] using wordTrace_append hprefix tailTrace_125591
  have hstable : (prefixWord ++ tailWord_125591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125591).length < 2 ^ (prefixWord ++ tailWord_125591).sum := by decide
  have hdescent : baseEnd_125591 < baseStart_125591 := by decide
  rcases family_descends (prefixWord ++ tailWord_125591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125730 : List Nat := [3, 3, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_125730 : Nat := 118140960795 + 125730 * 2 ^ 59
def prefixEnd_125730 : Nat := 4983230072969 + 3 ^ 40 * 125730 * 2
def baseEnd_125730 : Nat := 43039948459932209664523

theorem tailTrace_125730 : CollatzResearch.WordTrace tailWord_125730 prefixEnd_125730 43039948459932209664523 := by
  unfold tailWord_125730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146437458627289454889661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3057166556339438546372429 1146437458627289454889661)
  ·
    refine ⟨429914046985233545583623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1146437458627289454889661 429914046985233545583623)
    ·
      refine ⟨644871070477850318375435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429914046985233545583623 644871070477850318375435)
      ·
        refine ⟨967306605716775477563153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644871070477850318375435 967306605716775477563153)
        ·
          refine ⟨725479954287581608172365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 967306605716775477563153 725479954287581608172365)
          ·
            refine ⟨272054982857843103064637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 725479954287581608172365 272054982857843103064637)
            ·
              refine ⟨102020618571691163649239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272054982857843103064637 102020618571691163649239)
              ·
                refine ⟨153030927857536745473859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102020618571691163649239 153030927857536745473859)
                ·
                  refine ⟨229546391786305118210789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153030927857536745473859 229546391786305118210789)
                  ·
                    refine ⟨43039948459932209664523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 229546391786305118210789 43039948459932209664523)
                    ·
                      rfl

theorem cell22_125730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_125730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125730 prefixEnd_125730 := by exact prefixLift 125730
  have htrace : WordTrace (prefixWord ++ tailWord_125730) baseStart_125730 baseEnd_125730 := by
    simpa [prefixWord, tailWord_125730, baseEnd_125730] using wordTrace_append hprefix tailTrace_125730
  have hstable : (prefixWord ++ tailWord_125730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125730).length < 2 ^ (prefixWord ++ tailWord_125730).sum := by decide
  have hdescent : baseEnd_125730 < baseStart_125730 := by decide
  rcases family_descends (prefixWord ++ tailWord_125730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125794 : List Nat := [3, 3, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_125794 : Nat := 118140960795 + 125794 * 2 ^ 59
def prefixEnd_125794 : Nat := 4983230072969 + 3 ^ 40 * 125794 * 2
def baseEnd_125794 : Nat := 43061856967857376064327

theorem tailTrace_125794 : CollatzResearch.WordTrace tailWord_125794 prefixEnd_125794 43061856967857376064327 := by
  unfold tailWord_125794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1147021026569324187472109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3058722737518197833258957 1147021026569324187472109)
  ·
    refine ⟨430132884963496570302041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1147021026569324187472109 430132884963496570302041)
    ·
      refine ⟨322599663722622427726531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430132884963496570302041 322599663722622427726531)
      ·
        refine ⟨483899495583933641589797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322599663722622427726531 483899495583933641589797)
        ·
          refine ⟨90731155421987557798087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 483899495583933641589797 90731155421987557798087)
          ·
            refine ⟨136096733132981336697131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90731155421987557798087 136096733132981336697131)
            ·
              refine ⟨204145099699472005045697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136096733132981336697131 204145099699472005045697)
              ·
                refine ⟨153108824774604003784273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204145099699472005045697 153108824774604003784273)
                ·
                  refine ⟨114831618580953002838205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153108824774604003784273 114831618580953002838205)
                  ·
                    refine ⟨43061856967857376064327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114831618580953002838205 43061856967857376064327)
                    ·
                      rfl

theorem cell22_125794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_125794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125794 prefixEnd_125794 := by exact prefixLift 125794
  have htrace : WordTrace (prefixWord ++ tailWord_125794) baseStart_125794 baseEnd_125794 := by
    simpa [prefixWord, tailWord_125794, baseEnd_125794] using wordTrace_append hprefix tailTrace_125794
  have hstable : (prefixWord ++ tailWord_125794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125794).length < 2 ^ (prefixWord ++ tailWord_125794).sum := by decide
  have hdescent : baseEnd_125794 < baseStart_125794 := by decide
  rcases family_descends (prefixWord ++ tailWord_125794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125869 : List Nat := [1, 5, 2, 3, 1, 2, 2, 1, 5]
def baseStart_125869 : Nat := 118140960795 + 125869 * 2 ^ 59
def prefixEnd_125869 : Nat := 4983230072969 + 3 ^ 40 * 125869 * 2
def baseEnd_125869 : Nat := 14362510333527393479699

theorem tailTrace_125869 : CollatzResearch.WordTrace tailWord_125869 prefixEnd_125869 14362510333527393479699 := by
  unfold tailWord_125869
  simp only [CollatzResearch.WordTrace]
  refine ⟨4590819581005584558868661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3060546387337056372579107 4590819581005584558868661)
  ·
    refine ⟨430389335719273552393937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4590819581005584558868661 430389335719273552393937)
    ·
      refine ⟨322792001789455164295453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430389335719273552393937 322792001789455164295453)
      ·
        refine ⟨121047000671045686610795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322792001789455164295453 121047000671045686610795)
        ·
          refine ⟨181570501006568529916193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121047000671045686610795 181570501006568529916193)
          ·
            refine ⟨136177875754926397437145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181570501006568529916193 136177875754926397437145)
            ·
              refine ⟨102133406816194798077859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136177875754926397437145 102133406816194798077859)
              ·
                refine ⟨153200110224292197116789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102133406816194798077859 153200110224292197116789)
                ·
                  refine ⟨14362510333527393479699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153200110224292197116789 14362510333527393479699)
                  ·
                    rfl

theorem cell22_125869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_125869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125869 prefixEnd_125869 := by exact prefixLift 125869
  have htrace : WordTrace (prefixWord ++ tailWord_125869) baseStart_125869 baseEnd_125869 := by
    simpa [prefixWord, tailWord_125869, baseEnd_125869] using wordTrace_append hprefix tailTrace_125869
  have hstable : (prefixWord ++ tailWord_125869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125869).length < 2 ^ (prefixWord ++ tailWord_125869).sum := by decide
  have hdescent : baseEnd_125869 < baseStart_125869 := by decide
  rcases family_descends (prefixWord ++ tailWord_125869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125936 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 9]
def baseStart_125936 : Nat := 118140960795 + 125936 * 2 ^ 59
def prefixEnd_125936 : Nat := 4983230072969 + 3 ^ 40 * 125936 * 2
def baseEnd_125936 : Nat := 14370155489938779671297

theorem tailTrace_125936 : CollatzResearch.WordTrace tailWord_125936 prefixEnd_125936 14370155489938779671297 := by
  unfold tailWord_125936
  simp only [CollatzResearch.WordTrace]
  refine ⟨2296631635881427500778831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3062175514508570001038441 2296631635881427500778831)
  ·
    refine ⟨3444947453822141251168247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2296631635881427500778831 3444947453822141251168247)
    ·
      refine ⟨5167421180733211876752371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3444947453822141251168247 5167421180733211876752371)
      ·
        refine ⟨7751131771099817815128557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5167421180733211876752371 7751131771099817815128557)
        ·
          refine ⟨2906674414162431680673209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7751131771099817815128557 2906674414162431680673209)
          ·
            refine ⟨2180005810621823760504907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2906674414162431680673209 2180005810621823760504907)
            ·
              refine ⟨3270008715932735640757361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180005810621823760504907 3270008715932735640757361)
              ·
                refine ⟨2452506536949551730568021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3270008715932735640757361 2452506536949551730568021)
                ·
                  refine ⟨14370155489938779671297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2452506536949551730568021 14370155489938779671297)
                  ·
                    rfl

theorem cell22_125936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_125936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125936 prefixEnd_125936 := by exact prefixLift 125936
  have htrace : WordTrace (prefixWord ++ tailWord_125936) baseStart_125936 baseEnd_125936 := by
    simpa [prefixWord, tailWord_125936, baseEnd_125936] using wordTrace_append hprefix tailTrace_125936
  have hstable : (prefixWord ++ tailWord_125936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125936).length < 2 ^ (prefixWord ++ tailWord_125936).sum := by decide
  have hdescent : baseEnd_125936 < baseStart_125936 := by decide
  rcases family_descends (prefixWord ++ tailWord_125936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125957 : List Nat := [1, 3, 1, 1, 2, 3, 4, 3, 1, 3]
def baseStart_125957 : Nat := 118140960795 + 125957 * 2 ^ 59
def prefixEnd_125957 : Nat := 4983230072969 + 3 ^ 40 * 125957 * 2
def baseEnd_125957 : Nat := 43117655198979284238827

theorem tailTrace_125957 : CollatzResearch.WordTrace tailWord_125957 prefixEnd_125957 43117655198979284238827 := by
  unfold tailWord_125957
  simp only [CollatzResearch.WordTrace]
  refine ⟨4594029204686775588072125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3062686136457850392048083 4594029204686775588072125)
  ·
    refine ⟨1722760951757540845527047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4594029204686775588072125 1722760951757540845527047)
    ·
      refine ⟨2584141427636311268290571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1722760951757540845527047 2584141427636311268290571)
      ·
        refine ⟨3876212141454466902435857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2584141427636311268290571 3876212141454466902435857)
        ·
          refine ⟨2907159106090850176826893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3876212141454466902435857 2907159106090850176826893)
          ·
            refine ⟨1090184664784068816310085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2907159106090850176826893 1090184664784068816310085)
            ·
              refine ⟨204409624647012903058141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1090184664784068816310085 204409624647012903058141)
              ·
                refine ⟨76653609242629838646803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204409624647012903058141 76653609242629838646803)
                ·
                  refine ⟨114980413863944757970205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76653609242629838646803 114980413863944757970205)
                  ·
                    refine ⟨43117655198979284238827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114980413863944757970205 43117655198979284238827)
                    ·
                      rfl

theorem cell22_125957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_125957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_125957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_125957 prefixEnd_125957 := by exact prefixLift 125957
  have htrace : WordTrace (prefixWord ++ tailWord_125957) baseStart_125957 baseEnd_125957 := by
    simpa [prefixWord, tailWord_125957, baseEnd_125957] using wordTrace_append hprefix tailTrace_125957
  have hstable : (prefixWord ++ tailWord_125957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125957).length < 2 ^ (prefixWord ++ tailWord_125957).sum := by decide
  have hdescent : baseEnd_125957 < baseStart_125957 := by decide
  rcases family_descends (prefixWord ++ tailWord_125957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126000 : List Nat := [2, 1, 1, 1, 2, 4, 4, 2, 1, 4]
def baseStart_126000 : Nat := 118140960795 + 126000 * 2 ^ 59
def prefixEnd_126000 : Nat := 4983230072969 + 3 ^ 40 * 126000 * 2
def baseEnd_126000 : Nat := 43132374977741505413695

theorem tailTrace_126000 : CollatzResearch.WordTrace tailWord_126000 prefixEnd_126000 43132374977741505413695 := by
  unfold tailWord_126000
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297798771765496965943727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3063731695687329287924969 2297798771765496965943727)
  ·
    refine ⟨3446698157648245448915591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2297798771765496965943727 3446698157648245448915591)
    ·
      refine ⟨5170047236472368173373387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3446698157648245448915591 5170047236472368173373387)
      ·
        refine ⟨7755070854708552260060081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5170047236472368173373387 7755070854708552260060081)
        ·
          refine ⟨5816303141031414195045061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7755070854708552260060081 5816303141031414195045061)
          ·
            refine ⟨1090556838943390161570949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5816303141031414195045061 1090556838943390161570949)
            ·
              refine ⟨204479407301885655294553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1090556838943390161570949 204479407301885655294553)
              ·
                refine ⟨153359555476414241470915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204479407301885655294553 153359555476414241470915)
                ·
                  refine ⟨230039333214621362206373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153359555476414241470915 230039333214621362206373)
                  ·
                    refine ⟨43132374977741505413695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 230039333214621362206373 43132374977741505413695)
                    ·
                      rfl

theorem cell22_126000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_126000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126000 prefixEnd_126000 := by exact prefixLift 126000
  have htrace : WordTrace (prefixWord ++ tailWord_126000) baseStart_126000 baseEnd_126000 := by
    simpa [prefixWord, tailWord_126000, baseEnd_126000] using wordTrace_append hprefix tailTrace_126000
  have hstable : (prefixWord ++ tailWord_126000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126000).length < 2 ^ (prefixWord ++ tailWord_126000).sum := by decide
  have hdescent : baseEnd_126000 < baseStart_126000 := by decide
  rcases family_descends (prefixWord ++ tailWord_126000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126030 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_126030 : Nat := 118140960795 + 126030 * 2 ^ 59
def prefixEnd_126030 : Nat := 4983230072969 + 3 ^ 40 * 126030 * 2
def baseEnd_126030 : Nat := 43142644590831427163603

theorem tailTrace_126030 : CollatzResearch.WordTrace tailWord_126030 prefixEnd_126030 43142644590831427163603 := by
  unfold tailWord_126030
  simp only [CollatzResearch.WordTrace]
  refine ⟨574586466677788631934943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3064461155614872703653029 574586466677788631934943)
  ·
    refine ⟨861879700016682947902415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 574586466677788631934943 861879700016682947902415)
    ·
      refine ⟨1292819550025024421853623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 861879700016682947902415 1292819550025024421853623)
      ·
        refine ⟨1939229325037536632780435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1292819550025024421853623 1939229325037536632780435)
        ·
          refine ⟨2908843987556304949170653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939229325037536632780435 2908843987556304949170653)
          ·
            refine ⟨1090816495333614355938995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2908843987556304949170653 1090816495333614355938995)
            ·
              refine ⟨1636224743000421533908493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090816495333614355938995 1636224743000421533908493)
              ·
                refine ⟨613584278625158075215685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1636224743000421533908493 613584278625158075215685)
                ·
                  refine ⟨115047052242217139102941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 613584278625158075215685 115047052242217139102941)
                  ·
                    refine ⟨43142644590831427163603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115047052242217139102941 43142644590831427163603)
                    ·
                      rfl

theorem cell22_126030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_126030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126030 prefixEnd_126030 := by exact prefixLift 126030
  have htrace : WordTrace (prefixWord ++ tailWord_126030) baseStart_126030 baseEnd_126030 := by
    simpa [prefixWord, tailWord_126030, baseEnd_126030] using wordTrace_append hprefix tailTrace_126030
  have hstable : (prefixWord ++ tailWord_126030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126030).length < 2 ^ (prefixWord ++ tailWord_126030).sum := by decide
  have hdescent : baseEnd_126030 < baseStart_126030 := by decide
  rcases family_descends (prefixWord ++ tailWord_126030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126038 : List Nat := [5, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_126038 : Nat := 118140960795 + 126038 * 2 ^ 59
def prefixEnd_126038 : Nat := 4983230072969 + 3 ^ 40 * 126038 * 2
def baseEnd_126038 : Nat := 14381794384774024321193

theorem tailTrace_126038 : CollatzResearch.WordTrace tailWord_126038 prefixEnd_126038 14381794384774024321193 := by
  unfold tailWord_126038
  simp only [CollatzResearch.WordTrace]
  refine ⟨287311469837082901360673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3064655678262217614513845 287311469837082901360673)
  ·
    refine ⟨215483602377812176020505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287311469837082901360673 215483602377812176020505)
    ·
      refine ⟨161612701783359132015379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215483602377812176020505 161612701783359132015379)
      ·
        refine ⟨242419052675038698023069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161612701783359132015379 242419052675038698023069)
        ·
          refine ⟨90907144753139511758651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242419052675038698023069 90907144753139511758651)
          ·
            refine ⟨136360717129709267637977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90907144753139511758651 136360717129709267637977)
            ·
              refine ⟨102270537847281950728483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136360717129709267637977 102270537847281950728483)
              ·
                refine ⟨153405806770922926092725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102270537847281950728483 153405806770922926092725)
                ·
                  refine ⟨14381794384774024321193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153405806770922926092725 14381794384774024321193)
                  ·
                    rfl

theorem cell22_126038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_126038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126038 prefixEnd_126038 := by exact prefixLift 126038
  have htrace : WordTrace (prefixWord ++ tailWord_126038) baseStart_126038 baseEnd_126038 := by
    simpa [prefixWord, tailWord_126038, baseEnd_126038] using wordTrace_append hprefix tailTrace_126038
  have hstable : (prefixWord ++ tailWord_126038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126038).length < 2 ^ (prefixWord ++ tailWord_126038).sum := by decide
  have hdescent : baseEnd_126038 < baseStart_126038 := by decide
  rcases family_descends (prefixWord ++ tailWord_126038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126062 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_126062 : Nat := 118140960795 + 126062 * 2 ^ 59
def prefixEnd_126062 : Nat := 4983230072969 + 3 ^ 40 * 126062 * 2
def baseEnd_126062 : Nat := 43153598844794010363505

theorem tailTrace_126062 : CollatzResearch.WordTrace tailWord_126062 prefixEnd_126062 43153598844794010363505 := by
  unfold tailWord_126062
  simp only [CollatzResearch.WordTrace]
  refine ⟨574732358663297315080555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3065239246204252347096293 574732358663297315080555)
  ·
    refine ⟨862098537994945972620833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 574732358663297315080555 862098537994945972620833)
    ·
      refine ⟨646573903496209479465625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 862098537994945972620833 646573903496209479465625)
      ·
        refine ⟨484930427622157109599219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646573903496209479465625 484930427622157109599219)
        ·
          refine ⟨727395641433235664398829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484930427622157109599219 727395641433235664398829)
          ·
            refine ⟨272773365537463374149561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 727395641433235664398829 272773365537463374149561)
            ·
              refine ⟨204580024153097530612171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272773365537463374149561 204580024153097530612171)
              ·
                refine ⟨306870036229646295918257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204580024153097530612171 306870036229646295918257)
                ·
                  refine ⟨230152527172234721938693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306870036229646295918257 230152527172234721938693)
                  ·
                    refine ⟨43153598844794010363505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 230152527172234721938693 43153598844794010363505)
                    ·
                      rfl

theorem cell22_126062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_126062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126062 prefixEnd_126062 := by exact prefixLift 126062
  have htrace : WordTrace (prefixWord ++ tailWord_126062) baseStart_126062 baseEnd_126062 := by
    simpa [prefixWord, tailWord_126062, baseEnd_126062] using wordTrace_append hprefix tailTrace_126062
  have hstable : (prefixWord ++ tailWord_126062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126062).length < 2 ^ (prefixWord ++ tailWord_126062).sum := by decide
  have hdescent : baseEnd_126062 < baseStart_126062 := by decide
  rcases family_descends (prefixWord ++ tailWord_126062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126180 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_126180 : Nat := 118140960795 + 126180 * 2 ^ 59
def prefixEnd_126180 : Nat := 4983230072969 + 3 ^ 40 * 126180 * 2
def baseEnd_126180 : Nat := 43193992656281035913143

theorem tailTrace_126180 : CollatzResearch.WordTrace tailWord_126180 prefixEnd_126180 43193992656281035913143 := by
  unfold tailWord_126180
  simp only [CollatzResearch.WordTrace]
  refine ⟨2301081341439442336719997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3068108455252589782293329 2301081341439442336719997)
  ·
    refine ⟨862905503039790876269999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2301081341439442336719997 862905503039790876269999)
    ·
      refine ⟨1294358254559686314404999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 862905503039790876269999 1294358254559686314404999)
      ·
        refine ⟨1941537381839529471607499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294358254559686314404999 1941537381839529471607499)
        ·
          refine ⟨2912306072759294207411249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1941537381839529471607499 2912306072759294207411249)
          ·
            refine ⟨2184229554569470655558437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2912306072759294207411249 2184229554569470655558437)
            ·
              refine ⟨409543041481775747917207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2184229554569470655558437 409543041481775747917207)
              ·
                refine ⟨614314562222663621875811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409543041481775747917207 614314562222663621875811)
                ·
                  refine ⟨921471843333995432813717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614314562222663621875811 921471843333995432813717)
                  ·
                    refine ⟨43193992656281035913143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 921471843333995432813717 43193992656281035913143)
                    ·
                      rfl

theorem cell22_126180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_126180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126180 prefixEnd_126180 := by exact prefixLift 126180
  have htrace : WordTrace (prefixWord ++ tailWord_126180) baseStart_126180 baseEnd_126180 := by
    simpa [prefixWord, tailWord_126180, baseEnd_126180] using wordTrace_append hprefix tailTrace_126180
  have hstable : (prefixWord ++ tailWord_126180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126180).length < 2 ^ (prefixWord ++ tailWord_126180).sum := by decide
  have hdescent : baseEnd_126180 < baseStart_126180 := by decide
  rcases family_descends (prefixWord ++ tailWord_126180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126195 : List Nat := [1, 1, 1, 2, 2, 7, 8]
def baseStart_126195 : Nat := 118140960795 + 126195 * 2 ^ 59
def prefixEnd_126195 : Nat := 4983230072969 + 3 ^ 40 * 126195 * 2
def baseEnd_126195 : Nat := 1599967683808370251411

theorem tailTrace_126195 : CollatzResearch.WordTrace tailWord_126195 prefixEnd_126195 1599967683808370251411 := by
  unfold tailWord_126195
  simp only [CollatzResearch.WordTrace]
  refine ⟨4602709777824542235236039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3068473185216361490157359 4602709777824542235236039)
  ·
    refine ⟨6904064666736813352854059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4602709777824542235236039 6904064666736813352854059)
    ·
      refine ⟨10356097000105220029281089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6904064666736813352854059 10356097000105220029281089)
      ·
        refine ⟨7767072750078915021960817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10356097000105220029281089 7767072750078915021960817)
        ·
          refine ⟨5825304562559186266470613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7767072750078915021960817 5825304562559186266470613)
          ·
            refine ⟨136530575684980928120405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 5825304562559186266470613 136530575684980928120405)
            ·
              refine ⟨1599967683808370251411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 136530575684980928120405 1599967683808370251411)
              ·
                rfl

theorem cell22_126195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 8].length) (baseStart_126195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126195 prefixEnd_126195 := by exact prefixLift 126195
  have htrace : WordTrace (prefixWord ++ tailWord_126195) baseStart_126195 baseEnd_126195 := by
    simpa [prefixWord, tailWord_126195, baseEnd_126195] using wordTrace_append hprefix tailTrace_126195
  have hstable : (prefixWord ++ tailWord_126195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126195).length < 2 ^ (prefixWord ++ tailWord_126195).sum := by decide
  have hdescent : baseEnd_126195 < baseStart_126195 := by decide
  rcases family_descends (prefixWord ++ tailWord_126195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126212 : List Nat := [2, 3, 2, 2, 2, 2, 2, 7]
def baseStart_126212 : Nat := 118140960795 + 126212 * 2 ^ 59
def prefixEnd_126212 : Nat := 4983230072969 + 3 ^ 40 * 126212 * 2
def baseEnd_126212 : Nat := 4800549656693735457005

theorem tailTrace_126212 : CollatzResearch.WordTrace tailWord_126212 prefixEnd_126212 4800549656693735457005 := by
  unfold tailWord_126212
  simp only [CollatzResearch.WordTrace]
  refine ⟨2301664909381477069302445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3068886545841969425736593 2301664909381477069302445)
  ·
    refine ⟨863124341018053900988417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2301664909381477069302445 863124341018053900988417)
    ·
      refine ⟨647343255763540425741313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 863124341018053900988417 647343255763540425741313)
      ·
        refine ⟨485507441822655319305985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 647343255763540425741313 485507441822655319305985)
        ·
          refine ⟨364130581366991489479489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485507441822655319305985 364130581366991489479489)
          ·
            refine ⟨273097936025243617109617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364130581366991489479489 273097936025243617109617)
            ·
              refine ⟨204823452018932712832213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273097936025243617109617 204823452018932712832213)
              ·
                refine ⟨4800549656693735457005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 204823452018932712832213 4800549656693735457005)
                ·
                  rfl

theorem cell22_126212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 7].length) (baseStart_126212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126212 prefixEnd_126212 := by exact prefixLift 126212
  have htrace : WordTrace (prefixWord ++ tailWord_126212) baseStart_126212 baseEnd_126212 := by
    simpa [prefixWord, tailWord_126212, baseEnd_126212] using wordTrace_append hprefix tailTrace_126212
  have hstable : (prefixWord ++ tailWord_126212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126212).length < 2 ^ (prefixWord ++ tailWord_126212).sum := by decide
  have hdescent : baseEnd_126212 < baseStart_126212 := by decide
  rcases family_descends (prefixWord ++ tailWord_126212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126255 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 2, 5]
def baseStart_126255 : Nat := 118140960795 + 126255 * 2 ^ 59
def prefixEnd_126255 : Nat := 4983230072969 + 3 ^ 40 * 126255 * 2
def baseEnd_126255 : Nat := 43219666689005840287913

theorem tailTrace_126255 : CollatzResearch.WordTrace tailWord_126255 prefixEnd_126255 43219666689005840287913 := by
  unfold tailWord_126255
  simp only [CollatzResearch.WordTrace]
  refine ⟨4604898157607172482420219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3069932105071448321613479 4604898157607172482420219)
  ·
    refine ⟨6907347236410758723630329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4604898157607172482420219 6907347236410758723630329)
    ·
      refine ⟨5180510427308069042722747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6907347236410758723630329 5180510427308069042722747)
      ·
        refine ⟨7770765640962103564084121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5180510427308069042722747 7770765640962103564084121)
        ·
          refine ⟨5828074230721577673063091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7770765640962103564084121 5828074230721577673063091)
          ·
            refine ⟨8742111346082366509594637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5828074230721577673063091 8742111346082366509594637)
            ·
              refine ⟨3278291754780887441097989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8742111346082366509594637 3278291754780887441097989)
              ·
                refine ⟨614679704021416395205873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3278291754780887441097989 614679704021416395205873)
                ·
                  refine ⟨461009778016062296404405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614679704021416395205873 461009778016062296404405)
                  ·
                    refine ⟨43219666689005840287913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 461009778016062296404405 43219666689005840287913)
                    ·
                      rfl

theorem cell22_126255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_126255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126255 prefixEnd_126255 := by exact prefixLift 126255
  have htrace : WordTrace (prefixWord ++ tailWord_126255) baseStart_126255 baseEnd_126255 := by
    simpa [prefixWord, tailWord_126255, baseEnd_126255] using wordTrace_append hprefix tailTrace_126255
  have hstable : (prefixWord ++ tailWord_126255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126255).length < 2 ^ (prefixWord ++ tailWord_126255).sum := by decide
  have hdescent : baseEnd_126255 < baseStart_126255 := by decide
  rcases family_descends (prefixWord ++ tailWord_126255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126257 : List Nat := [1, 2, 2, 3, 3, 1, 1, 4, 5]
def baseStart_126257 : Nat := 118140960795 + 126257 * 2 ^ 59
def prefixEnd_126257 : Nat := 4983230072969 + 3 ^ 40 * 126257 * 2
def baseEnd_126257 : Nat := 14406783776626167245969

theorem tailTrace_126257 : CollatzResearch.WordTrace tailWord_126257 prefixEnd_126257 14406783776626167245969 := by
  unfold tailWord_126257
  simp only [CollatzResearch.WordTrace]
  refine ⟨4604971103599926823993025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3069980735733284549328683 4604971103599926823993025)
  ·
    refine ⟨3453728327699945117994769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4604971103599926823993025 3453728327699945117994769)
    ·
      refine ⟨2590296245774958838496077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3453728327699945117994769 2590296245774958838496077)
      ·
        refine ⟨971361092165609564436029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2590296245774958838496077 971361092165609564436029)
        ·
          refine ⟨364260409562103586663511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 971361092165609564436029 364260409562103586663511)
          ·
            refine ⟨546390614343155379995267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364260409562103586663511 546390614343155379995267)
            ·
              refine ⟨819585921514733069992901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546390614343155379995267 819585921514733069992901)
              ·
                refine ⟨153672360284012450623669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 819585921514733069992901 153672360284012450623669)
                ·
                  refine ⟨14406783776626167245969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153672360284012450623669 14406783776626167245969)
                  ·
                    rfl

theorem cell22_126257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 5].length) (baseStart_126257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126257 prefixEnd_126257 := by exact prefixLift 126257
  have htrace : WordTrace (prefixWord ++ tailWord_126257) baseStart_126257 baseEnd_126257 := by
    simpa [prefixWord, tailWord_126257, baseEnd_126257] using wordTrace_append hprefix tailTrace_126257
  have hstable : (prefixWord ++ tailWord_126257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126257).length < 2 ^ (prefixWord ++ tailWord_126257).sum := by decide
  have hdescent : baseEnd_126257 < baseStart_126257 := by decide
  rcases family_descends (prefixWord ++ tailWord_126257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126261 : List Nat := [1, 3, 3, 1, 2, 3, 1, 4, 1, 3]
def baseStart_126261 : Nat := 118140960795 + 126261 * 2 ^ 59
def prefixEnd_126261 : Nat := 4983230072969 + 3 ^ 40 * 126261 * 2
def baseEnd_126261 : Nat := 43221720611623824637895

theorem tailTrace_126261 : CollatzResearch.WordTrace tailWord_126261 prefixEnd_126261 43221720611623824637895 := by
  unfold tailWord_126261
  simp only [CollatzResearch.WordTrace]
  refine ⟨4605116995585435507138637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3070077997056957004759091 4605116995585435507138637)
  ·
    refine ⟨1726918873344538315176989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4605116995585435507138637 1726918873344538315176989)
    ·
      refine ⟨647594577504201868191371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1726918873344538315176989 647594577504201868191371)
      ·
        refine ⟨971391866256302802287057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647594577504201868191371 971391866256302802287057)
        ·
          refine ⟨728543899692227101715293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 971391866256302802287057 728543899692227101715293)
          ·
            refine ⟨273203962384585163143235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 728543899692227101715293 273203962384585163143235)
            ·
              refine ⟨409805943576877744714853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273203962384585163143235 409805943576877744714853)
              ·
                refine ⟨76838614420664577134035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409805943576877744714853 76838614420664577134035)
                ·
                  refine ⟨115257921630996865701053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76838614420664577134035 115257921630996865701053)
                  ·
                    refine ⟨43221720611623824637895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115257921630996865701053 43221720611623824637895)
                    ·
                      rfl

theorem cell22_126261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_126261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126261 prefixEnd_126261 := by exact prefixLift 126261
  have htrace : WordTrace (prefixWord ++ tailWord_126261) baseStart_126261 baseEnd_126261 := by
    simpa [prefixWord, tailWord_126261, baseEnd_126261] using wordTrace_append hprefix tailTrace_126261
  have hstable : (prefixWord ++ tailWord_126261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126261).length < 2 ^ (prefixWord ++ tailWord_126261).sum := by decide
  have hdescent : baseEnd_126261 < baseStart_126261 := by decide
  rcases family_descends (prefixWord ++ tailWord_126261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126304 : List Nat := [2, 1, 1, 3, 4, 2, 1, 3, 1, 4]
def baseStart_126304 : Nat := 118140960795 + 126304 * 2 ^ 59
def prefixEnd_126304 : Nat := 4983230072969 + 3 ^ 40 * 126304 * 2
def baseEnd_126304 : Nat := 43236440390386045812763

theorem tailTrace_126304 : CollatzResearch.WordTrace tailWord_126304 prefixEnd_126304 43236440390386045812763 := by
  unfold tailWord_126304
  simp only [CollatzResearch.WordTrace]
  refine ⟨2303342667214826925476983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3071123556286435900635977 2303342667214826925476983)
  ·
    refine ⟨3455014000822240388215475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2303342667214826925476983 3455014000822240388215475)
    ·
      refine ⟨5182521001233360582323213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3455014000822240388215475 5182521001233360582323213)
      ·
        refine ⟨1943445375462510218371205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5182521001233360582323213 1943445375462510218371205)
        ·
          refine ⟨364396007899220665944601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1943445375462510218371205 364396007899220665944601)
          ·
            refine ⟨273297005924415499458451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364396007899220665944601 273297005924415499458451)
            ·
              refine ⟨409945508886623249187677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273297005924415499458451 409945508886623249187677)
              ·
                refine ⟨153729565832483718445379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409945508886623249187677 153729565832483718445379)
                ·
                  refine ⟨230594348748725577668069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153729565832483718445379 230594348748725577668069)
                  ·
                    refine ⟨43236440390386045812763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 230594348748725577668069 43236440390386045812763)
                    ·
                      rfl

theorem cell22_126304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_126304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126304 prefixEnd_126304 := by exact prefixLift 126304
  have htrace : WordTrace (prefixWord ++ tailWord_126304) baseStart_126304 baseEnd_126304 := by
    simpa [prefixWord, tailWord_126304, baseEnd_126304] using wordTrace_append hprefix tailTrace_126304
  have hstable : (prefixWord ++ tailWord_126304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126304).length < 2 ^ (prefixWord ++ tailWord_126304).sum := by decide
  have hdescent : baseEnd_126304 < baseStart_126304 := by decide
  rcases family_descends (prefixWord ++ tailWord_126304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126315 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 5, 6]
def baseStart_126315 : Nat := 118140960795 + 126315 * 2 ^ 59
def prefixEnd_126315 : Nat := 4983230072969 + 3 ^ 40 * 126315 * 2
def baseEnd_126315 : Nat := 43240205915185683787729

theorem tailTrace_126315 : CollatzResearch.WordTrace tailWord_126315 prefixEnd_126315 43240205915185683787729 := by
  unfold tailWord_126315
  simp only [CollatzResearch.WordTrace]
  refine ⟨4607086537389802729604399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3071391024926535153069599 4607086537389802729604399)
  ·
    refine ⟨6910629806084704094406599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4607086537389802729604399 6910629806084704094406599)
    ·
      refine ⟨10365944709127056141609899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6910629806084704094406599 10365944709127056141609899)
      ·
        refine ⟨15548917063690584212414849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10365944709127056141609899 15548917063690584212414849)
        ·
          refine ⟨11661687797767938159311137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15548917063690584212414849 11661687797767938159311137)
          ·
            refine ⟨8746265848325953619483353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11661687797767938159311137 8746265848325953619483353)
            ·
              refine ⟨6559699386244465214612515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8746265848325953619483353 6559699386244465214612515)
              ·
                refine ⟨9839549079366697821918773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559699386244465214612515 9839549079366697821918773)
                ·
                  refine ⟨922457726190627920804885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9839549079366697821918773 922457726190627920804885)
                  ·
                    refine ⟨43240205915185683787729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 922457726190627920804885 43240205915185683787729)
                    ·
                      rfl

theorem cell22_126315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 6].length) (baseStart_126315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126315 prefixEnd_126315 := by exact prefixLift 126315
  have htrace : WordTrace (prefixWord ++ tailWord_126315) baseStart_126315 baseEnd_126315 := by
    simpa [prefixWord, tailWord_126315, baseEnd_126315] using wordTrace_append hprefix tailTrace_126315
  have hstable : (prefixWord ++ tailWord_126315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126315).length < 2 ^ (prefixWord ++ tailWord_126315).sum := by decide
  have hdescent : baseEnd_126315 < baseStart_126315 := by decide
  rcases family_descends (prefixWord ++ tailWord_126315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126338 : List Nat := [3, 4, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_126338 : Nat := 118140960795 + 126338 * 2 ^ 59
def prefixEnd_126338 : Nat := 4983230072969 + 3 ^ 40 * 126338 * 2
def baseEnd_126338 : Nat := 43248079285221290462659

theorem tailTrace_126338 : CollatzResearch.WordTrace tailWord_126338 prefixEnd_126338 43248079285221290462659 := by
  unfold tailWord_126338
  simp only [CollatzResearch.WordTrace]
  refine ⟨1151981354076619414422917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3071950277537651771794445 1151981354076619414422917)
  ·
    refine ⟨215996503889366140204297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1151981354076619414422917 215996503889366140204297)
    ·
      refine ⟨161997377917024605153223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215996503889366140204297 161997377917024605153223)
      ·
        refine ⟨242996066875536907729835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161997377917024605153223 242996066875536907729835)
        ·
          refine ⟨364494100313305361594753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242996066875536907729835 364494100313305361594753)
          ·
            refine ⟨273370575234979021196065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364494100313305361594753 273370575234979021196065)
            ·
              refine ⟨205027931426234265897049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273370575234979021196065 205027931426234265897049)
              ·
                refine ⟨153770948569675699422787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205027931426234265897049 153770948569675699422787)
                ·
                  refine ⟨230656422854513549134181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153770948569675699422787 230656422854513549134181)
                  ·
                    refine ⟨43248079285221290462659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 230656422854513549134181 43248079285221290462659)
                    ·
                      rfl

theorem cell22_126338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_126338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126338 prefixEnd_126338 := by exact prefixLift 126338
  have htrace : WordTrace (prefixWord ++ tailWord_126338) baseStart_126338 baseEnd_126338 := by
    simpa [prefixWord, tailWord_126338, baseEnd_126338] using wordTrace_append hprefix tailTrace_126338
  have hstable : (prefixWord ++ tailWord_126338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126338).length < 2 ^ (prefixWord ++ tailWord_126338).sum := by decide
  have hdescent : baseEnd_126338 < baseStart_126338 := by decide
  rcases family_descends (prefixWord ++ tailWord_126338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126439 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 3, 4]
def baseStart_126439 : Nat := 118140960795 + 126439 * 2 ^ 59
def prefixEnd_126439 : Nat := 4983230072969 + 3 ^ 40 * 126439 * 2
def baseEnd_126439 : Nat := 43282653649290693687349

theorem tailTrace_126439 : CollatzResearch.WordTrace tailWord_126439 prefixEnd_126439 43282653649290693687349 := by
  unfold tailWord_126439
  simp only [CollatzResearch.WordTrace]
  refine ⟨4611609188940571907118371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3074406125960381271412247 4611609188940571907118371)
  ·
    refine ⟨6917413783410857860677557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4611609188940571907118371 6917413783410857860677557)
    ·
      refine ⟨648507542194767924438521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6917413783410857860677557 648507542194767924438521)
      ·
        refine ⟨486380656646075943328891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648507542194767924438521 486380656646075943328891)
        ·
          refine ⟨729570984969113914993337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486380656646075943328891 729570984969113914993337)
          ·
            refine ⟨547178238726835436245003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729570984969113914993337 547178238726835436245003)
            ·
              refine ⟨820767358090253154367505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547178238726835436245003 820767358090253154367505)
              ·
                refine ⟨615575518567689865775629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820767358090253154367505 615575518567689865775629)
                ·
                  refine ⟨230840819462883699665861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615575518567689865775629 230840819462883699665861)
                  ·
                    refine ⟨43282653649290693687349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 230840819462883699665861 43282653649290693687349)
                    ·
                      rfl

theorem cell22_126439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_126439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126439 prefixEnd_126439 := by exact prefixLift 126439
  have htrace : WordTrace (prefixWord ++ tailWord_126439) baseStart_126439 baseEnd_126439 := by
    simpa [prefixWord, tailWord_126439, baseEnd_126439] using wordTrace_append hprefix tailTrace_126439
  have hstable : (prefixWord ++ tailWord_126439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126439).length < 2 ^ (prefixWord ++ tailWord_126439).sum := by decide
  have hdescent : baseEnd_126439 < baseStart_126439 := by decide
  rcases family_descends (prefixWord ++ tailWord_126439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126454 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_126454 : Nat := 118140960795 + 126454 * 2 ^ 59
def prefixEnd_126454 : Nat := 4983230072969 + 3 ^ 40 * 126454 * 2
def baseEnd_126454 : Nat := 14429262818611884854101

theorem tailTrace_126454 : CollatzResearch.WordTrace tailWord_126454 prefixEnd_126454 14429262818611884854101 := by
  unfold tailWord_126454
  simp only [CollatzResearch.WordTrace]
  refine ⟨288259767742889341807151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3074770855924152979276277 288259767742889341807151)
  ·
    refine ⟨432389651614334012710727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288259767742889341807151 432389651614334012710727)
    ·
      refine ⟨648584477421501019066091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432389651614334012710727 648584477421501019066091)
      ·
        refine ⟨972876716132251528599137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648584477421501019066091 972876716132251528599137)
        ·
          refine ⟨729657537099188646449353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 972876716132251528599137 729657537099188646449353)
          ·
            refine ⟨547243152824391484837015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729657537099188646449353 547243152824391484837015)
            ·
              refine ⟨820864729236587227255523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547243152824391484837015 820864729236587227255523)
              ·
                refine ⟨1231297093854880840883285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820864729236587227255523 1231297093854880840883285)
                ·
                  refine ⟨14429262818611884854101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1231297093854880840883285 14429262818611884854101)
                  ·
                    rfl

theorem cell22_126454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_126454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126454 prefixEnd_126454 := by exact prefixLift 126454
  have htrace : WordTrace (prefixWord ++ tailWord_126454) baseStart_126454 baseEnd_126454 := by
    simpa [prefixWord, tailWord_126454, baseEnd_126454] using wordTrace_append hprefix tailTrace_126454
  have hstable : (prefixWord ++ tailWord_126454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126454).length < 2 ^ (prefixWord ++ tailWord_126454).sum := by decide
  have hdescent : baseEnd_126454 < baseStart_126454 := by decide
  rcases family_descends (prefixWord ++ tailWord_126454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126469 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 4, 3]
def baseStart_126469 : Nat := 118140960795 + 126469 * 2 ^ 59
def prefixEnd_126469 : Nat := 4983230072969 + 3 ^ 40 * 126469 * 2
def baseEnd_126469 : Nat := 43292923262380615437257

theorem tailTrace_126469 : CollatzResearch.WordTrace tailWord_126469 prefixEnd_126469 43292923262380615437257 := by
  unfold tailWord_126469
  simp only [CollatzResearch.WordTrace]
  refine ⟨4612703378831887030710461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3075135585887924687140307 4612703378831887030710461)
  ·
    refine ⟨1729763767061957636516423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4612703378831887030710461 1729763767061957636516423)
    ·
      refine ⟨2594645650592936454774635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1729763767061957636516423 2594645650592936454774635)
      ·
        refine ⟨3891968475889404682161953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2594645650592936454774635 3891968475889404682161953)
        ·
          refine ⟨2918976356917053511621465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3891968475889404682161953 2918976356917053511621465)
          ·
            refine ⟨2189232267687790133716099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2918976356917053511621465 2189232267687790133716099)
            ·
              refine ⟨3283848401531685200574149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189232267687790133716099 3283848401531685200574149)
              ·
                refine ⟨615721575287190975107653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3283848401531685200574149 615721575287190975107653)
                ·
                  refine ⟨115447795366348307832685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 615721575287190975107653 115447795366348307832685)
                  ·
                    refine ⟨43292923262380615437257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115447795366348307832685 43292923262380615437257)
                    ·
                      rfl

theorem cell22_126469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_126469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126469 prefixEnd_126469 := by exact prefixLift 126469
  have htrace : WordTrace (prefixWord ++ tailWord_126469) baseStart_126469 baseEnd_126469 := by
    simpa [prefixWord, tailWord_126469, baseEnd_126469] using wordTrace_append hprefix tailTrace_126469
  have hstable : (prefixWord ++ tailWord_126469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126469).length < 2 ^ (prefixWord ++ tailWord_126469).sum := by decide
  have hdescent : baseEnd_126469 < baseStart_126469 := by decide
  rcases family_descends (prefixWord ++ tailWord_126469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126471 : List Nat := [1, 1, 4, 3, 2, 1, 1, 5, 4]
def baseStart_126471 : Nat := 118140960795 + 126471 * 2 ^ 59
def prefixEnd_126471 : Nat := 4983230072969 + 3 ^ 40 * 126471 * 2
def baseEnd_126471 : Nat := 14431202634417758962417

theorem tailTrace_126471 : CollatzResearch.WordTrace tailWord_126471 prefixEnd_126471 14431202634417758962417 := by
  unfold tailWord_126471
  simp only [CollatzResearch.WordTrace]
  refine ⟨4612776324824641372283267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3075184216549760914855511 4612776324824641372283267)
  ·
    refine ⟨6919164487236962058424901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4612776324824641372283267 6919164487236962058424901)
    ·
      refine ⟨1297343341356930385954669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6919164487236962058424901 1297343341356930385954669)
      ·
        refine ⟨486503753008848894733001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1297343341356930385954669 486503753008848894733001)
        ·
          refine ⟨364877814756636671049751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486503753008848894733001 364877814756636671049751)
          ·
            refine ⟨547316722134955006574627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364877814756636671049751 547316722134955006574627)
            ·
              refine ⟨820975083202432509861941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547316722134955006574627 820975083202432509861941)
              ·
                refine ⟨76966414050228047799557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 820975083202432509861941 76966414050228047799557)
                ·
                  refine ⟨14431202634417758962417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76966414050228047799557 14431202634417758962417)
                  ·
                    rfl

theorem cell22_126471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 4].length) (baseStart_126471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126471 prefixEnd_126471 := by exact prefixLift 126471
  have htrace : WordTrace (prefixWord ++ tailWord_126471) baseStart_126471 baseEnd_126471 := by
    simpa [prefixWord, tailWord_126471, baseEnd_126471] using wordTrace_append hprefix tailTrace_126471
  have hstable : (prefixWord ++ tailWord_126471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126471).length < 2 ^ (prefixWord ++ tailWord_126471).sum := by decide
  have hdescent : baseEnd_126471 < baseStart_126471 := by decide
  rcases family_descends (prefixWord ++ tailWord_126471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126477 : List Nat := [1, 7, 1, 1, 3, 1, 1, 2, 5]
def baseStart_126477 : Nat := 118140960795 + 126477 * 2 ^ 59
def prefixEnd_126477 : Nat := 4983230072969 + 3 ^ 40 * 126477 * 2
def baseEnd_126477 : Nat := 14431887275290420412411

theorem tailTrace_126477 : CollatzResearch.WordTrace tailWord_126477 prefixEnd_126477 14431887275290420412411 := by
  unfold tailWord_126477
  simp only [CollatzResearch.WordTrace]
  refine ⟨4612995162802904397001685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3075330108535269598001123 4612995162802904397001685)
  ·
    refine ⟨108117074128193071804727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 4612995162802904397001685 108117074128193071804727)
    ·
      refine ⟨162175611192289607707091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108117074128193071804727 162175611192289607707091)
      ·
        refine ⟨243263416788434411560637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162175611192289607707091 243263416788434411560637)
        ·
          refine ⟨91223781295662904335239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243263416788434411560637 91223781295662904335239)
          ·
            refine ⟨136835671943494356502859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91223781295662904335239 136835671943494356502859)
            ·
              refine ⟨205253507915241534754289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136835671943494356502859 205253507915241534754289)
              ·
                refine ⟨153940130936431151065717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205253507915241534754289 153940130936431151065717)
                ·
                  refine ⟨14431887275290420412411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153940130936431151065717 14431887275290420412411)
                  ·
                    rfl

theorem cell22_126477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_126477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126477 prefixEnd_126477 := by exact prefixLift 126477
  have htrace : WordTrace (prefixWord ++ tailWord_126477) baseStart_126477 baseEnd_126477 := by
    simpa [prefixWord, tailWord_126477, baseEnd_126477] using wordTrace_append hprefix tailTrace_126477
  have hstable : (prefixWord ++ tailWord_126477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126477).length < 2 ^ (prefixWord ++ tailWord_126477).sum := by decide
  have hdescent : baseEnd_126477 < baseStart_126477 := by decide
  rcases family_descends (prefixWord ++ tailWord_126477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126544 : List Nat := [2, 1, 1, 1, 1, 3, 4, 4, 5]
def baseStart_126544 : Nat := 118140960795 + 126544 * 2 ^ 59
def prefixEnd_126544 : Nat := 4983230072969 + 3 ^ 40 * 126544 * 2
def baseEnd_126544 : Nat := 14439532431701806604009

theorem tailTrace_126544 : CollatzResearch.WordTrace tailWord_126544 prefixEnd_126544 14439532431701806604009 := by
  unfold tailWord_126544
  simp only [CollatzResearch.WordTrace]
  refine ⟨2307719426780087419845343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3076959235706783226460457 2307719426780087419845343)
  ·
    refine ⟨3461579140170131129768015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2307719426780087419845343 3461579140170131129768015)
    ·
      refine ⟨5192368710255196694652023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3461579140170131129768015 5192368710255196694652023)
      ·
        refine ⟨7788553065382795041978035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5192368710255196694652023 7788553065382795041978035)
        ·
          refine ⟨11682829598074192562967053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7788553065382795041978035 11682829598074192562967053)
          ·
            refine ⟨4381061099277822211112645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11682829598074192562967053 4381061099277822211112645)
            ·
              refine ⟨821448956114591664583621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4381061099277822211112645 821448956114591664583621)
              ·
                refine ⟨154021679271485937109429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 821448956114591664583621 154021679271485937109429)
                ·
                  refine ⟨14439532431701806604009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154021679271485937109429 14439532431701806604009)
                  ·
                    rfl

theorem cell22_126544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 5].length) (baseStart_126544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126544 prefixEnd_126544 := by exact prefixLift 126544
  have htrace : WordTrace (prefixWord ++ tailWord_126544) baseStart_126544 baseEnd_126544 := by
    simpa [prefixWord, tailWord_126544, baseEnd_126544] using wordTrace_append hprefix tailTrace_126544
  have hstable : (prefixWord ++ tailWord_126544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126544).length < 2 ^ (prefixWord ++ tailWord_126544).sum := by decide
  have hdescent : baseEnd_126544 < baseStart_126544 := by decide
  rcases family_descends (prefixWord ++ tailWord_126544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126550 : List Nat := [5, 2, 2, 2, 1, 1, 2, 7]
def baseStart_126550 : Nat := 118140960795 + 126550 * 2 ^ 59
def prefixEnd_126550 : Nat := 4983230072969 + 3 ^ 40 * 126550 * 2
def baseEnd_126550 : Nat := 4813405690858156018001

theorem tailTrace_126550 : CollatzResearch.WordTrace tailWord_126550 prefixEnd_126550 4813405690858156018001 := by
  unfold tailWord_126550
  simp only [CollatzResearch.WordTrace]
  refine ⟨288478605721152366525569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3077105127692291909606069 288478605721152366525569)
  ·
    refine ⟨216358954290864274894177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288478605721152366525569 216358954290864274894177)
    ·
      refine ⟨162269215718148206170633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216358954290864274894177 162269215718148206170633)
      ·
        refine ⟨121701911788611154627975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162269215718148206170633 121701911788611154627975)
        ·
          refine ⟨182552867682916731941963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121701911788611154627975 182552867682916731941963)
          ·
            refine ⟨273829301524375097912945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182552867682916731941963 273829301524375097912945)
            ·
              refine ⟨205371976143281323434709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273829301524375097912945 205371976143281323434709)
              ·
                refine ⟨4813405690858156018001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 205371976143281323434709 4813405690858156018001)
                ·
                  rfl

theorem cell22_126550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_126550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126550 prefixEnd_126550 := by exact prefixLift 126550
  have htrace : WordTrace (prefixWord ++ tailWord_126550) baseStart_126550 baseEnd_126550 := by
    simpa [prefixWord, tailWord_126550, baseEnd_126550] using wordTrace_append hprefix tailTrace_126550
  have hstable : (prefixWord ++ tailWord_126550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126550).length < 2 ^ (prefixWord ++ tailWord_126550).sum := by decide
  have hdescent : baseEnd_126550 < baseStart_126550 := by decide
  rcases family_descends (prefixWord ++ tailWord_126550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126604 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_126604 : Nat := 118140960795 + 126604 * 2 ^ 59
def prefixEnd_126604 : Nat := 4983230072969 + 3 ^ 40 * 126604 * 2
def baseEnd_126604 : Nat := 43339136521285263311843

theorem tailTrace_126604 : CollatzResearch.WordTrace tailWord_126604 prefixEnd_126604 43339136521285263311843 := by
  unfold tailWord_126604
  simp only [CollatzResearch.WordTrace]
  refine ⟨2308813616671402543437433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3078418155561870057916577 2308813616671402543437433)
  ·
    refine ⟨1731610212503551907578075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2308813616671402543437433 1731610212503551907578075)
    ·
      refine ⟨2597415318755327861367113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1731610212503551907578075 2597415318755327861367113)
      ·
        refine ⟨1948061489066495896025335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2597415318755327861367113 1948061489066495896025335)
        ·
          refine ⟨2922092233599743844038003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948061489066495896025335 2922092233599743844038003)
          ·
            refine ⟨4383138350399615766057005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922092233599743844038003 4383138350399615766057005)
            ·
              refine ⟨1643676881399855912271377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4383138350399615766057005 1643676881399855912271377)
              ·
                refine ⟨1232757661049891934203533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643676881399855912271377 1232757661049891934203533)
                ·
                  refine ⟨462284122893709475326325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232757661049891934203533 462284122893709475326325)
                  ·
                    refine ⟨43339136521285263311843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 462284122893709475326325 43339136521285263311843)
                    ·
                      rfl

theorem cell22_126604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_126604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126604 prefixEnd_126604 := by exact prefixLift 126604
  have htrace : WordTrace (prefixWord ++ tailWord_126604) baseStart_126604 baseEnd_126604 := by
    simpa [prefixWord, tailWord_126604, baseEnd_126604] using wordTrace_append hprefix tailTrace_126604
  have hstable : (prefixWord ++ tailWord_126604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126604).length < 2 ^ (prefixWord ++ tailWord_126604).sum := by decide
  have hdescent : baseEnd_126604 < baseStart_126604 := by decide
  rcases family_descends (prefixWord ++ tailWord_126604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126621 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_126621 : Nat := 118140960795 + 126621 * 2 ^ 59
def prefixEnd_126621 : Nat := 4983230072969 + 3 ^ 40 * 126621 * 2
def baseEnd_126621 : Nat := 43344955968702885636791

theorem tailTrace_126621 : CollatzResearch.WordTrace tailWord_126621 prefixEnd_126621 43344955968702885636791 := by
  unfold tailWord_126621
  simp only [CollatzResearch.WordTrace]
  refine ⟨4618247274281216990243717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3078831516187477993495811 4618247274281216990243717)
  ·
    refine ⟨865921363927728185670697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4618247274281216990243717 865921363927728185670697)
    ·
      refine ⟨649441022945796139253023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 865921363927728185670697 649441022945796139253023)
      ·
        refine ⟨974161534418694208879535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649441022945796139253023 974161534418694208879535)
        ·
          refine ⟨1461242301628041313319303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974161534418694208879535 1461242301628041313319303)
          ·
            refine ⟨2191863452442061969978955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461242301628041313319303 2191863452442061969978955)
            ·
              refine ⟨3287795178663092954968433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2191863452442061969978955 3287795178663092954968433)
              ·
                refine ⟨2465846383997319716226325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3287795178663092954968433 2465846383997319716226325)
                ·
                  refine ⟨115586549249874361698109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2465846383997319716226325 115586549249874361698109)
                  ·
                    refine ⟨43344955968702885636791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115586549249874361698109 43344955968702885636791)
                    ·
                      rfl

theorem cell22_126621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_126621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126621 prefixEnd_126621 := by exact prefixLift 126621
  have htrace : WordTrace (prefixWord ++ tailWord_126621) baseStart_126621 baseEnd_126621 := by
    simpa [prefixWord, tailWord_126621, baseEnd_126621] using wordTrace_append hprefix tailTrace_126621
  have hstable : (prefixWord ++ tailWord_126621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126621).length < 2 ^ (prefixWord ++ tailWord_126621).sum := by decide
  have hdescent : baseEnd_126621 < baseStart_126621 := by decide
  rcases family_descends (prefixWord ++ tailWord_126621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126623 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 6]
def baseStart_126623 : Nat := 118140960795 + 126623 * 2 ^ 59
def prefixEnd_126623 : Nat := 4983230072969 + 3 ^ 40 * 126623 * 2
def baseEnd_126623 : Nat := 14448546869858515695595

theorem tailTrace_126623 : CollatzResearch.WordTrace tailWord_126623 prefixEnd_126623 14448546869858515695595 := by
  unfold tailWord_126623
  simp only [CollatzResearch.WordTrace]
  refine ⟨4618320220273971331816523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3078880146849314221211015 4618320220273971331816523)
  ·
    refine ⟨6927480330410956997724785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4618320220273971331816523 6927480330410956997724785)
    ·
      refine ⟨5195610247808217748293589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6927480330410956997724785 5195610247808217748293589)
      ·
        refine ⟨121772115183005103475631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 5195610247808217748293589 121772115183005103475631)
        ·
          refine ⟨182658172774507655213447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121772115183005103475631 182658172774507655213447)
          ·
            refine ⟨273987259161761482820171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182658172774507655213447 273987259161761482820171)
            ·
              refine ⟨410980888742642224230257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273987259161761482820171 410980888742642224230257)
              ·
                refine ⟨308235666556981668172693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410980888742642224230257 308235666556981668172693)
                ·
                  refine ⟨14448546869858515695595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 308235666556981668172693 14448546869858515695595)
                  ·
                    rfl

theorem cell22_126623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 6].length) (baseStart_126623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126623 prefixEnd_126623 := by exact prefixLift 126623
  have htrace : WordTrace (prefixWord ++ tailWord_126623) baseStart_126623 baseEnd_126623 := by
    simpa [prefixWord, tailWord_126623, baseEnd_126623] using wordTrace_append hprefix tailTrace_126623
  have hstable : (prefixWord ++ tailWord_126623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126623).length < 2 ^ (prefixWord ++ tailWord_126623).sum := by decide
  have hdescent : baseEnd_126623 < baseStart_126623 := by decide
  rcases family_descends (prefixWord ++ tailWord_126623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126696 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 7]
def baseStart_126696 : Nat := 118140960795 + 126696 * 2 ^ 59
def prefixEnd_126696 : Nat := 4983230072969 + 3 ^ 40 * 126696 * 2
def baseEnd_126696 : Nat := 14456876667142563337187

theorem tailTrace_126696 : CollatzResearch.WordTrace tailWord_126696 prefixEnd_126696 14456876667142563337187 := by
  unfold tailWord_126696
  simp only [CollatzResearch.WordTrace]
  refine ⟨2310491374504752399611971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3080655166006336532815961 2310491374504752399611971)
  ·
    refine ⟨3465737061757128599417957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2310491374504752399611971 3465737061757128599417957)
    ·
      refine ⟨649825699079461612390867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3465737061757128599417957 649825699079461612390867)
      ·
        refine ⟨974738548619192418586301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649825699079461612390867 974738548619192418586301)
        ·
          refine ⟨365526955732197156969863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 974738548619192418586301 365526955732197156969863)
          ·
            refine ⟨548290433598295735454795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365526955732197156969863 548290433598295735454795)
            ·
              refine ⟨822435650397443603182193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548290433598295735454795 822435650397443603182193)
              ·
                refine ⟨616826737798082702386645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822435650397443603182193 616826737798082702386645)
                ·
                  refine ⟨14456876667142563337187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 616826737798082702386645 14456876667142563337187)
                  ·
                    rfl

theorem cell22_126696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 7].length) (baseStart_126696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126696 prefixEnd_126696 := by exact prefixLift 126696
  have htrace : WordTrace (prefixWord ++ tailWord_126696) baseStart_126696 baseEnd_126696 := by
    simpa [prefixWord, tailWord_126696, baseEnd_126696] using wordTrace_append hprefix tailTrace_126696
  have hstable : (prefixWord ++ tailWord_126696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126696).length < 2 ^ (prefixWord ++ tailWord_126696).sum := by decide
  have hdescent : baseEnd_126696 < baseStart_126696 := by decide
  rcases family_descends (prefixWord ++ tailWord_126696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126700 : List Nat := [2, 2, 1, 1, 2, 2, 5, 3, 1, 3]
def baseStart_126700 : Nat := 118140960795 + 126700 * 2 ^ 59
def prefixEnd_126700 : Nat := 4983230072969 + 3 ^ 40 * 126700 * 2
def baseEnd_126700 : Nat := 43371999283173012911549

theorem tailTrace_126700 : CollatzResearch.WordTrace tailWord_126700 prefixEnd_126700 43371999283173012911549 := by
  unfold tailWord_126700
  simp only [CollatzResearch.WordTrace]
  refine ⟨2310564320497506741184777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3080752427330008988246369 2310564320497506741184777)
  ·
    refine ⟨1732923240373130055888583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2310564320497506741184777 1732923240373130055888583)
    ·
      refine ⟨2599384860559695083832875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1732923240373130055888583 2599384860559695083832875)
      ·
        refine ⟨3899077290839542625749313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599384860559695083832875 3899077290839542625749313)
        ·
          refine ⟨2924307968129656969311985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3899077290839542625749313 2924307968129656969311985)
          ·
            refine ⟨2193230976097242726983989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2924307968129656969311985 2193230976097242726983989)
            ·
              refine ⟨205615404009116505654749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2193230976097242726983989 205615404009116505654749)
              ·
                refine ⟨77105776503418689620531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205615404009116505654749 77105776503418689620531)
                ·
                  refine ⟨115658664755128034430797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77105776503418689620531 115658664755128034430797)
                  ·
                    refine ⟨43371999283173012911549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115658664755128034430797 43371999283173012911549)
                    ·
                      rfl

theorem cell22_126700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_126700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126700 prefixEnd_126700 := by exact prefixLift 126700
  have htrace : WordTrace (prefixWord ++ tailWord_126700) baseStart_126700 baseEnd_126700 := by
    simpa [prefixWord, tailWord_126700, baseEnd_126700] using wordTrace_append hprefix tailTrace_126700
  have hstable : (prefixWord ++ tailWord_126700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126700).length < 2 ^ (prefixWord ++ tailWord_126700).sum := by decide
  have hdescent : baseEnd_126700 < baseStart_126700 := by decide
  rcases family_descends (prefixWord ++ tailWord_126700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126730 : List Nat := [3, 1, 2, 2, 1, 5, 2, 1, 5]
def baseStart_126730 : Nat := 118140960795 + 126730 * 2 ^ 59
def prefixEnd_126730 : Nat := 4983230072969 + 3 ^ 40 * 126730 * 2
def baseEnd_126730 : Nat := 14460756298754311553819

theorem tailTrace_126730 : CollatzResearch.WordTrace tailWord_126730 prefixEnd_126730 14460756298754311553819 := by
  unfold tailWord_126730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155555707721582151490411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3081481887257552403974429 1155555707721582151490411)
  ·
    refine ⟨1733333561582373227235617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1155555707721582151490411 1733333561582373227235617)
    ·
      refine ⟨1300000171186779920426713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1733333561582373227235617 1300000171186779920426713)
      ·
        refine ⟨975000128390084940320035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1300000171186779920426713 975000128390084940320035)
        ·
          refine ⟨1462500192585127410480053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975000128390084940320035 1462500192585127410480053)
          ·
            refine ⟨137109393054855694732505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1462500192585127410480053 137109393054855694732505)
            ·
              refine ⟨102832044791141771049379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137109393054855694732505 102832044791141771049379)
              ·
                refine ⟨154248067186712656574069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102832044791141771049379 154248067186712656574069)
                ·
                  refine ⟨14460756298754311553819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154248067186712656574069 14460756298754311553819)
                  ·
                    rfl

theorem cell22_126730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_126730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126730 prefixEnd_126730 := by exact prefixLift 126730
  have htrace : WordTrace (prefixWord ++ tailWord_126730) baseStart_126730 baseEnd_126730 := by
    simpa [prefixWord, tailWord_126730, baseEnd_126730] using wordTrace_append hprefix tailTrace_126730
  have hstable : (prefixWord ++ tailWord_126730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126730).length < 2 ^ (prefixWord ++ tailWord_126730).sum := by decide
  have hdescent : baseEnd_126730 < baseStart_126730 := by decide
  rcases family_descends (prefixWord ++ tailWord_126730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126743 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 3, 4]
def baseStart_126743 : Nat := 118140960795 + 126743 * 2 ^ 59
def prefixEnd_126743 : Nat := 4983230072969 + 3 ^ 40 * 126743 * 2
def baseEnd_126743 : Nat := 43386719061935234086417

theorem tailTrace_126743 : CollatzResearch.WordTrace tailWord_126743 prefixEnd_126743 43386719061935234086417 := by
  unfold tailWord_126743
  simp only [CollatzResearch.WordTrace]
  refine ⟨4622696979839231826184883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3081797986559487884123255 4622696979839231826184883)
  ·
    refine ⟨6934045469758847739277325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4622696979839231826184883 6934045469758847739277325)
    ·
      refine ⟨2600267051159567902228997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6934045469758847739277325 2600267051159567902228997)
      ·
        refine ⟨487550072092418981667937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2600267051159567902228997 487550072092418981667937)
        ·
          refine ⟨365662554069314236250953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487550072092418981667937 365662554069314236250953)
          ·
            refine ⟨274246915551985677188215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365662554069314236250953 274246915551985677188215)
            ·
              refine ⟨411370373327978515782323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274246915551985677188215 411370373327978515782323)
              ·
                refine ⟨617055559991967773673485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411370373327978515782323 617055559991967773673485)
                ·
                  refine ⟨231395834996987915127557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617055559991967773673485 231395834996987915127557)
                  ·
                    refine ⟨43386719061935234086417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 231395834996987915127557 43386719061935234086417)
                    ·
                      rfl

theorem cell22_126743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_126743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126743 prefixEnd_126743 := by exact prefixLift 126743
  have htrace : WordTrace (prefixWord ++ tailWord_126743) baseStart_126743 baseEnd_126743 := by
    simpa [prefixWord, tailWord_126743, baseEnd_126743] using wordTrace_append hprefix tailTrace_126743
  have hstable : (prefixWord ++ tailWord_126743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126743).length < 2 ^ (prefixWord ++ tailWord_126743).sum := by decide
  have hdescent : baseEnd_126743 < baseStart_126743 := by decide
  rcases family_descends (prefixWord ++ tailWord_126743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126805 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 2, 4]
def baseStart_126805 : Nat := 118140960795 + 126805 * 2 ^ 59
def prefixEnd_126805 : Nat := 4983230072969 + 3 ^ 40 * 126805 * 2
def baseEnd_126805 : Nat := 43407942928987739036227

theorem tailTrace_126805 : CollatzResearch.WordTrace tailWord_126805 prefixEnd_126805 43407942928987739036227 := by
  unfold tailWord_126805
  simp only [CollatzResearch.WordTrace]
  refine ⟨4624958305614616414941869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3083305537076410943294579 4624958305614616414941869)
  ·
    refine ⟨1734359364605481155603201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4624958305614616414941869 1734359364605481155603201)
    ·
      refine ⟨1300769523454110866702401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1734359364605481155603201 1300769523454110866702401)
      ·
        refine ⟨975577142590583150026801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1300769523454110866702401 975577142590583150026801)
        ·
          refine ⟨731682856942937362520101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975577142590583150026801 731682856942937362520101)
          ·
            refine ⟨137190535676800755472519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 731682856942937362520101 137190535676800755472519)
            ·
              refine ⟨205785803515201133208779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137190535676800755472519 205785803515201133208779)
              ·
                refine ⟨308678705272801699813169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205785803515201133208779 308678705272801699813169)
                ·
                  refine ⟨231509028954601274859877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308678705272801699813169 231509028954601274859877)
                  ·
                    refine ⟨43407942928987739036227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 231509028954601274859877 43407942928987739036227)
                    ·
                      rfl

theorem cell22_126805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_126805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126805 prefixEnd_126805 := by exact prefixLift 126805
  have htrace : WordTrace (prefixWord ++ tailWord_126805) baseStart_126805 baseEnd_126805 := by
    simpa [prefixWord, tailWord_126805, baseEnd_126805] using wordTrace_append hprefix tailTrace_126805
  have hstable : (prefixWord ++ tailWord_126805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126805).length < 2 ^ (prefixWord ++ tailWord_126805).sum := by decide
  have hdescent : baseEnd_126805 < baseStart_126805 := by decide
  rcases family_descends (prefixWord ++ tailWord_126805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126891 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 2, 9]
def baseStart_126891 : Nat := 118140960795 + 126891 * 2 ^ 59
def prefixEnd_126891 : Nat := 4983230072969 + 3 ^ 40 * 126891 * 2
def baseEnd_126891 : Nat := 43437382486512181385963

theorem tailTrace_126891 : CollatzResearch.WordTrace tailWord_126891 prefixEnd_126891 43437382486512181385963 := by
  unfold tailWord_126891
  simp only [CollatzResearch.WordTrace]
  refine ⟨4628094983303053102572527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3085396655535368735048351 4628094983303053102572527)
  ·
    refine ⟨6942142474954579653858791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4628094983303053102572527 6942142474954579653858791)
    ·
      refine ⟨10413213712431869480788187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6942142474954579653858791 10413213712431869480788187)
      ·
        refine ⟨15619820568647804221182281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10413213712431869480788187 15619820568647804221182281)
        ·
          refine ⟨11714865426485853165886711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15619820568647804221182281 11714865426485853165886711)
          ·
            refine ⟨17572298139728779748830067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11714865426485853165886711 17572298139728779748830067)
            ·
              refine ⟨26358447209593169623245101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17572298139728779748830067 26358447209593169623245101)
              ·
                refine ⟨9884417703597438608716913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26358447209593169623245101 9884417703597438608716913)
                ·
                  refine ⟨7413313277698078956537685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9884417703597438608716913 7413313277698078956537685)
                  ·
                    refine ⟨43437382486512181385963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 7413313277698078956537685 43437382486512181385963)
                    ·
                      rfl

theorem cell22_126891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_126891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126891 prefixEnd_126891 := by exact prefixLift 126891
  have htrace : WordTrace (prefixWord ++ tailWord_126891) baseStart_126891 baseEnd_126891 := by
    simpa [prefixWord, tailWord_126891, baseEnd_126891] using wordTrace_append hprefix tailTrace_126891
  have hstable : (prefixWord ++ tailWord_126891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126891).length < 2 ^ (prefixWord ++ tailWord_126891).sum := by decide
  have hdescent : baseEnd_126891 < baseStart_126891 := by decide
  rcases family_descends (prefixWord ++ tailWord_126891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126938 : List Nat := [3, 1, 1, 2, 5, 10]
def baseStart_126938 : Nat := 118140960795 + 126938 * 2 ^ 59
def prefixEnd_126938 : Nat := 4983230072969 + 3 ^ 40 * 126938 * 2
def baseEnd_126938 : Nat := 536462611691601548899

theorem tailTrace_126938 : CollatzResearch.WordTrace tailWord_126938 prefixEnd_126938 536462611691601548899 := by
  unfold tailWord_126938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1157452303533195032383367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3086539476088520086355645 1157452303533195032383367)
  ·
    refine ⟨1736178455299792548575051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1157452303533195032383367 1736178455299792548575051)
    ·
      refine ⟨2604267682949688822862577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1736178455299792548575051 2604267682949688822862577)
      ·
        refine ⟨1953200762212266617146933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2604267682949688822862577 1953200762212266617146933)
        ·
          refine ⟨183112571457399995357525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1953200762212266617146933 183112571457399995357525)
          ·
            refine ⟨536462611691601548899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 183112571457399995357525 536462611691601548899)
            ·
              rfl

theorem cell22_126938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 10].length) (baseStart_126938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126938 prefixEnd_126938 := by exact prefixLift 126938
  have htrace : WordTrace (prefixWord ++ tailWord_126938) baseStart_126938 baseEnd_126938 := by
    simpa [prefixWord, tailWord_126938, baseEnd_126938] using wordTrace_append hprefix tailTrace_126938
  have hstable : (prefixWord ++ tailWord_126938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126938).length < 2 ^ (prefixWord ++ tailWord_126938).sum := by decide
  have hdescent : baseEnd_126938 < baseStart_126938 := by decide
  rcases family_descends (prefixWord ++ tailWord_126938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126974 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_126974 : Nat := 118140960795 + 126974 * 2 ^ 59
def prefixEnd_126974 : Nat := 4983230072969 + 3 ^ 40 * 126974 * 2
def baseEnd_126974 : Nat := 43465795082727631560709

theorem tailTrace_126974 : CollatzResearch.WordTrace tailWord_126974 prefixEnd_126974 43465795082727631560709 := by
  unfold tailWord_126974
  simp only [CollatzResearch.WordTrace]
  refine ⟨578890280250294784730497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3087414828001572185229317 578890280250294784730497)
  ·
    refine ⟨434167710187721088547873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 578890280250294784730497 434167710187721088547873)
    ·
      refine ⟨325625782640790816410905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434167710187721088547873 325625782640790816410905)
      ·
        refine ⟨244219336980593112308179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325625782640790816410905 244219336980593112308179)
        ·
          refine ⟨366329005470889668462269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244219336980593112308179 366329005470889668462269)
          ·
            refine ⟨137373377051583625673351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366329005470889668462269 137373377051583625673351)
            ·
              refine ⟨206060065577375438510027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137373377051583625673351 206060065577375438510027)
              ·
                refine ⟨309090098366063157765041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206060065577375438510027 309090098366063157765041)
                ·
                  refine ⟨231817573774547368323781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309090098366063157765041 231817573774547368323781)
                  ·
                    refine ⟨43465795082727631560709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 231817573774547368323781 43465795082727631560709)
                    ·
                      rfl

theorem cell22_126974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_126974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126974 prefixEnd_126974 := by exact prefixLift 126974
  have htrace : WordTrace (prefixWord ++ tailWord_126974) baseStart_126974 baseEnd_126974 := by
    simpa [prefixWord, tailWord_126974, baseEnd_126974] using wordTrace_append hprefix tailTrace_126974
  have hstable : (prefixWord ++ tailWord_126974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126974).length < 2 ^ (prefixWord ++ tailWord_126974).sum := by decide
  have hdescent : baseEnd_126974 < baseStart_126974 := by decide
  rcases family_descends (prefixWord ++ tailWord_126974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126989 : List Nat := [1, 7, 1, 2, 1, 1, 9]
def baseStart_126989 : Nat := 118140960795 + 126989 * 2 ^ 59
def prefixEnd_126989 : Nat := 4983230072969 + 3 ^ 40 * 126989 * 2
def baseEnd_126989 : Nat := 1610034440343429349469

theorem tailTrace_126989 : CollatzResearch.WordTrace tailWord_126989 prefixEnd_126989 1610034440343429349469 := by
  unfold tailWord_126989
  simp only [CollatzResearch.WordTrace]
  refine ⟨4631669336948015839640021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3087779557965343893093347 4631669336948015839640021)
  ·
    refine ⟨108554750084719121241563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 4631669336948015839640021 108554750084719121241563)
    ·
      refine ⟨162832125127078681862345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108554750084719121241563 162832125127078681862345)
      ·
        refine ⟨122124093845309011396759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162832125127078681862345 122124093845309011396759)
        ·
          refine ⟨183186140767963517095139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122124093845309011396759 183186140767963517095139)
          ·
            refine ⟨274779211151945275642709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183186140767963517095139 274779211151945275642709)
            ·
              refine ⟨1610034440343429349469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 274779211151945275642709 1610034440343429349469)
              ·
                rfl

theorem cell22_126989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 9].length) (baseStart_126989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_126989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_126989 prefixEnd_126989 := by exact prefixLift 126989
  have htrace : WordTrace (prefixWord ++ tailWord_126989) baseStart_126989 baseEnd_126989 := by
    simpa [prefixWord, tailWord_126989, baseEnd_126989] using wordTrace_append hprefix tailTrace_126989
  have hstable : (prefixWord ++ tailWord_126989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126989).length < 2 ^ (prefixWord ++ tailWord_126989).sum := by decide
  have hdescent : baseEnd_126989 < baseStart_126989 := by decide
  rcases family_descends (prefixWord ++ tailWord_126989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127004 : List Nat := [2, 2, 3, 1, 3, 1, 2, 4, 1, 3]
def baseStart_127004 : Nat := 118140960795 + 127004 * 2 ^ 59
def prefixEnd_127004 : Nat := 4983230072969 + 3 ^ 40 * 127004 * 2
def baseEnd_127004 : Nat := 43476064695817553310617

theorem tailTrace_127004 : CollatzResearch.WordTrace tailWord_127004 prefixEnd_127004 43476064695817553310617 := by
  unfold tailWord_127004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2316108215946836700718033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3088144287929115600957377 2316108215946836700718033)
  ·
    refine ⟨1737081161960127525538525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2316108215946836700718033 1737081161960127525538525)
    ·
      refine ⟨651405435735047822076947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1737081161960127525538525 651405435735047822076947)
      ·
        refine ⟨977108153602571733115421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651405435735047822076947 977108153602571733115421)
        ·
          refine ⟨366415557600964399918283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 977108153602571733115421 366415557600964399918283)
          ·
            refine ⟨549623336401446599877425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366415557600964399918283 549623336401446599877425)
            ·
              refine ⟨412217502301084949908069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549623336401446599877425 412217502301084949908069)
              ·
                refine ⟨77290781681453428107763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412217502301084949908069 77290781681453428107763)
                ·
                  refine ⟨115936172522180142161645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77290781681453428107763 115936172522180142161645)
                  ·
                    refine ⟨43476064695817553310617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115936172522180142161645 43476064695817553310617)
                    ·
                      rfl

theorem cell22_127004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_127004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127004 prefixEnd_127004 := by exact prefixLift 127004
  have htrace : WordTrace (prefixWord ++ tailWord_127004) baseStart_127004 baseEnd_127004 := by
    simpa [prefixWord, tailWord_127004, baseEnd_127004] using wordTrace_append hprefix tailTrace_127004
  have hstable : (prefixWord ++ tailWord_127004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127004).length < 2 ^ (prefixWord ++ tailWord_127004).sum := by decide
  have hdescent : baseEnd_127004 < baseStart_127004 := by decide
  rcases family_descends (prefixWord ++ tailWord_127004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127038 : List Nat := [4, 2, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_127038 : Nat := 118140960795 + 127038 * 2 ^ 59
def prefixEnd_127038 : Nat := 4983230072969 + 3 ^ 40 * 127038 * 2
def baseEnd_127038 : Nat := 43487703590652797960513

theorem tailTrace_127038 : CollatzResearch.WordTrace tailWord_127038 prefixEnd_127038 43487703590652797960513 := by
  unfold tailWord_127038
  simp only [CollatzResearch.WordTrace]
  refine ⟨579182064221312151021721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3088971009180331472115845 579182064221312151021721)
  ·
    refine ⟨434386548165984113266291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 579182064221312151021721 434386548165984113266291)
    ·
      refine ⟨651579822248976169899437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434386548165984113266291 651579822248976169899437)
      ·
        refine ⟨244342433343366063712289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651579822248976169899437 244342433343366063712289)
        ·
          refine ⟨183256825007524547784217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244342433343366063712289 183256825007524547784217)
          ·
            refine ⟨137442618755643410838163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183256825007524547784217 137442618755643410838163)
            ·
              refine ⟨206163928133465116257245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137442618755643410838163 206163928133465116257245)
              ·
                refine ⟨77311473050049418596467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206163928133465116257245 77311473050049418596467)
                ·
                  refine ⟨115967209575074127894701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77311473050049418596467 115967209575074127894701)
                  ·
                    refine ⟨43487703590652797960513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115967209575074127894701 43487703590652797960513)
                    ·
                      rfl

theorem cell22_127038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_127038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127038 prefixEnd_127038 := by exact prefixLift 127038
  have htrace : WordTrace (prefixWord ++ tailWord_127038) baseStart_127038 baseEnd_127038 := by
    simpa [prefixWord, tailWord_127038, baseEnd_127038] using wordTrace_append hprefix tailTrace_127038
  have hstable : (prefixWord ++ tailWord_127038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127038).length < 2 ^ (prefixWord ++ tailWord_127038).sum := by decide
  have hdescent : baseEnd_127038 < baseStart_127038 := by decide
  rcases family_descends (prefixWord ++ tailWord_127038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127090 : List Nat := [3, 2, 1, 2, 2, 2, 2, 8]
def baseStart_127090 : Nat := 118140960795 + 127090 * 2 ^ 59
def prefixEnd_127090 : Nat := 4983230072969 + 3 ^ 40 * 127090 * 2
def baseEnd_127090 : Nat := 4833944917037999517817

theorem tailTrace_127090 : CollatzResearch.WordTrace tailWord_127090 prefixEnd_127090 4833944917037999517817 := by
  unfold tailWord_127090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1158838277395527522266681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3090235406388073392711149 1158838277395527522266681)
  ·
    refine ⟨869128708046645641700011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1158838277395527522266681 869128708046645641700011)
    ·
      refine ⟨1303693062069968462550017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 869128708046645641700011 1303693062069968462550017)
      ·
        refine ⟨977769796552476346912513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1303693062069968462550017 977769796552476346912513)
        ·
          refine ⟨733327347414357260184385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 977769796552476346912513 733327347414357260184385)
          ·
            refine ⟨549995510560767945138289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733327347414357260184385 549995510560767945138289)
            ·
              refine ⟨412496632920575958853717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549995510560767945138289 412496632920575958853717)
              ·
                refine ⟨4833944917037999517817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 412496632920575958853717 4833944917037999517817)
                ·
                  rfl

theorem cell22_127090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_127090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127090 prefixEnd_127090 := by exact prefixLift 127090
  have htrace : WordTrace (prefixWord ++ tailWord_127090) baseStart_127090 baseEnd_127090 := by
    simpa [prefixWord, tailWord_127090, baseEnd_127090] using wordTrace_append hprefix tailTrace_127090
  have hstable : (prefixWord ++ tailWord_127090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127090).length < 2 ^ (prefixWord ++ tailWord_127090).sum := by decide
  have hdescent : baseEnd_127090 < baseStart_127090 := by decide
  rcases family_descends (prefixWord ++ tailWord_127090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127169 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 7]
def baseStart_127169 : Nat := 118140960795 + 127169 * 2 ^ 59
def prefixEnd_127169 : Nat := 4983230072969 + 3 ^ 40 * 127169 * 2
def baseEnd_127169 : Nat := 14510849189270707645037

theorem tailTrace_127169 : CollatzResearch.WordTrace tailWord_127169 prefixEnd_127169 14510849189270707645037 := by
  unfold tailWord_127169
  simp only [CollatzResearch.WordTrace]
  refine ⟨4638234476295906581192561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3092156317530604387461707 4638234476295906581192561)
  ·
    refine ⟨3478675857221929935894421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4638234476295906581192561 3478675857221929935894421)
    ·
      refine ⟨163062930807277965745051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3478675857221929935894421 163062930807277965745051)
      ·
        refine ⟨244594396210916948617577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163062930807277965745051 244594396210916948617577)
        ·
          refine ⟨183445797158187711463183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244594396210916948617577 183445797158187711463183)
          ·
            refine ⟨275168695737281567194775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183445797158187711463183 275168695737281567194775)
            ·
              refine ⟨412753043605922350792163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275168695737281567194775 412753043605922350792163)
              ·
                refine ⟨619129565408883526188245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412753043605922350792163 619129565408883526188245)
                ·
                  refine ⟨14510849189270707645037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 619129565408883526188245 14510849189270707645037)
                  ·
                    rfl

theorem cell22_127169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 7].length) (baseStart_127169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127169 prefixEnd_127169 := by exact prefixLift 127169
  have htrace : WordTrace (prefixWord ++ tailWord_127169) baseStart_127169 baseEnd_127169 := by
    simpa [prefixWord, tailWord_127169, baseEnd_127169] using wordTrace_append hprefix tailTrace_127169
  have hstable : (prefixWord ++ tailWord_127169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127169).length < 2 ^ (prefixWord ++ tailWord_127169).sum := by decide
  have hdescent : baseEnd_127169 < baseStart_127169 := by decide
  rcases family_descends (prefixWord ++ tailWord_127169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127212 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 6, 3]
def baseStart_127212 : Nat := 118140960795 + 127212 * 2 ^ 59
def prefixEnd_127212 : Nat := 4983230072969 + 3 ^ 40 * 127212 * 2
def baseEnd_127212 : Nat := 43547267346574344109979

theorem tailTrace_127212 : CollatzResearch.WordTrace tailWord_127212 prefixEnd_127212 43547267346574344109979 := by
  unfold tailWord_127212
  simp only [CollatzResearch.WordTrace]
  refine ⟨2319901407570062462503945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3093201876760083283338593 2319901407570062462503945)
  ·
    refine ⟨1739926055677546846877959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2319901407570062462503945 1739926055677546846877959)
    ·
      refine ⟨2609889083516320270316939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1739926055677546846877959 2609889083516320270316939)
      ·
        refine ⟨3914833625274480405475409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609889083516320270316939 3914833625274480405475409)
        ·
          refine ⟨2936125218955860304106557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3914833625274480405475409 2936125218955860304106557)
          ·
            refine ⟨1101046957108447614039959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2936125218955860304106557 1101046957108447614039959)
            ·
              refine ⟨1651570435662671421059939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101046957108447614039959 1651570435662671421059939)
              ·
                refine ⟨2477355653494007131589909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651570435662671421059939 2477355653494007131589909)
                ·
                  refine ⟨116126046257531584293277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2477355653494007131589909 116126046257531584293277)
                  ·
                    refine ⟨43547267346574344109979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116126046257531584293277 43547267346574344109979)
                    ·
                      rfl

theorem cell22_127212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_127212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127212 prefixEnd_127212 := by exact prefixLift 127212
  have htrace : WordTrace (prefixWord ++ tailWord_127212) baseStart_127212 baseEnd_127212 := by
    simpa [prefixWord, tailWord_127212, baseEnd_127212] using wordTrace_append hprefix tailTrace_127212
  have hstable : (prefixWord ++ tailWord_127212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127212).length < 2 ^ (prefixWord ++ tailWord_127212).sum := by decide
  have hdescent : baseEnd_127212 < baseStart_127212 := by decide
  rcases family_descends (prefixWord ++ tailWord_127212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127261 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_127261 : Nat := 118140960795 + 127261 * 2 ^ 59
def prefixEnd_127261 : Nat := 4983230072969 + 3 ^ 40 * 127261 * 2
def baseEnd_127261 : Nat := 43564041047954549634829

theorem tailTrace_127261 : CollatzResearch.WordTrace tailWord_127261 prefixEnd_127261 43564041047954549634829 := by
  unfold tailWord_127261
  simp only [CollatzResearch.WordTrace]
  refine ⟨4641589991962606293541637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3094393327975070862361091 4641589991962606293541637)
  ·
    refine ⟨870298123492988680039057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4641589991962606293541637 870298123492988680039057)
    ·
      refine ⟨652723592619741510029293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 870298123492988680039057 652723592619741510029293)
      ·
        refine ⟨244771347232403066260985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 652723592619741510029293 244771347232403066260985)
        ·
          refine ⟨183578510424302299695739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244771347232403066260985 183578510424302299695739)
          ·
            refine ⟨275367765636453449543609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183578510424302299695739 275367765636453449543609)
            ·
              refine ⟨206525824227340087157707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275367765636453449543609 206525824227340087157707)
              ·
                refine ⟨309788736341010130736561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206525824227340087157707 309788736341010130736561)
                ·
                  refine ⟨232341552255757598052421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309788736341010130736561 232341552255757598052421)
                  ·
                    refine ⟨43564041047954549634829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 232341552255757598052421 43564041047954549634829)
                    ·
                      rfl

theorem cell22_127261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_127261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127261 prefixEnd_127261 := by exact prefixLift 127261
  have htrace : WordTrace (prefixWord ++ tailWord_127261) baseStart_127261 baseEnd_127261 := by
    simpa [prefixWord, tailWord_127261, baseEnd_127261] using wordTrace_append hprefix tailTrace_127261
  have hstable : (prefixWord ++ tailWord_127261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127261).length < 2 ^ (prefixWord ++ tailWord_127261).sum := by decide
  have hdescent : baseEnd_127261 < baseStart_127261 := by decide
  rcases family_descends (prefixWord ++ tailWord_127261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127332 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 8]
def baseStart_127332 : Nat := 118140960795 + 127332 * 2 ^ 59
def prefixEnd_127332 : Nat := 4983230072969 + 3 ^ 40 * 127332 * 2
def baseEnd_127332 : Nat := 14529448599644677036537

theorem tailTrace_127332 : CollatzResearch.WordTrace tailWord_127332 prefixEnd_127332 14529448599644677036537 := by
  unfold tailWord_127332
  simp only [CollatzResearch.WordTrace]
  refine ⟨2322089787352692709688125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3096119716470256946250833 2322089787352692709688125)
  ·
    refine ⟨870783670257259766133047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2322089787352692709688125 870783670257259766133047)
    ·
      refine ⟨1306175505385889649199571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 870783670257259766133047 1306175505385889649199571)
      ·
        refine ⟨1959263258078834473799357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1306175505385889649199571 1959263258078834473799357)
        ·
          refine ⟨734723721779562927674759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1959263258078834473799357 734723721779562927674759)
          ·
            refine ⟨1102085582669344391512139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734723721779562927674759 1102085582669344391512139)
            ·
              refine ⟨1653128374004016587268209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102085582669344391512139 1653128374004016587268209)
              ·
                refine ⟨1239846280503012440451157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653128374004016587268209 1239846280503012440451157)
                ·
                  refine ⟨14529448599644677036537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1239846280503012440451157 14529448599644677036537)
                  ·
                    rfl

theorem cell22_127332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_127332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127332 prefixEnd_127332 := by exact prefixLift 127332
  have htrace : WordTrace (prefixWord ++ tailWord_127332) baseStart_127332 baseEnd_127332 := by
    simpa [prefixWord, tailWord_127332, baseEnd_127332] using wordTrace_append hprefix tailTrace_127332
  have hstable : (prefixWord ++ tailWord_127332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127332).length < 2 ^ (prefixWord ++ tailWord_127332).sum := by decide
  have hdescent : baseEnd_127332 < baseStart_127332 := by decide
  rcases family_descends (prefixWord ++ tailWord_127332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127349 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 6]
def baseStart_127349 : Nat := 118140960795 + 127349 * 2 ^ 59
def prefixEnd_127349 : Nat := 4983230072969 + 3 ^ 40 * 127349 * 2
def baseEnd_127349 : Nat := 14531388415450551144853

theorem tailTrace_127349 : CollatzResearch.WordTrace tailWord_127349 prefixEnd_127349 14531388415450551144853 := by
  unfold tailWord_127349
  simp only [CollatzResearch.WordTrace]
  refine ⟨4644799615643797322745101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3096533077095864881830067 4644799615643797322745101)
  ·
    refine ⟨1741799855866423996029413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4644799615643797322745101 1741799855866423996029413)
    ·
      refine ⟨326587472974954499255515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1741799855866423996029413 326587472974954499255515)
      ·
        refine ⟨489881209462431748883273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326587472974954499255515 489881209462431748883273)
        ·
          refine ⟨367410907096823811662455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489881209462431748883273 367410907096823811662455)
          ·
            refine ⟨551116360645235717493683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367410907096823811662455 551116360645235717493683)
            ·
              refine ⟨826674540967853576240525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551116360645235717493683 826674540967853576240525)
              ·
                refine ⟨310002952862945091090197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 826674540967853576240525 310002952862945091090197)
                ·
                  refine ⟨14531388415450551144853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 310002952862945091090197 14531388415450551144853)
                  ·
                    rfl

theorem cell22_127349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_127349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127349 prefixEnd_127349 := by exact prefixLift 127349
  have htrace : WordTrace (prefixWord ++ tailWord_127349) baseStart_127349 baseEnd_127349 := by
    simpa [prefixWord, tailWord_127349, baseEnd_127349] using wordTrace_append hprefix tailTrace_127349
  have hstable : (prefixWord ++ tailWord_127349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127349).length < 2 ^ (prefixWord ++ tailWord_127349).sum := by decide
  have hdescent : baseEnd_127349 < baseStart_127349 := by decide
  rcases family_descends (prefixWord ++ tailWord_127349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127400 : List Nat := [2, 1, 6, 1, 1, 2, 3, 2, 4]
def baseStart_127400 : Nat := 118140960795 + 127400 * 2 ^ 59
def prefixEnd_127400 : Nat := 4983230072969 + 3 ^ 40 * 127400 * 2
def baseEnd_127400 : Nat := 14537207862868173469801

theorem tailTrace_127400 : CollatzResearch.WordTrace tailWord_127400 prefixEnd_127400 14537207862868173469801 := by
  unfold tailWord_127400
  simp only [CollatzResearch.WordTrace]
  refine ⟨2323329869229516516425827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3097773158972688688567769 2323329869229516516425827)
  ·
    refine ⟨3484994803844274774638741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2323329869229516516425827 3484994803844274774638741)
    ·
      refine ⟨163359131430200380061191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3484994803844274774638741 163359131430200380061191)
      ·
        refine ⟨245038697145300570091787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163359131430200380061191 245038697145300570091787)
        ·
          refine ⟨367558045717950855137681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245038697145300570091787 367558045717950855137681)
          ·
            refine ⟨275668534288463141353261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367558045717950855137681 275668534288463141353261)
            ·
              refine ⟨103375700358173678007473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275668534288463141353261 103375700358173678007473)
              ·
                refine ⟨77531775268630258505605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103375700358173678007473 77531775268630258505605)
                ·
                  refine ⟨14537207862868173469801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77531775268630258505605 14537207862868173469801)
                  ·
                    rfl

theorem cell22_127400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 4].length) (baseStart_127400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127400 prefixEnd_127400 := by exact prefixLift 127400
  have htrace : WordTrace (prefixWord ++ tailWord_127400) baseStart_127400 baseEnd_127400 := by
    simpa [prefixWord, tailWord_127400, baseEnd_127400] using wordTrace_append hprefix tailTrace_127400
  have hstable : (prefixWord ++ tailWord_127400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127400).length < 2 ^ (prefixWord ++ tailWord_127400).sum := by decide
  have hdescent : baseEnd_127400 < baseStart_127400 := by decide
  rcases family_descends (prefixWord ++ tailWord_127400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127494 : List Nat := [6, 2, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_127494 : Nat := 118140960795 + 127494 * 2 ^ 59
def prefixEnd_127494 : Nat := 4983230072969 + 3 ^ 40 * 127494 * 2
def baseEnd_127494 : Nat := 43643801709619608559115

theorem tailTrace_127494 : CollatzResearch.WordTrace tailWord_127494 prefixEnd_127494 43643801709619608559115 := by
  unfold tailWord_127494
  simp only [CollatzResearch.WordTrace]
  refine ⟨145315256253702721461673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3100058800078991391182357 145315256253702721461673)
  ·
    refine ⟨108986442190277041096255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145315256253702721461673 108986442190277041096255)
    ·
      refine ⟨163479663285415561644383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108986442190277041096255 163479663285415561644383)
      ·
        refine ⟨245219494928123342466575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163479663285415561644383 245219494928123342466575)
        ·
          refine ⟨367829242392185013699863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245219494928123342466575 367829242392185013699863)
          ·
            refine ⟨551743863588277520549795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367829242392185013699863 551743863588277520549795)
            ·
              refine ⟨827615795382416280824693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551743863588277520549795 827615795382416280824693)
              ·
                refine ⟨77588980817101526327315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 827615795382416280824693 77588980817101526327315)
                ·
                  refine ⟨116383471225652289490973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77588980817101526327315 116383471225652289490973)
                  ·
                    refine ⟨43643801709619608559115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116383471225652289490973 43643801709619608559115)
                    ·
                      rfl

theorem cell22_127494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_127494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127494 prefixEnd_127494 := by exact prefixLift 127494
  have htrace : WordTrace (prefixWord ++ tailWord_127494) baseStart_127494 baseEnd_127494 := by
    simpa [prefixWord, tailWord_127494, baseEnd_127494] using wordTrace_append hprefix tailTrace_127494
  have hstable : (prefixWord ++ tailWord_127494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127494).length < 2 ^ (prefixWord ++ tailWord_127494).sum := by decide
  have hdescent : baseEnd_127494 < baseStart_127494 := by decide
  rcases family_descends (prefixWord ++ tailWord_127494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127544 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 2, 7]
def baseStart_127544 : Nat := 118140960795 + 127544 * 2 ^ 59
def prefixEnd_127544 : Nat := 4983230072969 + 3 ^ 40 * 127544 * 2
def baseEnd_127544 : Nat := 43660917731436144808961

theorem tailTrace_127544 : CollatzResearch.WordTrace tailWord_127544 prefixEnd_127544 43660917731436144808961 := by
  unfold tailWord_127544
  simp only [CollatzResearch.WordTrace]
  refine ⟨2325955924968672813046843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3101274566624897084062457 2325955924968672813046843)
  ·
    refine ⟨3488933887453009219570265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2325955924968672813046843 3488933887453009219570265)
    ·
      refine ⟨2616700415589756914677699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3488933887453009219570265 2616700415589756914677699)
      ·
        refine ⟨3925050623384635372016549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2616700415589756914677699 3925050623384635372016549)
        ·
          refine ⟨735946991884619132253103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3925050623384635372016549 735946991884619132253103)
          ·
            refine ⟨1103920487826928698379655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735946991884619132253103 1103920487826928698379655)
            ·
              refine ⟨1655880731740393047569483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103920487826928698379655 1655880731740393047569483)
              ·
                refine ⟨2483821097610589571354225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655880731740393047569483 2483821097610589571354225)
                ·
                  refine ⟨1862865823207942178515669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2483821097610589571354225 1862865823207942178515669)
                  ·
                    refine ⟨43660917731436144808961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1862865823207942178515669 43660917731436144808961)
                    ·
                      rfl

theorem cell22_127544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_127544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127544 prefixEnd_127544 := by exact prefixLift 127544
  have htrace : WordTrace (prefixWord ++ tailWord_127544) baseStart_127544 baseEnd_127544 := by
    simpa [prefixWord, tailWord_127544, baseEnd_127544] using wordTrace_append hprefix tailTrace_127544
  have hstable : (prefixWord ++ tailWord_127544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127544).length < 2 ^ (prefixWord ++ tailWord_127544).sum := by decide
  have hdescent : baseEnd_127544 < baseStart_127544 := by decide
  rcases family_descends (prefixWord ++ tailWord_127544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127546 : List Nat := [3, 1, 1, 1, 3, 3, 4, 6]
def baseStart_127546 : Nat := 118140960795 + 127546 * 2 ^ 59
def prefixEnd_127546 : Nat := 4983230072969 + 3 ^ 40 * 127546 * 2
def baseEnd_127546 : Nat := 4851289152478756250995

theorem tailTrace_127546 : CollatzResearch.WordTrace tailWord_127546 prefixEnd_127546 4851289152478756250995 := by
  unfold tailWord_127546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1162996198982524991916623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3101323197286733311777661 1162996198982524991916623)
  ·
    refine ⟨1744494298473787487874935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1162996198982524991916623 1744494298473787487874935)
    ·
      refine ⟨2616741447710681231812403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1744494298473787487874935 2616741447710681231812403)
      ·
        refine ⟨3925112171566021847718605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2616741447710681231812403 3925112171566021847718605)
        ·
          refine ⟨1471917064337258192894477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3925112171566021847718605 1471917064337258192894477)
          ·
            refine ⟨551968899126471822335429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1471917064337258192894477 551968899126471822335429)
            ·
              refine ⟨103494168586213466687893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 551968899126471822335429 103494168586213466687893)
              ·
                refine ⟨4851289152478756250995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103494168586213466687893 4851289152478756250995)
                ·
                  rfl

theorem cell22_127546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 6].length) (baseStart_127546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127546 prefixEnd_127546 := by exact prefixLift 127546
  have htrace : WordTrace (prefixWord ++ tailWord_127546) baseStart_127546 baseEnd_127546 := by
    simpa [prefixWord, tailWord_127546, baseEnd_127546] using wordTrace_append hprefix tailTrace_127546
  have hstable : (prefixWord ++ tailWord_127546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127546).length < 2 ^ (prefixWord ++ tailWord_127546).sum := by decide
  have hdescent : baseEnd_127546 < baseStart_127546 := by decide
  rcases family_descends (prefixWord ++ tailWord_127546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127715 : List Nat := [1, 1, 1, 7, 1, 3, 2, 6]
def baseStart_127715 : Nat := 118140960795 + 127715 * 2 ^ 59
def prefixEnd_127715 : Nat := 4983230072969 + 3 ^ 40 * 127715 * 2
def baseEnd_127715 : Nat := 4857717169560966531493

theorem tailTrace_127715 : CollatzResearch.WordTrace tailWord_127715 prefixEnd_127715 4857717169560966531493 := by
  unfold tailWord_127715
  simp only [CollatzResearch.WordTrace]
  refine ⟨4658148732317841830568599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3105432488211894553712399 4658148732317841830568599)
  ·
    refine ⟨6987223098476762745852899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4658148732317841830568599 6987223098476762745852899)
    ·
      refine ⟨10480834647715144118779349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6987223098476762745852899 10480834647715144118779349)
      ·
        refine ⟨245644562055823690283891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 10480834647715144118779349 245644562055823690283891)
        ·
          refine ⟨368466843083735535425837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245644562055823690283891 368466843083735535425837)
          ·
            refine ⟨138175066156400825784689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368466843083735535425837 138175066156400825784689)
            ·
              refine ⟨103631299617300619338517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138175066156400825784689 103631299617300619338517)
              ·
                refine ⟨4857717169560966531493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103631299617300619338517 4857717169560966531493)
                ·
                  rfl

theorem cell22_127715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 6].length) (baseStart_127715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127715 prefixEnd_127715 := by exact prefixLift 127715
  have htrace : WordTrace (prefixWord ++ tailWord_127715) baseStart_127715 baseEnd_127715 := by
    simpa [prefixWord, tailWord_127715, baseEnd_127715] using wordTrace_append hprefix tailTrace_127715
  have hstable : (prefixWord ++ tailWord_127715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127715).length < 2 ^ (prefixWord ++ tailWord_127715).sum := by decide
  have hdescent : baseEnd_127715 < baseStart_127715 := by decide
  rcases family_descends (prefixWord ++ tailWord_127715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127732 : List Nat := [2, 6, 1, 1, 2, 2, 8]
def baseStart_127732 : Nat := 118140960795 + 127732 * 2 ^ 59
def prefixEnd_127732 : Nat := 4983230072969 + 3 ^ 40 * 127732 * 2
def baseEnd_127732 : Nat := 1619454591609863744755

theorem tailTrace_127732 : CollatzResearch.WordTrace tailWord_127732 prefixEnd_127732 1619454591609863744755 := by
  unfold tailWord_127732
  simp only [CollatzResearch.WordTrace]
  refine ⟨2329384386628126866968725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3105845848837502489291633 2329384386628126866968725)
  ·
    refine ⟨109189893123193446889159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2329384386628126866968725 109189893123193446889159)
    ·
      refine ⟨163784839684790170333739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109189893123193446889159 163784839684790170333739)
      ·
        refine ⟨245677259527185255500609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163784839684790170333739 245677259527185255500609)
        ·
          refine ⟨184257944645388941625457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245677259527185255500609 184257944645388941625457)
          ·
            refine ⟨138193458484041706219093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184257944645388941625457 138193458484041706219093)
            ·
              refine ⟨1619454591609863744755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 138193458484041706219093 1619454591609863744755)
              ·
                rfl

theorem cell22_127732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 8].length) (baseStart_127732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127732 prefixEnd_127732 := by exact prefixLift 127732
  have htrace : WordTrace (prefixWord ++ tailWord_127732) baseStart_127732 baseEnd_127732 := by
    simpa [prefixWord, tailWord_127732, baseEnd_127732] using wordTrace_append hprefix tailTrace_127732
  have hstable : (prefixWord ++ tailWord_127732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127732).length < 2 ^ (prefixWord ++ tailWord_127732).sum := by decide
  have hdescent : baseEnd_127732 < baseStart_127732 := by decide
  rcases family_descends (prefixWord ++ tailWord_127732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127756 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_127756 : Nat := 118140960795 + 127756 * 2 ^ 59
def prefixEnd_127756 : Nat := 4983230072969 + 3 ^ 40 * 127756 * 2
def baseEnd_127756 : Nat := 43733489663938258508311

theorem tailTrace_127756 : CollatzResearch.WordTrace tailWord_127756 prefixEnd_127756 43733489663938258508311 := by
  unfold tailWord_127756
  simp only [CollatzResearch.WordTrace]
  refine ⟨2329822062584652916405561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3106429416779537221874081 2329822062584652916405561)
  ·
    refine ⟨1747366546938489687304171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2329822062584652916405561 1747366546938489687304171)
    ·
      refine ⟨2621049820407734530956257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1747366546938489687304171 2621049820407734530956257)
      ·
        refine ⟨1965787365305800898217193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2621049820407734530956257 1965787365305800898217193)
        ·
          refine ⟨1474340523979350673662895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1965787365305800898217193 1474340523979350673662895)
          ·
            refine ⟨2211510785969026010494343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474340523979350673662895 2211510785969026010494343)
            ·
              refine ⟨3317266178953539015741515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211510785969026010494343 3317266178953539015741515)
              ·
                refine ⟨4975899268430308523612273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3317266178953539015741515 4975899268430308523612273)
                ·
                  refine ⟨3731924451322731392709205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4975899268430308523612273 3731924451322731392709205)
                  ·
                    refine ⟨43733489663938258508311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3731924451322731392709205 43733489663938258508311)
                    ·
                      rfl

theorem cell22_127756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_127756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127756 prefixEnd_127756 := by exact prefixLift 127756
  have htrace : WordTrace (prefixWord ++ tailWord_127756) baseStart_127756 baseEnd_127756 := by
    simpa [prefixWord, tailWord_127756, baseEnd_127756] using wordTrace_append hprefix tailTrace_127756
  have hstable : (prefixWord ++ tailWord_127756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127756).length < 2 ^ (prefixWord ++ tailWord_127756).sum := by decide
  have hdescent : baseEnd_127756 < baseStart_127756 := by decide
  rcases family_descends (prefixWord ++ tailWord_127756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127798 : List Nat := [5, 1, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_127798 : Nat := 118140960795 + 127798 * 2 ^ 59
def prefixEnd_127798 : Nat := 4983230072969 + 3 ^ 40 * 127798 * 2
def baseEnd_127798 : Nat := 43747867122264148958183

theorem tailTrace_127798 : CollatzResearch.WordTrace tailWord_127798 prefixEnd_127798 43747867122264148958183 := by
  unfold tailWord_127798
  simp only [CollatzResearch.WordTrace]
  refine ⟨291323499438571687865003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3107450660678098003893365 291323499438571687865003)
  ·
    refine ⟨436985249157857531797505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291323499438571687865003 436985249157857531797505)
    ·
      refine ⟨327738936868393148848129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436985249157857531797505 327738936868393148848129)
      ·
        refine ⟨245804202651294861636097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327738936868393148848129 245804202651294861636097)
        ·
          refine ⟨184353151988471146227073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245804202651294861636097 184353151988471146227073)
          ·
            refine ⟨138264863991353359670305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184353151988471146227073 138264863991353359670305)
            ·
              refine ⟨103698647993515019752729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138264863991353359670305 103698647993515019752729)
              ·
                refine ⟨77773985995136264814547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103698647993515019752729 77773985995136264814547)
                ·
                  refine ⟨116660978992704397221821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77773985995136264814547 116660978992704397221821)
                  ·
                    refine ⟨43747867122264148958183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116660978992704397221821 43747867122264148958183)
                    ·
                      rfl

theorem cell22_127798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_127798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127798 prefixEnd_127798 := by exact prefixLift 127798
  have htrace : WordTrace (prefixWord ++ tailWord_127798) baseStart_127798 baseEnd_127798 := by
    simpa [prefixWord, tailWord_127798, baseEnd_127798] using wordTrace_append hprefix tailTrace_127798
  have hstable : (prefixWord ++ tailWord_127798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127798).length < 2 ^ (prefixWord ++ tailWord_127798).sum := by decide
  have hdescent : baseEnd_127798 < baseStart_127798 := by decide
  rcases family_descends (prefixWord ++ tailWord_127798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127820 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 1, 5]
def baseStart_127820 : Nat := 118140960795 + 127820 * 2 ^ 59
def prefixEnd_127820 : Nat := 4983230072969 + 3 ^ 40 * 127820 * 2
def baseEnd_127820 : Nat := 43755398171863424908115

theorem tailTrace_127820 : CollatzResearch.WordTrace tailWord_127820 prefixEnd_127820 43755398171863424908115 := by
  unfold tailWord_127820
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330989198468722381570457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3107985597958296508760609 2330989198468722381570457)
  ·
    refine ⟨1748241898851541786177843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2330989198468722381570457 1748241898851541786177843)
    ·
      refine ⟨2622362848277312679266765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1748241898851541786177843 2622362848277312679266765)
      ·
        refine ⟨983386068103992254725037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2622362848277312679266765 983386068103992254725037)
        ·
          refine ⟨368769775538997095521889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 983386068103992254725037 368769775538997095521889)
          ·
            refine ⟨276577331654247821641417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368769775538997095521889 276577331654247821641417)
            ·
              refine ⟨207432998740685866231063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276577331654247821641417 207432998740685866231063)
              ·
                refine ⟨311149498111028799346595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207432998740685866231063 311149498111028799346595)
                ·
                  refine ⟨466724247166543199019893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311149498111028799346595 466724247166543199019893)
                  ·
                    refine ⟨43755398171863424908115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 466724247166543199019893 43755398171863424908115)
                    ·
                      rfl

theorem cell22_127820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_127820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127820 prefixEnd_127820 := by exact prefixLift 127820
  have htrace : WordTrace (prefixWord ++ tailWord_127820) baseStart_127820 baseEnd_127820 := by
    simpa [prefixWord, tailWord_127820, baseEnd_127820] using wordTrace_append hprefix tailTrace_127820
  have hstable : (prefixWord ++ tailWord_127820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127820).length < 2 ^ (prefixWord ++ tailWord_127820).sum := by decide
  have hdescent : baseEnd_127820 < baseStart_127820 := by decide
  rcases family_descends (prefixWord ++ tailWord_127820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127865 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 3, 3]
def baseStart_127865 : Nat := 118140960795 + 127865 * 2 ^ 59
def prefixEnd_127865 : Nat := 4983230072969 + 3 ^ 40 * 127865 * 2
def baseEnd_127865 : Nat := 43770802591498307532977

theorem tailTrace_127865 : CollatzResearch.WordTrace tailWord_127865 prefixEnd_127865 43770802591498307532977 := by
  unfold tailWord_127865
  simp only [CollatzResearch.WordTrace]
  refine ⟨4663619681774417448529049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3109079787849611632352699 4663619681774417448529049)
  ·
    refine ⟨3497714761330813086396787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4663619681774417448529049 3497714761330813086396787)
    ·
      refine ⟨5246572141996219629595181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3497714761330813086396787 5246572141996219629595181)
      ·
        refine ⟨1967464553248582361098193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5246572141996219629595181 1967464553248582361098193)
        ·
          refine ⟨1475598414936436770823645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1967464553248582361098193 1475598414936436770823645)
          ·
            refine ⟨553349405601163789058867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1475598414936436770823645 553349405601163789058867)
            ·
              refine ⟨830024108401745683588301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553349405601163789058867 830024108401745683588301)
              ·
                refine ⟨311259040650654631345613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 830024108401745683588301 311259040650654631345613)
                ·
                  refine ⟨116722140243995486754605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311259040650654631345613 116722140243995486754605)
                  ·
                    refine ⟨43770802591498307532977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116722140243995486754605 43770802591498307532977)
                    ·
                      rfl

theorem cell22_127865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 3].length) (baseStart_127865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127865 prefixEnd_127865 := by exact prefixLift 127865
  have htrace : WordTrace (prefixWord ++ tailWord_127865) baseStart_127865 baseEnd_127865 := by
    simpa [prefixWord, tailWord_127865, baseEnd_127865] using wordTrace_append hprefix tailTrace_127865
  have hstable : (prefixWord ++ tailWord_127865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127865).length < 2 ^ (prefixWord ++ tailWord_127865).sum := by decide
  have hdescent : baseEnd_127865 < baseStart_127865 := by decide
  rcases family_descends (prefixWord ++ tailWord_127865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127882 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 3, 3]
def baseStart_127882 : Nat := 118140960795 + 127882 * 2 ^ 59
def prefixEnd_127882 : Nat := 4983230072969 + 3 ^ 40 * 127882 * 2
def baseEnd_127882 : Nat := 43776622038915929857925

theorem tailTrace_127882 : CollatzResearch.WordTrace tailWord_127882 prefixEnd_127882 43776622038915929857925 := by
  unfold tailWord_127882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1166059930678207337974475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3109493148475219567931933 1166059930678207337974475)
  ·
    refine ⟨1749089896017311006961713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1166059930678207337974475 1749089896017311006961713)
    ·
      refine ⟨1311817422012983255221285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1749089896017311006961713 1311817422012983255221285)
      ·
        refine ⟨245965766627434360353991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1311817422012983255221285 245965766627434360353991)
        ·
          refine ⟨368948649941151540530987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245965766627434360353991 368948649941151540530987)
          ·
            refine ⟨553422974911727310796481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368948649941151540530987 553422974911727310796481)
            ·
              refine ⟨415067231183795483097361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553422974911727310796481 415067231183795483097361)
              ·
                refine ⟨311300423387846612323021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415067231183795483097361 311300423387846612323021)
                ·
                  refine ⟨116737658770442479621133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311300423387846612323021 116737658770442479621133)
                  ·
                    refine ⟨43776622038915929857925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116737658770442479621133 43776622038915929857925)
                    ·
                      rfl

theorem cell22_127882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_127882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127882 prefixEnd_127882 := by exact prefixLift 127882
  have htrace : WordTrace (prefixWord ++ tailWord_127882) baseStart_127882 baseEnd_127882 := by
    simpa [prefixWord, tailWord_127882, baseEnd_127882] using wordTrace_append hprefix tailTrace_127882
  have hstable : (prefixWord ++ tailWord_127882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127882).length < 2 ^ (prefixWord ++ tailWord_127882).sum := by decide
  have hdescent : baseEnd_127882 < baseStart_127882 := by decide
  rcases family_descends (prefixWord ++ tailWord_127882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127923 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 6]
def baseStart_127923 : Nat := 118140960795 + 127923 * 2 ^ 59
def prefixEnd_127923 : Nat := 4983230072969 + 3 ^ 40 * 127923 * 2
def baseEnd_127923 : Nat := 14596885725601829860933

theorem tailTrace_127923 : CollatzResearch.WordTrace tailWord_127923 prefixEnd_127923 14596885725601829860933 := by
  unfold tailWord_127923
  simp only [CollatzResearch.WordTrace]
  refine ⟨4665735115564293354140423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3110490077042862236093615 4665735115564293354140423)
  ·
    refine ⟨6998602673346440031210635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4665735115564293354140423 6998602673346440031210635)
    ·
      refine ⟨10497904010019660046815953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6998602673346440031210635 10497904010019660046815953)
      ·
        refine ⟨7873428007514745035111965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10497904010019660046815953 7873428007514745035111965)
        ·
          refine ⟨2952535502818029388166987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7873428007514745035111965 2952535502818029388166987)
          ·
            refine ⟨4428803254227044082250481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952535502818029388166987 4428803254227044082250481)
            ·
              refine ⟨3321602440670283061687861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4428803254227044082250481 3321602440670283061687861)
              ·
                refine ⟨311400228812839037033237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3321602440670283061687861 311400228812839037033237)
                ·
                  refine ⟨14596885725601829860933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 311400228812839037033237 14596885725601829860933)
                  ·
                    rfl

theorem cell22_127923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 6].length) (baseStart_127923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127923 prefixEnd_127923 := by exact prefixLift 127923
  have htrace : WordTrace (prefixWord ++ tailWord_127923) baseStart_127923 baseEnd_127923 := by
    simpa [prefixWord, tailWord_127923, baseEnd_127923] using wordTrace_append hprefix tailTrace_127923
  have hstable : (prefixWord ++ tailWord_127923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127923).length < 2 ^ (prefixWord ++ tailWord_127923).sum := by decide
  have hdescent : baseEnd_127923 < baseStart_127923 := by decide
  rcases family_descends (prefixWord ++ tailWord_127923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127925 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_127925 : Nat := 118140960795 + 127925 * 2 ^ 59
def prefixEnd_127925 : Nat := 4983230072969 + 3 ^ 40 * 127925 * 2
def baseEnd_127925 : Nat := 43791341817678151032793

theorem tailTrace_127925 : CollatzResearch.WordTrace tailWord_127925 prefixEnd_127925 43791341817678151032793 := by
  unfold tailWord_127925
  simp only [CollatzResearch.WordTrace]
  refine ⟨4665808061557047695713229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3110538707704698463808819 4665808061557047695713229)
  ·
    refine ⟨1749678023083892885892461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4665808061557047695713229 1749678023083892885892461)
    ·
      refine ⟨656129258656459832209673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1749678023083892885892461 656129258656459832209673)
      ·
        refine ⟨492096943992344874157255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656129258656459832209673 492096943992344874157255)
        ·
          refine ⟨738145415988517311235883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492096943992344874157255 738145415988517311235883)
          ·
            refine ⟨1107218123982775966853825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738145415988517311235883 1107218123982775966853825)
            ·
              refine ⟨830413592987081975140369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107218123982775966853825 830413592987081975140369)
              ·
                refine ⟨622810194740311481355277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 830413592987081975140369 622810194740311481355277)
                ·
                  refine ⟨233553823027616805508229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 622810194740311481355277 233553823027616805508229)
                  ·
                    refine ⟨43791341817678151032793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 233553823027616805508229 43791341817678151032793)
                    ·
                      rfl

theorem cell22_127925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_127925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127925 prefixEnd_127925 := by exact prefixLift 127925
  have htrace : WordTrace (prefixWord ++ tailWord_127925) baseStart_127925 baseEnd_127925 := by
    simpa [prefixWord, tailWord_127925, baseEnd_127925] using wordTrace_append hprefix tailTrace_127925
  have hstable : (prefixWord ++ tailWord_127925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127925).length < 2 ^ (prefixWord ++ tailWord_127925).sum := by decide
  have hdescent : baseEnd_127925 < baseStart_127925 := by decide
  rcases family_descends (prefixWord ++ tailWord_127925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127985 : List Nat := [1, 2, 2, 2, 4, 1, 3, 7]
def baseStart_127985 : Nat := 118140960795 + 127985 * 2 ^ 59
def prefixEnd_127985 : Nat := 4983230072969 + 3 ^ 40 * 127985 * 2
def baseEnd_127985 : Nat := 4867986782650888281401

theorem tailTrace_127985 : CollatzResearch.WordTrace tailWord_127985 prefixEnd_127985 4867986782650888281401 := by
  unfold tailWord_127985
  simp only [CollatzResearch.WordTrace]
  refine ⟨4667996441339677942897409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3111997627559785295264939 4667996441339677942897409)
  ·
    refine ⟨3500997331004758457173057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4667996441339677942897409 3500997331004758457173057)
    ·
      refine ⟨2625747998253568842879793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3500997331004758457173057 2625747998253568842879793)
      ·
        refine ⟨1969310998690176632159845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2625747998253568842879793 1969310998690176632159845)
        ·
          refine ⟨369245812254408118529971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1969310998690176632159845 369245812254408118529971)
          ·
            refine ⟨553868718381612177794957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369245812254408118529971 553868718381612177794957)
            ·
              refine ⟨207700769393104566673109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 553868718381612177794957 207700769393104566673109)
              ·
                refine ⟨4867986782650888281401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 207700769393104566673109 4867986782650888281401)
                ·
                  rfl

theorem cell22_127985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 7].length) (baseStart_127985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_127985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_127985 prefixEnd_127985 := by exact prefixLift 127985
  have htrace : WordTrace (prefixWord ++ tailWord_127985) baseStart_127985 baseEnd_127985 := by
    simpa [prefixWord, tailWord_127985, baseEnd_127985] using wordTrace_append hprefix tailTrace_127985
  have hstable : (prefixWord ++ tailWord_127985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127985).length < 2 ^ (prefixWord ++ tailWord_127985).sum := by decide
  have hdescent : baseEnd_127985 < baseStart_127985 := by decide
  rcases family_descends (prefixWord ++ tailWord_127985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128034 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_128034 : Nat := 118140960795 + 128034 * 2 ^ 59
def prefixEnd_128034 : Nat := 4983230072969 + 3 ^ 40 * 128034 * 2
def baseEnd_128034 : Nat := 43828654745238200057459

theorem tailTrace_128034 : CollatzResearch.WordTrace tailWord_128034 prefixEnd_128034 43828654745238200057459 := by
  unfold tailWord_128034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1167445904540539827857789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3113189078774772874287437 1167445904540539827857789)
  ·
    refine ⟨437792214202702435446671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1167445904540539827857789 437792214202702435446671)
    ·
      refine ⟨656688321304053653170007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437792214202702435446671 656688321304053653170007)
      ·
        refine ⟨985032481956080479755011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656688321304053653170007 985032481956080479755011)
        ·
          refine ⟨1477548722934120719632517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985032481956080479755011 1477548722934120719632517)
          ·
            refine ⟨277040385550147634931097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1477548722934120719632517 277040385550147634931097)
            ·
              refine ⟨207780289162610726198323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277040385550147634931097 207780289162610726198323)
              ·
                refine ⟨311670433743916089297485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207780289162610726198323 311670433743916089297485)
                ·
                  refine ⟨116876412653968533486557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311670433743916089297485 116876412653968533486557)
                  ·
                    refine ⟨43828654745238200057459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116876412653968533486557 43828654745238200057459)
                    ·
                      rfl

theorem cell22_128034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_128034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128034 prefixEnd_128034 := by exact prefixLift 128034
  have htrace : WordTrace (prefixWord ++ tailWord_128034) baseStart_128034 baseEnd_128034 := by
    simpa [prefixWord, tailWord_128034, baseEnd_128034] using wordTrace_append hprefix tailTrace_128034
  have hstable : (prefixWord ++ tailWord_128034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128034).length < 2 ^ (prefixWord ++ tailWord_128034).sum := by decide
  have hdescent : baseEnd_128034 < baseStart_128034 := by decide
  rcases family_descends (prefixWord ++ tailWord_128034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128090 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_128090 : Nat := 118140960795 + 128090 * 2 ^ 59
def prefixEnd_128090 : Nat := 4983230072969 + 3 ^ 40 * 128090 * 2
def baseEnd_128090 : Nat := 43847824689672720657287

theorem tailTrace_128090 : CollatzResearch.WordTrace tailWord_128090 prefixEnd_128090 43847824689672720657287 := by
  unfold tailWord_128090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1167956526489820218867431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3114550737306187250313149 1167956526489820218867431)
  ·
    refine ⟨1751934789734730328301147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1167956526489820218867431 1751934789734730328301147)
    ·
      refine ⟨2627902184602095492451721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1751934789734730328301147 2627902184602095492451721)
      ·
        refine ⟨1970926638451571619338791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2627902184602095492451721 1970926638451571619338791)
        ·
          refine ⟨2956389957677357429008187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1970926638451571619338791 2956389957677357429008187)
          ·
            refine ⟨4434584936516036143512281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956389957677357429008187 4434584936516036143512281)
            ·
              refine ⟨3325938702387027107634211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4434584936516036143512281 3325938702387027107634211)
              ·
                refine ⟨4988908053580540661451317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3325938702387027107634211 4988908053580540661451317)
                ·
                  refine ⟨467710130023175687011061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4988908053580540661451317 467710130023175687011061)
                  ·
                    refine ⟨43847824689672720657287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 467710130023175687011061 43847824689672720657287)
                    ·
                      rfl

theorem cell22_128090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_128090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128090 prefixEnd_128090 := by exact prefixLift 128090
  have htrace : WordTrace (prefixWord ++ tailWord_128090) baseStart_128090 baseEnd_128090 := by
    simpa [prefixWord, tailWord_128090, baseEnd_128090] using wordTrace_append hprefix tailTrace_128090
  have hstable : (prefixWord ++ tailWord_128090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128090).length < 2 ^ (prefixWord ++ tailWord_128090).sum := by decide
  have hdescent : baseEnd_128090 < baseStart_128090 := by decide
  rcases family_descends (prefixWord ++ tailWord_128090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128120 : List Nat := [2, 1, 2, 1, 1, 1, 6, 8]
def baseStart_128120 : Nat := 118140960795 + 128120 * 2 ^ 59
def prefixEnd_128120 : Nat := 4983230072969 + 3 ^ 40 * 128120 * 2
def baseEnd_128120 : Nat := 4873121589195849156355

theorem tailTrace_128120 : CollatzResearch.WordTrace tailWord_128120 prefixEnd_128120 4873121589195849156355 := by
  unfold tailWord_128120
  simp only [CollatzResearch.WordTrace]
  refine ⟨2336460147925297999530907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3115280197233730666041209 2336460147925297999530907)
  ·
    refine ⟨3504690221887946999296361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2336460147925297999530907 3504690221887946999296361)
    ·
      refine ⟨2628517666415960249472271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3504690221887946999296361 2628517666415960249472271)
      ·
        refine ⟨3942776499623940374208407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2628517666415960249472271 3942776499623940374208407)
        ·
          refine ⟨5914164749435910561312611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3942776499623940374208407 5914164749435910561312611)
          ·
            refine ⟨8871247124153865841968917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914164749435910561312611 8871247124153865841968917)
            ·
              refine ⟨415839708944712461342293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8871247124153865841968917 415839708944712461342293)
              ·
                refine ⟨4873121589195849156355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 415839708944712461342293 4873121589195849156355)
                ·
                  rfl

theorem cell22_128120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 8].length) (baseStart_128120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128120 prefixEnd_128120 := by exact prefixLift 128120
  have htrace : WordTrace (prefixWord ++ tailWord_128120) baseStart_128120 baseEnd_128120 := by
    simpa [prefixWord, tailWord_128120, baseEnd_128120] using wordTrace_append hprefix tailTrace_128120
  have hstable : (prefixWord ++ tailWord_128120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128120).length < 2 ^ (prefixWord ++ tailWord_128120).sum := by decide
  have hdescent : baseEnd_128120 < baseStart_128120 := by decide
  rcases family_descends (prefixWord ++ tailWord_128120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128154 : List Nat := [3, 1, 1, 5, 1, 3, 1, 7]
def baseStart_128154 : Nat := 118140960795 + 128154 * 2 ^ 59
def prefixEnd_128154 : Nat := 4983230072969 + 3 ^ 40 * 128154 * 2
def baseEnd_128154 : Nat := 4874414799733098561899

theorem tailTrace_128154 : CollatzResearch.WordTrace tailWord_128154 prefixEnd_128154 4874414799733098561899 := by
  unfold tailWord_128154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1168540094431854951449879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3116106918484946537199677 1168540094431854951449879)
  ·
    refine ⟨1752810141647782427174819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1168540094431854951449879 1752810141647782427174819)
    ·
      refine ⟨2629215212471673640762229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1752810141647782427174819 2629215212471673640762229)
      ·
        refine ⟨246488926169219403821459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2629215212471673640762229 246488926169219403821459)
        ·
          refine ⟨369733389253829105732189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246488926169219403821459 369733389253829105732189)
          ·
            refine ⟨138650020970185914649571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369733389253829105732189 138650020970185914649571)
            ·
              refine ⟨207975031455278871974357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138650020970185914649571 207975031455278871974357)
              ·
                refine ⟨4874414799733098561899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 207975031455278871974357 4874414799733098561899)
                ·
                  rfl

theorem cell22_128154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 7].length) (baseStart_128154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128154 prefixEnd_128154 := by exact prefixLift 128154
  have htrace : WordTrace (prefixWord ++ tailWord_128154) baseStart_128154 baseEnd_128154 := by
    simpa [prefixWord, tailWord_128154, baseEnd_128154] using wordTrace_append hprefix tailTrace_128154
  have hstable : (prefixWord ++ tailWord_128154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128154).length < 2 ^ (prefixWord ++ tailWord_128154).sum := by decide
  have hdescent : baseEnd_128154 < baseStart_128154 := by decide
  rcases family_descends (prefixWord ++ tailWord_128154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128173 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_128173 : Nat := 118140960795 + 128173 * 2 ^ 59
def prefixEnd_128173 : Nat := 4983230072969 + 3 ^ 40 * 128173 * 2
def baseEnd_128173 : Nat := 43876237285888170832033

theorem tailTrace_128173 : CollatzResearch.WordTrace tailWord_128173 prefixEnd_128173 43876237285888170832033 := by
  unfold tailWord_128173
  simp only [CollatzResearch.WordTrace]
  refine ⟨4674853364658586050741173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3116568909772390700494115 4674853364658586050741173)
  ·
    refine ⟨438267502936742442256985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4674853364658586050741173 438267502936742442256985)
    ·
      refine ⟨328700627202556831692739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438267502936742442256985 328700627202556831692739)
      ·
        refine ⟨493050940803835247539109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328700627202556831692739 493050940803835247539109)
        ·
          refine ⟨92447051400719108913583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 493050940803835247539109 92447051400719108913583)
          ·
            refine ⟨138670577101078663370375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92447051400719108913583 138670577101078663370375)
            ·
              refine ⟨208005865651617995055563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138670577101078663370375 208005865651617995055563)
              ·
                refine ⟨312008798477426992583345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208005865651617995055563 312008798477426992583345)
                ·
                  refine ⟨234006598858070244437509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312008798477426992583345 234006598858070244437509)
                  ·
                    refine ⟨43876237285888170832033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234006598858070244437509 43876237285888170832033)
                    ·
                      rfl

theorem cell22_128173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_128173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128173 prefixEnd_128173 := by exact prefixLift 128173
  have htrace : WordTrace (prefixWord ++ tailWord_128173) baseStart_128173 baseEnd_128173 := by
    simpa [prefixWord, tailWord_128173, baseEnd_128173] using wordTrace_append hprefix tailTrace_128173
  have hstable : (prefixWord ++ tailWord_128173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128173).length < 2 ^ (prefixWord ++ tailWord_128173).sum := by decide
  have hdescent : baseEnd_128173 < baseStart_128173 := by decide
  rcases family_descends (prefixWord ++ tailWord_128173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128216 : List Nat := [2, 1, 2, 2, 5, 1, 3, 1, 5]
def baseStart_128216 : Nat := 118140960795 + 128216 * 2 ^ 59
def prefixEnd_128216 : Nat := 4983230072969 + 3 ^ 40 * 128216 * 2
def baseEnd_128216 : Nat := 14630319021550130668967

theorem tailTrace_128216 : CollatzResearch.WordTrace tailWord_128216 prefixEnd_128216 14630319021550130668967 := by
  unfold tailWord_128216
  simp only [CollatzResearch.WordTrace]
  refine ⟨2338210851751402197278251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3117614469001869596371001 2338210851751402197278251)
  ·
    refine ⟨3507316277627103295917377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2338210851751402197278251 3507316277627103295917377)
    ·
      refine ⟨2630487208220327471938033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3507316277627103295917377 2630487208220327471938033)
      ·
        refine ⟨1972865406165245603953525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2630487208220327471938033 1972865406165245603953525)
        ·
          refine ⟨184956131827991775370643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1972865406165245603953525 184956131827991775370643)
          ·
            refine ⟨277434197741987663055965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184956131827991775370643 277434197741987663055965)
            ·
              refine ⟨104037824153245373645987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277434197741987663055965 104037824153245373645987)
              ·
                refine ⟨156056736229868060468981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104037824153245373645987 156056736229868060468981)
                ·
                  refine ⟨14630319021550130668967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156056736229868060468981 14630319021550130668967)
                  ·
                    rfl

theorem cell22_128216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 5].length) (baseStart_128216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128216 prefixEnd_128216 := by exact prefixLift 128216
  have htrace : WordTrace (prefixWord ++ tailWord_128216) baseStart_128216 baseEnd_128216 := by
    simpa [prefixWord, tailWord_128216, baseEnd_128216] using wordTrace_append hprefix tailTrace_128216
  have hstable : (prefixWord ++ tailWord_128216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128216).length < 2 ^ (prefixWord ++ tailWord_128216).sum := by decide
  have hdescent : baseEnd_128216 < baseStart_128216 := by decide
  rcases family_descends (prefixWord ++ tailWord_128216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128259 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 4, 3]
def baseStart_128259 : Nat := 118140960795 + 128259 * 2 ^ 59
def prefixEnd_128259 : Nat := 4983230072969 + 3 ^ 40 * 128259 * 2
def baseEnd_128259 : Nat := 43905676843412613181769

theorem tailTrace_128259 : CollatzResearch.WordTrace tailWord_128259 prefixEnd_128259 43905676843412613181769 := by
  unfold tailWord_128259
  simp only [CollatzResearch.WordTrace]
  refine ⟨4677990042347022738371831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3118660028231348492247887 4677990042347022738371831)
  ·
    refine ⟨7016985063520534107557747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4677990042347022738371831 7016985063520534107557747)
    ·
      refine ⟨10525477595280801161336621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7016985063520534107557747 10525477595280801161336621)
      ·
        refine ⟨3947054098230300435501233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10525477595280801161336621 3947054098230300435501233)
        ·
          refine ⟨2960290573672725326625925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3947054098230300435501233 2960290573672725326625925)
          ·
            refine ⟨555054482563635998742361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2960290573672725326625925 555054482563635998742361)
            ·
              refine ⟨416290861922726999056771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555054482563635998742361 416290861922726999056771)
              ·
                refine ⟨624436292884090498585157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416290861922726999056771 624436292884090498585157)
                ·
                  refine ⟨117081804915766968484717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624436292884090498585157 117081804915766968484717)
                  ·
                    refine ⟨43905676843412613181769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117081804915766968484717 43905676843412613181769)
                    ·
                      rfl

theorem cell22_128259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 3].length) (baseStart_128259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128259 prefixEnd_128259 := by exact prefixLift 128259
  have htrace : WordTrace (prefixWord ++ tailWord_128259) baseStart_128259 baseEnd_128259 := by
    simpa [prefixWord, tailWord_128259, baseEnd_128259] using wordTrace_append hprefix tailTrace_128259
  have hstable : (prefixWord ++ tailWord_128259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128259).length < 2 ^ (prefixWord ++ tailWord_128259).sum := by decide
  have hdescent : baseEnd_128259 < baseStart_128259 := by decide
  rcases family_descends (prefixWord ++ tailWord_128259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128261 : List Nat := [1, 3, 1, 1, 2, 1, 7, 2, 4]
def baseStart_128261 : Nat := 118140960795 + 128261 * 2 ^ 59
def prefixEnd_128261 : Nat := 4983230072969 + 3 ^ 40 * 128261 * 2
def baseEnd_128261 : Nat := 14635453828095091543921

theorem tailTrace_128261 : CollatzResearch.WordTrace tailWord_128261 prefixEnd_128261 14635453828095091543921 := by
  unfold tailWord_128261
  simp only [CollatzResearch.WordTrace]
  refine ⟨4678062988339777079944637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3118708658893184719963091 4678062988339777079944637)
  ·
    refine ⟨1754273620627416404979239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4678062988339777079944637 1754273620627416404979239)
    ·
      refine ⟨2631410430941124607468859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1754273620627416404979239 2631410430941124607468859)
      ·
        refine ⟨3947115646411686911203289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2631410430941124607468859 3947115646411686911203289)
        ·
          refine ⟨2960336734808765183402467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3947115646411686911203289 2960336734808765183402467)
          ·
            refine ⟨4440505102213147775103701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960336734808765183402467 4440505102213147775103701)
            ·
              refine ⟨104074338333120650978993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4440505102213147775103701 104074338333120650978993)
              ·
                refine ⟨78055753749840488234245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104074338333120650978993 78055753749840488234245)
                ·
                  refine ⟨14635453828095091543921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78055753749840488234245 14635453828095091543921)
                  ·
                    rfl

theorem cell22_128261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_128261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128261 prefixEnd_128261 := by exact prefixLift 128261
  have htrace : WordTrace (prefixWord ++ tailWord_128261) baseStart_128261 baseEnd_128261 := by
    simpa [prefixWord, tailWord_128261, baseEnd_128261] using wordTrace_append hprefix tailTrace_128261
  have hstable : (prefixWord ++ tailWord_128261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128261).length < 2 ^ (prefixWord ++ tailWord_128261).sum := by decide
  have hdescent : baseEnd_128261 < baseStart_128261 := by decide
  rcases family_descends (prefixWord ++ tailWord_128261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128334 : List Nat := [4, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_128334 : Nat := 118140960795 + 128334 * 2 ^ 59
def prefixEnd_128334 : Nat := 4983230072969 + 3 ^ 40 * 128334 * 2
def baseEnd_128334 : Nat := 14643783625379139185513

theorem tailTrace_128334 : CollatzResearch.WordTrace tailWord_128334 prefixEnd_128334 14643783625379139185513 := by
  unfold tailWord_128334
  simp only [CollatzResearch.WordTrace]
  refine ⟨585090689634413818419007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3120483678050207031568037 585090689634413818419007)
  ·
    refine ⟨877636034451620727628511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 585090689634413818419007 877636034451620727628511)
    ·
      refine ⟨1316454051677431091442767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 877636034451620727628511 1316454051677431091442767)
      ·
        refine ⟨1974681077516146637164151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316454051677431091442767 1974681077516146637164151)
        ·
          refine ⟨2962021616274219955746227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974681077516146637164151 2962021616274219955746227)
          ·
            refine ⟨4443032424411329933619341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962021616274219955746227 4443032424411329933619341)
            ·
              refine ⟨1666137159154248725107253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4443032424411329933619341 1666137159154248725107253)
              ·
                refine ⟨156200358670710817978805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1666137159154248725107253 156200358670710817978805)
                ·
                  refine ⟨14643783625379139185513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156200358670710817978805 14643783625379139185513)
                  ·
                    rfl

theorem cell22_128334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_128334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128334 prefixEnd_128334 := by exact prefixLift 128334
  have htrace : WordTrace (prefixWord ++ tailWord_128334) baseStart_128334 baseEnd_128334 := by
    simpa [prefixWord, tailWord_128334, baseEnd_128334] using wordTrace_append hprefix tailTrace_128334
  have hstable : (prefixWord ++ tailWord_128334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128334).length < 2 ^ (prefixWord ++ tailWord_128334).sum := by decide
  have hdescent : baseEnd_128334 < baseStart_128334 := by decide
  rcases family_descends (prefixWord ++ tailWord_128334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128379 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 6]
def baseStart_128379 : Nat := 118140960795 + 128379 * 2 ^ 59
def prefixEnd_128379 : Nat := 4983230072969 + 3 ^ 40 * 128379 * 2
def baseEnd_128379 : Nat := 14648918431924100060467

theorem tailTrace_128379 : CollatzResearch.WordTrace tailWord_128379 prefixEnd_128379 14648918431924100060467 := by
  unfold tailWord_128379
  simp only [CollatzResearch.WordTrace]
  refine ⟨4682366801912283232740191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3121577867941522155160127 4682366801912283232740191)
  ·
    refine ⟨7023550202868424849110287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4682366801912283232740191 7023550202868424849110287)
    ·
      refine ⟨10535325304302637273665431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7023550202868424849110287 10535325304302637273665431)
      ·
        refine ⟨15802987956453955910498147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10535325304302637273665431 15802987956453955910498147)
        ·
          refine ⟨23704481934680933865747221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15802987956453955910498147 23704481934680933865747221)
          ·
            refine ⟨1111147590688168774956901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23704481934680933865747221 1111147590688168774956901)
            ·
              refine ⟨208340173254031645304419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1111147590688168774956901 208340173254031645304419)
              ·
                refine ⟨312510259881047467956629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208340173254031645304419 312510259881047467956629)
                ·
                  refine ⟨14648918431924100060467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 312510259881047467956629 14648918431924100060467)
                  ·
                    rfl

theorem cell22_128379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 6].length) (baseStart_128379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128379 prefixEnd_128379 := by exact prefixLift 128379
  have htrace : WordTrace (prefixWord ++ tailWord_128379) baseStart_128379 baseEnd_128379 := by
    simpa [prefixWord, tailWord_128379, baseEnd_128379] using wordTrace_append hprefix tailTrace_128379
  have hstable : (prefixWord ++ tailWord_128379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128379).length < 2 ^ (prefixWord ++ tailWord_128379).sum := by decide
  have hdescent : baseEnd_128379 < baseStart_128379 := by decide
  rcases family_descends (prefixWord ++ tailWord_128379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128409 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 1, 6]
def baseStart_128409 : Nat := 118140960795 + 128409 * 2 ^ 59
def prefixEnd_128409 : Nat := 4983230072969 + 3 ^ 40 * 128409 * 2
def baseEnd_128409 : Nat := 43957024908862221931309

theorem tailTrace_128409 : CollatzResearch.WordTrace tailWord_128409 prefixEnd_128409 43957024908862221931309 := by
  unfold tailWord_128409
  simp only [CollatzResearch.WordTrace]
  refine ⟨4683460991803598356332281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3122307327869065570888187 4683460991803598356332281)
  ·
    refine ⟨3512595743852698767249211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4683460991803598356332281 3512595743852698767249211)
    ·
      refine ⟨5268893615779048150873817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3512595743852698767249211 5268893615779048150873817)
      ·
        refine ⟨3951670211834286113155363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5268893615779048150873817 3951670211834286113155363)
        ·
          refine ⟨5927505317751429169733045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3951670211834286113155363 5927505317751429169733045)
          ·
            refine ⟨555703623539196484662473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5927505317751429169733045 555703623539196484662473)
            ·
              refine ⟨416777717654397363496855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555703623539196484662473 416777717654397363496855)
              ·
                refine ⟨625166576481596045245283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416777717654397363496855 625166576481596045245283)
                ·
                  refine ⟨937749864722394067867925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 625166576481596045245283 937749864722394067867925)
                  ·
                    refine ⟨43957024908862221931309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 937749864722394067867925 43957024908862221931309)
                    ·
                      rfl

theorem cell22_128409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_128409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128409 prefixEnd_128409 := by exact prefixLift 128409
  have htrace : WordTrace (prefixWord ++ tailWord_128409) baseStart_128409 baseEnd_128409 := by
    simpa [prefixWord, tailWord_128409, baseEnd_128409] using wordTrace_append hprefix tailTrace_128409
  have hstable : (prefixWord ++ tailWord_128409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128409).length < 2 ^ (prefixWord ++ tailWord_128409).sum := by decide
  have hdescent : baseEnd_128409 < baseStart_128409 := by decide
  rcases family_descends (prefixWord ++ tailWord_128409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128413 : List Nat := [1, 4, 2, 1, 3, 1, 3, 3, 4]
def baseStart_128413 : Nat := 118140960795 + 128413 * 2 ^ 59
def prefixEnd_128413 : Nat := 4983230072969 + 3 ^ 40 * 128413 * 2
def baseEnd_128413 : Nat := 14652798063535848277099

theorem tailTrace_128413 : CollatzResearch.WordTrace tailWord_128413 prefixEnd_128413 14652798063535848277099 := by
  unfold tailWord_128413
  simp only [CollatzResearch.WordTrace]
  refine ⟨4683606883789107039477893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3122404589192738026318595 4683606883789107039477893)
  ·
    refine ⟨878176290710457569902105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4683606883789107039477893 878176290710457569902105)
    ·
      refine ⟨658632218032843177426579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 878176290710457569902105 658632218032843177426579)
      ·
        refine ⟨987948327049264766139869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658632218032843177426579 987948327049264766139869)
        ·
          refine ⟨370480622643474287302451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 987948327049264766139869 370480622643474287302451)
          ·
            refine ⟨555720933965211430953677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370480622643474287302451 555720933965211430953677)
            ·
              refine ⟨208395350236954286607629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 555720933965211430953677 208395350236954286607629)
              ·
                refine ⟨78148256338857857477861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208395350236954286607629 78148256338857857477861)
                ·
                  refine ⟨14652798063535848277099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78148256338857857477861 14652798063535848277099)
                  ·
                    rfl

theorem cell22_128413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_128413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128413 prefixEnd_128413 := by exact prefixLift 128413
  have htrace : WordTrace (prefixWord ++ tailWord_128413) baseStart_128413 baseEnd_128413 := by
    simpa [prefixWord, tailWord_128413, baseEnd_128413] using wordTrace_append hprefix tailTrace_128413
  have hstable : (prefixWord ++ tailWord_128413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128413).length < 2 ^ (prefixWord ++ tailWord_128413).sum := by decide
  have hdescent : baseEnd_128413 < baseStart_128413 := by decide
  rcases family_descends (prefixWord ++ tailWord_128413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128441 : List Nat := [1, 2, 1, 4, 4, 1, 2, 7]
def baseStart_128441 : Nat := 118140960795 + 128441 * 2 ^ 59
def prefixEnd_128441 : Nat := 4983230072969 + 3 ^ 40 * 128441 * 2
def baseEnd_128441 : Nat := 4885331018091645014579

theorem tailTrace_128441 : CollatzResearch.WordTrace tailWord_128441 prefixEnd_128441 4885331018091645014579 := by
  unfold tailWord_128441
  simp only [CollatzResearch.WordTrace]
  refine ⟨4684628127687667821497177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3123085418458445214331451 4684628127687667821497177)
  ·
    refine ⟨3513471095765750866122883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4684628127687667821497177 3513471095765750866122883)
    ·
      refine ⟨5270206643648626299184325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3513471095765750866122883 5270206643648626299184325)
      ·
        refine ⟨988163745684117431097061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5270206643648626299184325 988163745684117431097061)
        ·
          refine ⟨185280702315772018330699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 988163745684117431097061 185280702315772018330699)
          ·
            refine ⟨277921053473658027496049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185280702315772018330699 277921053473658027496049)
            ·
              refine ⟨208440790105243520622037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277921053473658027496049 208440790105243520622037)
              ·
                refine ⟨4885331018091645014579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 208440790105243520622037 4885331018091645014579)
                ·
                  rfl

theorem cell22_128441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 7].length) (baseStart_128441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128441 prefixEnd_128441 := by exact prefixLift 128441
  have htrace : WordTrace (prefixWord ++ tailWord_128441) baseStart_128441 baseEnd_128441 := by
    simpa [prefixWord, tailWord_128441, baseEnd_128441] using wordTrace_append hprefix tailTrace_128441
  have hstable : (prefixWord ++ tailWord_128441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128441).length < 2 ^ (prefixWord ++ tailWord_128441).sum := by decide
  have hdescent : baseEnd_128441 < baseStart_128441 := by decide
  rcases family_descends (prefixWord ++ tailWord_128441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128456 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 5, 3]
def baseStart_128456 : Nat := 118140960795 + 128456 * 2 ^ 59
def prefixEnd_128456 : Nat := 4983230072969 + 3 ^ 40 * 128456 * 2
def baseEnd_128456 : Nat := 43973113969369766006165

theorem tailTrace_128456 : CollatzResearch.WordTrace tailWord_128456 prefixEnd_128456 43973113969369766006165 := by
  unfold tailWord_128456
  simp only [CollatzResearch.WordTrace]
  refine ⟨2342587611316662691646611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3123450148422216922195481 2342587611316662691646611)
  ·
    refine ⟨3513881416974994037469917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2342587611316662691646611 3513881416974994037469917)
    ·
      refine ⟨1317705531365622764051219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3513881416974994037469917 1317705531365622764051219)
      ·
        refine ⟨1976558297048434146076829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317705531365622764051219 1976558297048434146076829)
        ·
          refine ⟨741209361393162804778811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1976558297048434146076829 741209361393162804778811)
          ·
            refine ⟨1111814042089744207168217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741209361393162804778811 1111814042089744207168217)
            ·
              refine ⟨833860531567308155376163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1111814042089744207168217 833860531567308155376163)
              ·
                refine ⟨1250790797350962233064245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833860531567308155376163 1250790797350962233064245)
                ·
                  refine ⟨117261637251652709349773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1250790797350962233064245 117261637251652709349773)
                  ·
                    refine ⟨43973113969369766006165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117261637251652709349773 43973113969369766006165)
                    ·
                      rfl

theorem cell22_128456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_128456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128456 prefixEnd_128456 := by exact prefixLift 128456
  have htrace : WordTrace (prefixWord ++ tailWord_128456) baseStart_128456 baseEnd_128456 := by
    simpa [prefixWord, tailWord_128456, baseEnd_128456] using wordTrace_append hprefix tailTrace_128456
  have hstable : (prefixWord ++ tailWord_128456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128456).length < 2 ^ (prefixWord ++ tailWord_128456).sum := by decide
  have hdescent : baseEnd_128456 < baseStart_128456 := by decide
  rcases family_descends (prefixWord ++ tailWord_128456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128484 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_128484 : Nat := 118140960795 + 128484 * 2 ^ 59
def prefixEnd_128484 : Nat := 4983230072969 + 3 ^ 40 * 128484 * 2
def baseEnd_128484 : Nat := 43982698941587026306079

theorem tailTrace_128484 : CollatzResearch.WordTrace tailWord_128484 prefixEnd_128484 43982698941587026306079 := by
  unfold tailWord_128484
  simp only [CollatzResearch.WordTrace]
  refine ⟨2343098233265943082656253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3124130977687924110208337 2343098233265943082656253)
  ·
    refine ⟨878661837474728655996095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2343098233265943082656253 878661837474728655996095)
    ·
      refine ⟨1317992756212092983994143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878661837474728655996095 1317992756212092983994143)
      ·
        refine ⟨1976989134318139475991215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317992756212092983994143 1976989134318139475991215)
        ·
          refine ⟨2965483701477209213986823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976989134318139475991215 2965483701477209213986823)
          ·
            refine ⟨4448225552215813820980235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965483701477209213986823 4448225552215813820980235)
            ·
              refine ⟨6672338328323720731470353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448225552215813820980235 6672338328323720731470353)
              ·
                refine ⟨5004253746242790548602765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6672338328323720731470353 5004253746242790548602765)
                ·
                  refine ⟨1876595154841046455726037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5004253746242790548602765 1876595154841046455726037)
                  ·
                    refine ⟨43982698941587026306079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1876595154841046455726037 43982698941587026306079)
                    ·
                      rfl

theorem cell22_128484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_128484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128484 prefixEnd_128484 := by exact prefixLift 128484
  have htrace : WordTrace (prefixWord ++ tailWord_128484) baseStart_128484 baseEnd_128484 := by
    simpa [prefixWord, tailWord_128484, baseEnd_128484] using wordTrace_append hprefix tailTrace_128484
  have hstable : (prefixWord ++ tailWord_128484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128484).length < 2 ^ (prefixWord ++ tailWord_128484).sum := by decide
  have hdescent : baseEnd_128484 < baseStart_128484 := by decide
  rcases family_descends (prefixWord ++ tailWord_128484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128533 : List Nat := [1, 3, 2, 1, 3, 3, 1, 3, 1, 4]
def baseStart_128533 : Nat := 118140960795 + 128533 * 2 ^ 59
def prefixEnd_128533 : Nat := 4983230072969 + 3 ^ 40 * 128533 * 2
def baseEnd_128533 : Nat := 43999472642967231830929

theorem tailTrace_128533 : CollatzResearch.WordTrace tailWord_128533 prefixEnd_128533 43999472642967231830929 := by
  unfold tailWord_128533
  simp only [CollatzResearch.WordTrace]
  refine ⟨4687983643354367533846253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3125322428902911689230835 4687983643354367533846253)
  ·
    refine ⟨1757993866257887825192345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4687983643354367533846253 1757993866257887825192345)
    ·
      refine ⟨1318495399693415868894259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1757993866257887825192345 1318495399693415868894259)
      ·
        refine ⟨1977743099540123803341389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1318495399693415868894259 1977743099540123803341389)
        ·
          refine ⟨741653662327546426253021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1977743099540123803341389 741653662327546426253021)
          ·
            refine ⟨278120123372829909844883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 741653662327546426253021 278120123372829909844883)
            ·
              refine ⟨417180185059244864767325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278120123372829909844883 417180185059244864767325)
              ·
                refine ⟨156442569397216824287747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417180185059244864767325 156442569397216824287747)
                ·
                  refine ⟨234663854095825236431621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156442569397216824287747 234663854095825236431621)
                  ·
                    refine ⟨43999472642967231830929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234663854095825236431621 43999472642967231830929)
                    ·
                      rfl

theorem cell22_128533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_128533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128533 prefixEnd_128533 := by exact prefixLift 128533
  have htrace : WordTrace (prefixWord ++ tailWord_128533) baseStart_128533 baseEnd_128533 := by
    simpa [prefixWord, tailWord_128533, baseEnd_128533] using wordTrace_append hprefix tailTrace_128533
  have hstable : (prefixWord ++ tailWord_128533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128533).length < 2 ^ (prefixWord ++ tailWord_128533).sum := by decide
  have hdescent : baseEnd_128533 < baseStart_128533 := by decide
  rcases family_descends (prefixWord ++ tailWord_128533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128546 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_128546 : Nat := 118140960795 + 128546 * 2 ^ 59
def prefixEnd_128546 : Nat := 4983230072969 + 3 ^ 40 * 128546 * 2
def baseEnd_128546 : Nat := 44003922808639531255889

theorem tailTrace_128546 : CollatzResearch.WordTrace tailWord_128546 prefixEnd_128546 44003922808639531255889 := by
  unfold tailWord_128546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1172114448076817688517373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3125638528204847169379661 1172114448076817688517373)
  ·
    refine ⟨439542918028806633194015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1172114448076817688517373 439542918028806633194015)
    ·
      refine ⟨659314377043209949791023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439542918028806633194015 659314377043209949791023)
      ·
        refine ⟨988971565564814924686535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659314377043209949791023 988971565564814924686535)
        ·
          refine ⟨1483457348347222387029803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988971565564814924686535 1483457348347222387029803)
          ·
            refine ⟨2225186022520833580544705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483457348347222387029803 2225186022520833580544705)
            ·
              refine ⟨1668889516890625185408529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2225186022520833580544705 1668889516890625185408529)
              ·
                refine ⟨1251667137667968889056397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1668889516890625185408529 1251667137667968889056397)
                ·
                  refine ⟨469375176625488333396149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251667137667968889056397 469375176625488333396149)
                  ·
                    refine ⟨44003922808639531255889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 469375176625488333396149 44003922808639531255889)
                    ·
                      rfl

theorem cell22_128546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_128546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128546 prefixEnd_128546 := by exact prefixLift 128546
  have htrace : WordTrace (prefixWord ++ tailWord_128546) baseStart_128546 baseEnd_128546 := by
    simpa [prefixWord, tailWord_128546, baseEnd_128546] using wordTrace_append hprefix tailTrace_128546
  have hstable : (prefixWord ++ tailWord_128546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128546).length < 2 ^ (prefixWord ++ tailWord_128546).sum := by decide
  have hdescent : baseEnd_128546 < baseStart_128546 := by decide
  rcases family_descends (prefixWord ++ tailWord_128546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128563 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 1, 5]
def baseStart_128563 : Nat := 118140960795 + 128563 * 2 ^ 59
def prefixEnd_128563 : Nat := 4983230072969 + 3 ^ 40 * 128563 * 2
def baseEnd_128563 : Nat := 44009742256057153580837

theorem tailTrace_128563 : CollatzResearch.WordTrace tailWord_128563 prefixEnd_128563 44009742256057153580837 := by
  unfold tailWord_128563
  simp only [CollatzResearch.WordTrace]
  refine ⟨4689077833245682657438343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3126051888830455104958895 4689077833245682657438343)
  ·
    refine ⟨7033616749868523986157515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4689077833245682657438343 7033616749868523986157515)
    ·
      refine ⟨10550425124802785979236273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7033616749868523986157515 10550425124802785979236273)
      ·
        refine ⟨7912818843602089484427205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10550425124802785979236273 7912818843602089484427205)
        ·
          refine ⟨1483653533175391778330101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7912818843602089484427205 1483653533175391778330101)
          ·
            refine ⟨139092518735192979218447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1483653533175391778330101 139092518735192979218447)
            ·
              refine ⟨208638778102789468827671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139092518735192979218447 208638778102789468827671)
              ·
                refine ⟨312958167154184203241507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208638778102789468827671 312958167154184203241507)
                ·
                  refine ⟨469437250731276304862261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312958167154184203241507 469437250731276304862261)
                  ·
                    refine ⟨44009742256057153580837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 469437250731276304862261 44009742256057153580837)
                    ·
                      rfl

theorem cell22_128563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 5].length) (baseStart_128563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128563 prefixEnd_128563 := by exact prefixLift 128563
  have htrace : WordTrace (prefixWord ++ tailWord_128563) baseStart_128563 baseEnd_128563 := by
    simpa [prefixWord, tailWord_128563, baseEnd_128563] using wordTrace_append hprefix tailTrace_128563
  have hstable : (prefixWord ++ tailWord_128563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128563).length < 2 ^ (prefixWord ++ tailWord_128563).sum := by decide
  have hdescent : baseEnd_128563 < baseStart_128563 := by decide
  rcases family_descends (prefixWord ++ tailWord_128563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128636 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_128636 : Nat := 118140960795 + 128636 * 2 ^ 59
def prefixEnd_128636 : Nat := 4983230072969 + 3 ^ 40 * 128636 * 2
def baseEnd_128636 : Nat := 44034731647909296505613

theorem tailTrace_128636 : CollatzResearch.WordTrace tailWord_128636 prefixEnd_128636 44034731647909296505613 := by
  unfold tailWord_128636
  simp only [CollatzResearch.WordTrace]
  refine ⟨2345870180990608062422881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3127826907987477416563841 2345870180990608062422881)
  ·
    refine ⟨1759402635742956046817161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2345870180990608062422881 1759402635742956046817161)
    ·
      refine ⟨1319551976807217035112871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1759402635742956046817161 1319551976807217035112871)
      ·
        refine ⟨1979327965210825552669307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1319551976807217035112871 1979327965210825552669307)
        ·
          refine ⟨2968991947816238329003961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979327965210825552669307 2968991947816238329003961)
          ·
            refine ⟨2226743960862178746752971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2968991947816238329003961 2226743960862178746752971)
            ·
              refine ⟨3340115941293268120129457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226743960862178746752971 3340115941293268120129457)
              ·
                refine ⟨2505086955969951090097093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340115941293268120129457 2505086955969951090097093)
                ·
                  refine ⟨469703804244365829393205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2505086955969951090097093 469703804244365829393205)
                  ·
                    refine ⟨44034731647909296505613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 469703804244365829393205 44034731647909296505613)
                    ·
                      rfl

theorem cell22_128636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_128636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128636 prefixEnd_128636 := by exact prefixLift 128636
  have htrace : WordTrace (prefixWord ++ tailWord_128636) baseStart_128636 baseEnd_128636 := by
    simpa [prefixWord, tailWord_128636, baseEnd_128636] using wordTrace_append hprefix tailTrace_128636
  have hstable : (prefixWord ++ tailWord_128636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128636).length < 2 ^ (prefixWord ++ tailWord_128636).sum := by decide
  have hdescent : baseEnd_128636 < baseStart_128636 := by decide
  rcases family_descends (prefixWord ++ tailWord_128636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128670 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_128670 : Nat := 118140960795 + 128670 * 2 ^ 59
def prefixEnd_128670 : Nat := 4983230072969 + 3 ^ 40 * 128670 * 2
def baseEnd_128670 : Nat := 44046370542744541155509

theorem tailTrace_128670 : CollatzResearch.WordTrace tailWord_128670 prefixEnd_128670 44046370542744541155509 := by
  unfold tailWord_128670
  simp only [CollatzResearch.WordTrace]
  refine ⟨586622555482254991447933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3128653629238693287722309 586622555482254991447933)
  ·
    refine ⟨219983458305845621792975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 586622555482254991447933 219983458305845621792975)
    ·
      refine ⟨329975187458768432689463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219983458305845621792975 329975187458768432689463)
      ·
        refine ⟨494962781188152649034195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329975187458768432689463 494962781188152649034195)
        ·
          refine ⟨742444171782228973551293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494962781188152649034195 742444171782228973551293)
          ·
            refine ⟨278416564418335865081735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 742444171782228973551293 278416564418335865081735)
            ·
              refine ⟨417624846627503797622603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278416564418335865081735 417624846627503797622603)
              ·
                refine ⟨626437269941255696433905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417624846627503797622603 626437269941255696433905)
                ·
                  refine ⟨469827952455941772325429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626437269941255696433905 469827952455941772325429)
                  ·
                    refine ⟨44046370542744541155509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 469827952455941772325429 44046370542744541155509)
                    ·
                      rfl

theorem cell22_128670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_128670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128670 prefixEnd_128670 := by exact prefixLift 128670
  have htrace : WordTrace (prefixWord ++ tailWord_128670) baseStart_128670 baseEnd_128670 := by
    simpa [prefixWord, tailWord_128670, baseEnd_128670] using wordTrace_append hprefix tailTrace_128670
  have hstable : (prefixWord ++ tailWord_128670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128670).length < 2 ^ (prefixWord ++ tailWord_128670).sum := by decide
  have hdescent : baseEnd_128670 < baseStart_128670 := by decide
  rcases family_descends (prefixWord ++ tailWord_128670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128685 : List Nat := [1, 5, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_128685 : Nat := 118140960795 + 128685 * 2 ^ 59
def prefixEnd_128685 : Nat := 4983230072969 + 3 ^ 40 * 128685 * 2
def baseEnd_128685 : Nat := 44051505349289502030463

theorem tailTrace_128685 : CollatzResearch.WordTrace tailWord_128685 prefixEnd_128685 44051505349289502030463 := by
  unfold tailWord_128685
  simp only [CollatzResearch.WordTrace]
  refine ⟨4693527538803697493379509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3129018359202464995586339 4693527538803697493379509)
  ·
    refine ⟨440018206762846640004329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4693527538803697493379509 440018206762846640004329)
    ·
      refine ⟨330013655072134980003247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440018206762846640004329 330013655072134980003247)
      ·
        refine ⟨495020482608202470004871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330013655072134980003247 495020482608202470004871)
        ·
          refine ⟨742530723912303705007307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495020482608202470004871 742530723912303705007307)
          ·
            refine ⟨1113796085868455557510961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742530723912303705007307 1113796085868455557510961)
            ·
              refine ⟨835347064401341668133221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1113796085868455557510961 835347064401341668133221)
              ·
                refine ⟨156627574575251562774979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 835347064401341668133221 156627574575251562774979)
                ·
                  refine ⟨234941361862877344162469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156627574575251562774979 234941361862877344162469)
                  ·
                    refine ⟨44051505349289502030463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234941361862877344162469 44051505349289502030463)
                    ·
                      rfl

theorem cell22_128685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_128685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128685 prefixEnd_128685 := by exact prefixLift 128685
  have htrace : WordTrace (prefixWord ++ tailWord_128685) baseStart_128685 baseEnd_128685 := by
    simpa [prefixWord, tailWord_128685, baseEnd_128685] using wordTrace_append hprefix tailTrace_128685
  have hstable : (prefixWord ++ tailWord_128685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128685).length < 2 ^ (prefixWord ++ tailWord_128685).sum := by decide
  have hdescent : baseEnd_128685 < baseStart_128685 := by decide
  rcases family_descends (prefixWord ++ tailWord_128685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128698 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_128698 : Nat := 118140960795 + 128698 * 2 ^ 59
def prefixEnd_128698 : Nat := 4983230072969 + 3 ^ 40 * 128698 * 2
def baseEnd_128698 : Nat := 44055955514961801455423

theorem tailTrace_128698 : CollatzResearch.WordTrace tailWord_128698 prefixEnd_128698 44055955514961801455423 := by
  unfold tailWord_128698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1173500421939150178400687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3129334458504400475735165 1173500421939150178400687)
  ·
    refine ⟨1760250632908725267601031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1173500421939150178400687 1760250632908725267601031)
    ·
      refine ⟨2640375949363087901401547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1760250632908725267601031 2640375949363087901401547)
      ·
        refine ⟨3960563924044631852102321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640375949363087901401547 3960563924044631852102321)
        ·
          refine ⟨2970422943033473889076741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3960563924044631852102321 2970422943033473889076741)
          ·
            refine ⟨556954301818776354201889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2970422943033473889076741 556954301818776354201889)
            ·
              refine ⟨417715726364082265651417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556954301818776354201889 417715726364082265651417)
              ·
                refine ⟨313286794773061699238563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417715726364082265651417 313286794773061699238563)
                ·
                  refine ⟨469930192159592548857845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313286794773061699238563 469930192159592548857845)
                  ·
                    refine ⟨44055955514961801455423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 469930192159592548857845 44055955514961801455423)
                    ·
                      rfl

theorem cell22_128698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_128698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128698 prefixEnd_128698 := by exact prefixLift 128698
  have htrace : WordTrace (prefixWord ++ tailWord_128698) baseStart_128698 baseEnd_128698 := by
    simpa [prefixWord, tailWord_128698, baseEnd_128698] using wordTrace_append hprefix tailTrace_128698
  have hstable : (prefixWord ++ tailWord_128698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128698).length < 2 ^ (prefixWord ++ tailWord_128698).sum := by decide
  have hdescent : baseEnd_128698 < baseStart_128698 := by decide
  rcases family_descends (prefixWord ++ tailWord_128698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128700 : List Nat := [2, 2, 2, 3, 1, 2, 1, 5, 4]
def baseStart_128700 : Nat := 118140960795 + 128700 * 2 ^ 59
def prefixEnd_128700 : Nat := 4983230072969 + 3 ^ 40 * 128700 * 2
def baseEnd_128700 : Nat := 14685546718611487635139

theorem tailTrace_128700 : CollatzResearch.WordTrace tailWord_128700 prefixEnd_128700 14685546718611487635139 := by
  unfold tailWord_128700
  simp only [CollatzResearch.WordTrace]
  refine ⟨2347037316874677527587777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3129383089166236703450369 2347037316874677527587777)
  ·
    refine ⟨1760277987656008145690833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2347037316874677527587777 1760277987656008145690833)
    ·
      refine ⟨1320208490742006109268125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1760277987656008145690833 1320208490742006109268125)
      ·
        refine ⟨495078184028252290975547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1320208490742006109268125 495078184028252290975547)
        ·
          refine ⟨742617276042378436463321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495078184028252290975547 742617276042378436463321)
          ·
            refine ⟨556962957031783827347491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742617276042378436463321 556962957031783827347491)
            ·
              refine ⟨835444435547675741021237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556962957031783827347491 835444435547675741021237)
              ·
                refine ⟨78322915832594600720741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 835444435547675741021237 78322915832594600720741)
                ·
                  refine ⟨14685546718611487635139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78322915832594600720741 14685546718611487635139)
                  ·
                    rfl

theorem cell22_128700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_128700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128700 prefixEnd_128700 := by exact prefixLift 128700
  have htrace : WordTrace (prefixWord ++ tailWord_128700) baseStart_128700 baseEnd_128700 := by
    simpa [prefixWord, tailWord_128700, baseEnd_128700] using wordTrace_append hprefix tailTrace_128700
  have hstable : (prefixWord ++ tailWord_128700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128700).length < 2 ^ (prefixWord ++ tailWord_128700).sum := by decide
  have hdescent : baseEnd_128700 < baseStart_128700 := by decide
  rcases family_descends (prefixWord ++ tailWord_128700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128702 : List Nat := [4, 2, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_128702 : Nat := 118140960795 + 128702 * 2 ^ 59
def prefixEnd_128702 : Nat := 4983230072969 + 3 ^ 40 * 128702 * 2
def baseEnd_128702 : Nat := 44057324796707124355411

theorem tailTrace_128702 : CollatzResearch.WordTrace tailWord_128702 prefixEnd_128702 44057324796707124355411 := by
  unfold tailWord_128702
  simp only [CollatzResearch.WordTrace]
  refine ⟨586768447467763674593545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3129431719828072931165573 586768447467763674593545)
  ·
    refine ⟨440076335600822755945159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 586768447467763674593545 440076335600822755945159)
    ·
      refine ⟨660114503401234133917739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440076335600822755945159 660114503401234133917739)
      ·
        refine ⟨990171755101851200876609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660114503401234133917739 990171755101851200876609)
        ·
          refine ⟨742628816326388400657457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990171755101851200876609 742628816326388400657457)
          ·
            refine ⟨556971612244791300493093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742628816326388400657457 556971612244791300493093)
            ·
              refine ⟨104432177295898368842455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 556971612244791300493093 104432177295898368842455)
              ·
                refine ⟨156648265943847553263683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104432177295898368842455 156648265943847553263683)
                ·
                  refine ⟨234972398915771329895525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156648265943847553263683 234972398915771329895525)
                  ·
                    refine ⟨44057324796707124355411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234972398915771329895525 44057324796707124355411)
                    ·
                      rfl

theorem cell22_128702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_128702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128702 prefixEnd_128702 := by exact prefixLift 128702
  have htrace : WordTrace (prefixWord ++ tailWord_128702) baseStart_128702 baseEnd_128702 := by
    simpa [prefixWord, tailWord_128702, baseEnd_128702] using wordTrace_append hprefix tailTrace_128702
  have hstable : (prefixWord ++ tailWord_128702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128702).length < 2 ^ (prefixWord ++ tailWord_128702).sum := by decide
  have hdescent : baseEnd_128702 < baseStart_128702 := by decide
  rcases family_descends (prefixWord ++ tailWord_128702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128706 : List Nat := [3, 5, 1, 2, 1, 2, 1, 2, 5]
def baseStart_128706 : Nat := 118140960795 + 128706 * 2 ^ 59
def prefixEnd_128706 : Nat := 4983230072969 + 3 ^ 40 * 128706 * 2
def baseEnd_128706 : Nat := 14686231359484149085133

theorem tailTrace_128706 : CollatzResearch.WordTrace tailWord_128706 prefixEnd_128706 14686231359484149085133 := by
  unfold tailWord_128706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1173573367931904519973493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3129528981151745386595981 1173573367931904519973493)
  ·
    refine ⟨110022503243616048747515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1173573367931904519973493 110022503243616048747515)
    ·
      refine ⟨165033754865424073121273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110022503243616048747515 165033754865424073121273)
      ·
        refine ⟨123775316149068054840955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165033754865424073121273 123775316149068054840955)
        ·
          refine ⟨185662974223602082261433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123775316149068054840955 185662974223602082261433)
          ·
            refine ⟨139247230667701561696075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185662974223602082261433 139247230667701561696075)
            ·
              refine ⟨208870846001552342544113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139247230667701561696075 208870846001552342544113)
              ·
                refine ⟨156653134501164256908085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208870846001552342544113 156653134501164256908085)
                ·
                  refine ⟨14686231359484149085133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156653134501164256908085 14686231359484149085133)
                  ·
                    rfl

theorem cell22_128706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_128706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128706 prefixEnd_128706 := by exact prefixLift 128706
  have htrace : WordTrace (prefixWord ++ tailWord_128706) baseStart_128706 baseEnd_128706 := by
    simpa [prefixWord, tailWord_128706, baseEnd_128706] using wordTrace_append hprefix tailTrace_128706
  have hstable : (prefixWord ++ tailWord_128706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128706).length < 2 ^ (prefixWord ++ tailWord_128706).sum := by decide
  have hdescent : baseEnd_128706 < baseStart_128706 := by decide
  rcases family_descends (prefixWord ++ tailWord_128706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128711 : List Nat := [1, 1, 4, 1, 1, 1, 13]
def baseStart_128711 : Nat := 118140960795 + 128711 * 2 ^ 59
def prefixEnd_128711 : Nat := 4983230072969 + 3 ^ 40 * 128711 * 2
def baseEnd_128711 : Nat := 1631866877060522254829

theorem tailTrace_128711 : CollatzResearch.WordTrace tailWord_128711 prefixEnd_128711 1631866877060522254829 := by
  unfold tailWord_128711
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694475836709503933825987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3129650557806335955883991 4694475836709503933825987)
  ·
    refine ⟨7041713755064255900738981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4694475836709503933825987 7041713755064255900738981)
    ·
      refine ⟨1320321329074547981388559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7041713755064255900738981 1320321329074547981388559)
      ·
        refine ⟨1980481993611821972082839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320321329074547981388559 1980481993611821972082839)
        ·
          refine ⟨2970722990417732958124259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980481993611821972082839 2970722990417732958124259)
          ·
            refine ⟨4456084485626599437186389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970722990417732958124259 4456084485626599437186389)
            ·
              refine ⟨1631866877060522254829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 4456084485626599437186389 1631866877060522254829)
              ·
                rfl

theorem cell22_128711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 13].length) (baseStart_128711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128711 prefixEnd_128711 := by exact prefixLift 128711
  have htrace : WordTrace (prefixWord ++ tailWord_128711) baseStart_128711 baseEnd_128711 := by
    simpa [prefixWord, tailWord_128711, baseEnd_128711] using wordTrace_append hprefix tailTrace_128711
  have hstable : (prefixWord ++ tailWord_128711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128711).length < 2 ^ (prefixWord ++ tailWord_128711).sum := by decide
  have hdescent : baseEnd_128711 < baseStart_128711 := by decide
  rcases family_descends (prefixWord ++ tailWord_128711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128717 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 6]
def baseStart_128717 : Nat := 118140960795 + 128717 * 2 ^ 59
def prefixEnd_128717 : Nat := 4983230072969 + 3 ^ 40 * 128717 * 2
def baseEnd_128717 : Nat := 14687486534417361743455

theorem tailTrace_128717 : CollatzResearch.WordTrace tailWord_128717 prefixEnd_128717 14687486534417361743455 := by
  unfold tailWord_128717
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694694674687766958544405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3129796449791844639029603 4694694674687766958544405)
  ·
    refine ⟨220063812875989076181769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4694694674687766958544405 220063812875989076181769)
    ·
      refine ⟨165047859656991807136327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220063812875989076181769 165047859656991807136327)
      ·
        refine ⟨247571789485487710704491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165047859656991807136327 247571789485487710704491)
        ·
          refine ⟨371357684228231566056737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247571789485487710704491 371357684228231566056737)
          ·
            refine ⟨278518263171173674542553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371357684228231566056737 278518263171173674542553)
            ·
              refine ⟨208888697378380255906915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278518263171173674542553 208888697378380255906915)
              ·
                refine ⟨313333046067570383860373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208888697378380255906915 313333046067570383860373)
                ·
                  refine ⟨14687486534417361743455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 313333046067570383860373 14687486534417361743455)
                  ·
                    rfl

theorem cell22_128717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_128717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128717 prefixEnd_128717 := by exact prefixLift 128717
  have htrace : WordTrace (prefixWord ++ tailWord_128717) baseStart_128717 baseEnd_128717 := by
    simpa [prefixWord, tailWord_128717, baseEnd_128717] using wordTrace_append hprefix tailTrace_128717
  have hstable : (prefixWord ++ tailWord_128717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128717).length < 2 ^ (prefixWord ++ tailWord_128717).sum := by decide
  have hdescent : baseEnd_128717 < baseStart_128717 := by decide
  rcases family_descends (prefixWord ++ tailWord_128717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128848 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 1, 6]
def baseStart_128848 : Nat := 118140960795 + 128848 * 2 ^ 59
def prefixEnd_128848 : Nat := 4983230072969 + 3 ^ 40 * 128848 * 2
def baseEnd_128848 : Nat := 44107303580411410204963

theorem tailTrace_128848 : CollatzResearch.WordTrace tailWord_128848 prefixEnd_128848 44107303580411410204963 := by
  unfold tailWord_128848
  simp only [CollatzResearch.WordTrace]
  refine ⟨2349736318606588165781599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3132981758142117554375465 2349736318606588165781599)
  ·
    refine ⟨3524604477909882248672399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2349736318606588165781599 3524604477909882248672399)
    ·
      refine ⟨5286906716864823373008599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3524604477909882248672399 5286906716864823373008599)
      ·
        refine ⟨7930360075297235059512899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5286906716864823373008599 7930360075297235059512899)
        ·
          refine ⟨11895540112945852589269349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7930360075297235059512899 11895540112945852589269349)
          ·
            refine ⟨2230413771177347360488003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11895540112945852589269349 2230413771177347360488003)
            ·
              refine ⟨3345620656766021040732005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2230413771177347360488003 3345620656766021040732005)
              ·
                refine ⟨627303873143628945137251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3345620656766021040732005 627303873143628945137251)
                ·
                  refine ⟨940955809715443417705877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627303873143628945137251 940955809715443417705877)
                  ·
                    refine ⟨44107303580411410204963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 940955809715443417705877 44107303580411410204963)
                    ·
                      rfl

theorem cell22_128848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_128848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128848 prefixEnd_128848 := by exact prefixLift 128848
  have htrace : WordTrace (prefixWord ++ tailWord_128848) baseStart_128848 baseEnd_128848 := by
    simpa [prefixWord, tailWord_128848, baseEnd_128848] using wordTrace_append hprefix tailTrace_128848
  have hstable : (prefixWord ++ tailWord_128848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128848).length < 2 ^ (prefixWord ++ tailWord_128848).sum := by decide
  have hdescent : baseEnd_128848 < baseStart_128848 := by decide
  rcases family_descends (prefixWord ++ tailWord_128848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128850 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_128850 : Nat := 118140960795 + 128850 * 2 ^ 59
def prefixEnd_128850 : Nat := 4983230072969 + 3 ^ 40 * 128850 * 2
def baseEnd_128850 : Nat := 44107988221284071654957

theorem tailTrace_128850 : CollatzResearch.WordTrace tailWord_128850 prefixEnd_128850 44107988221284071654957 := by
  unfold tailWord_128850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1174886395801482668284001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3133030388803953782090669 1174886395801482668284001)
  ·
    refine ⟨881164796851112001213001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1174886395801482668284001 881164796851112001213001)
    ·
      refine ⟨660873597638334000909751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 881164796851112001213001 660873597638334000909751)
      ·
        refine ⟨991310396457501001364627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660873597638334000909751 991310396457501001364627)
        ·
          refine ⟨1486965594686251502046941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991310396457501001364627 1486965594686251502046941)
          ·
            refine ⟨557612098007344313267603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1486965594686251502046941 557612098007344313267603)
            ·
              refine ⟨836418147011016469901405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557612098007344313267603 836418147011016469901405)
              ·
                refine ⟨313656805129131176213027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 836418147011016469901405 313656805129131176213027)
                ·
                  refine ⟨470485207693696764319541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313656805129131176213027 470485207693696764319541)
                  ·
                    refine ⟨44107988221284071654957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 470485207693696764319541 44107988221284071654957)
                    ·
                      rfl

theorem cell22_128850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_128850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128850 prefixEnd_128850 := by exact prefixLift 128850
  have htrace : WordTrace (prefixWord ++ tailWord_128850) baseStart_128850 baseEnd_128850 := by
    simpa [prefixWord, tailWord_128850, baseEnd_128850] using wordTrace_append hprefix tailTrace_128850
  have hstable : (prefixWord ++ tailWord_128850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128850).length < 2 ^ (prefixWord ++ tailWord_128850).sum := by decide
  have hdescent : baseEnd_128850 < baseStart_128850 := by decide
  rcases family_descends (prefixWord ++ tailWord_128850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128914 : List Nat := [3, 2, 3, 2, 1, 3, 2, 6]
def baseStart_128914 : Nat := 118140960795 + 128914 * 2 ^ 59
def prefixEnd_128914 : Nat := 4983230072969 + 3 ^ 40 * 128914 * 2
def baseEnd_128914 : Nat := 4903321858801026450529

theorem tailTrace_128914 : CollatzResearch.WordTrace tailWord_128914 prefixEnd_128914 4903321858801026450529 := by
  unfold tailWord_128914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175469963743517400866449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3134586569982713068977197 1175469963743517400866449)
  ·
    refine ⟨881602472807638050649837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1175469963743517400866449 881602472807638050649837)
    ·
      refine ⟨330600927302864268993689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 881602472807638050649837 330600927302864268993689)
      ·
        refine ⟨247950695477148201745267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330600927302864268993689 247950695477148201745267)
        ·
          refine ⟨371926043215722302617901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247950695477148201745267 371926043215722302617901)
          ·
            refine ⟨139472266205895863481713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371926043215722302617901 139472266205895863481713)
            ·
              refine ⟨104604199654421897611285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139472266205895863481713 104604199654421897611285)
              ·
                refine ⟨4903321858801026450529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104604199654421897611285 4903321858801026450529)
                ·
                  rfl

theorem cell22_128914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 6].length) (baseStart_128914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128914 prefixEnd_128914 := by exact prefixLift 128914
  have htrace : WordTrace (prefixWord ++ tailWord_128914) baseStart_128914 baseEnd_128914 := by
    simpa [prefixWord, tailWord_128914, baseEnd_128914] using wordTrace_append hprefix tailTrace_128914
  have hstable : (prefixWord ++ tailWord_128914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128914).length < 2 ^ (prefixWord ++ tailWord_128914).sum := by decide
  have hdescent : baseEnd_128914 < baseStart_128914 := by decide
  rcases family_descends (prefixWord ++ tailWord_128914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128925 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 7]
def baseStart_128925 : Nat := 118140960795 + 128925 * 2 ^ 59
def prefixEnd_128925 : Nat := 4983230072969 + 3 ^ 40 * 128925 * 2
def baseEnd_128925 : Nat := 14711220751336292009909

theorem tailTrace_128925 : CollatzResearch.WordTrace tailWord_128925 prefixEnd_128925 14711220751336292009909 := by
  unfold tailWord_128925
  simp only [CollatzResearch.WordTrace]
  refine ⟨4702281057934218482116229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3134854038622812321410819 4702281057934218482116229)
  ·
    refine ⟨881677698362665965396793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4702281057934218482116229 881677698362665965396793)
    ·
      refine ⟨661258273771999474047595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 881677698362665965396793 661258273771999474047595)
      ·
        refine ⟨991887410657999211071393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661258273771999474047595 991887410657999211071393)
        ·
          refine ⟨743915557993499408303545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 991887410657999211071393 743915557993499408303545)
          ·
            refine ⟨557936668495124556227659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743915557993499408303545 557936668495124556227659)
            ·
              refine ⟨836905002742686834341489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557936668495124556227659 836905002742686834341489)
              ·
                refine ⟨627678752057015125756117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836905002742686834341489 627678752057015125756117)
                ·
                  refine ⟨14711220751336292009909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 627678752057015125756117 14711220751336292009909)
                  ·
                    rfl

theorem cell22_128925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_128925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128925 prefixEnd_128925 := by exact prefixLift 128925
  have htrace : WordTrace (prefixWord ++ tailWord_128925) baseStart_128925 baseEnd_128925 := by
    simpa [prefixWord, tailWord_128925, baseEnd_128925] using wordTrace_append hprefix tailTrace_128925
  have hstable : (prefixWord ++ tailWord_128925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128925).length < 2 ^ (prefixWord ++ tailWord_128925).sum := by decide
  have hdescent : baseEnd_128925 < baseStart_128925 := by decide
  rcases family_descends (prefixWord ++ tailWord_128925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128970 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 6]
def baseStart_128970 : Nat := 118140960795 + 128970 * 2 ^ 59
def prefixEnd_128970 : Nat := 4983230072969 + 3 ^ 40 * 128970 * 2
def baseEnd_128970 : Nat := 14716355557881252884863

theorem tailTrace_128970 : CollatzResearch.WordTrace tailWord_128970 prefixEnd_128970 14716355557881252884863 := by
  unfold tailWord_128970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175980585692797791876091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3135948228514127445002909 1175980585692797791876091)
  ·
    refine ⟨1763970878539196687814137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1175980585692797791876091 1763970878539196687814137)
    ·
      refine ⟨1322978158904397515860603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1763970878539196687814137 1322978158904397515860603)
      ·
        refine ⟨1984467238356596273790905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322978158904397515860603 1984467238356596273790905)
        ·
          refine ⟨1488350428767447205343179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1984467238356596273790905 1488350428767447205343179)
          ·
            refine ⟨2232525643151170808014769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488350428767447205343179 2232525643151170808014769)
            ·
              refine ⟨1674394232363378106011077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232525643151170808014769 1674394232363378106011077)
              ·
                refine ⟨313948918568133394877077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1674394232363378106011077 313948918568133394877077)
                ·
                  refine ⟨14716355557881252884863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 313948918568133394877077 14716355557881252884863)
                  ·
                    rfl

theorem cell22_128970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_128970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128970 prefixEnd_128970 := by exact prefixLift 128970
  have htrace : WordTrace (prefixWord ++ tailWord_128970) baseStart_128970 baseEnd_128970 := by
    simpa [prefixWord, tailWord_128970, baseEnd_128970] using wordTrace_append hprefix tailTrace_128970
  have hstable : (prefixWord ++ tailWord_128970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128970).length < 2 ^ (prefixWord ++ tailWord_128970).sum := by decide
  have hdescent : baseEnd_128970 < baseStart_128970 := by decide
  rcases family_descends (prefixWord ++ tailWord_128970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128972 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_128972 : Nat := 118140960795 + 128972 * 2 ^ 59
def prefixEnd_128972 : Nat := 4983230072969 + 3 ^ 40 * 128972 * 2
def baseEnd_128972 : Nat := 44149751314516420104583

theorem tailTrace_128972 : CollatzResearch.WordTrace tailWord_128972 prefixEnd_128972 44149751314516420104583 := by
  unfold tailWord_128972
  simp only [CollatzResearch.WordTrace]
  refine ⟨2351997644381972754538585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3135996859175963672718113 2351997644381972754538585)
  ·
    refine ⟨1763998233286479565903939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2351997644381972754538585 1763998233286479565903939)
    ·
      refine ⟨2645997349929719348855909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1763998233286479565903939 2645997349929719348855909)
      ·
        refine ⟨496124503111822377910483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2645997349929719348855909 496124503111822377910483)
        ·
          refine ⟨744186754667733566865725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496124503111822377910483 744186754667733566865725)
          ·
            refine ⟨279070033000400087574647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 744186754667733566865725 279070033000400087574647)
            ·
              refine ⟨418605049500600131361971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279070033000400087574647 418605049500600131361971)
              ·
                refine ⟨627907574250900197042957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418605049500600131361971 627907574250900197042957)
                ·
                  refine ⟨235465340344087573891109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627907574250900197042957 235465340344087573891109)
                  ·
                    refine ⟨44149751314516420104583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 235465340344087573891109 44149751314516420104583)
                    ·
                      rfl

theorem cell22_128972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_128972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_128972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_128972 prefixEnd_128972 := by exact prefixLift 128972
  have htrace : WordTrace (prefixWord ++ tailWord_128972) baseStart_128972 baseEnd_128972 := by
    simpa [prefixWord, tailWord_128972, baseEnd_128972] using wordTrace_append hprefix tailTrace_128972
  have hstable : (prefixWord ++ tailWord_128972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128972).length < 2 ^ (prefixWord ++ tailWord_128972).sum := by decide
  have hdescent : baseEnd_128972 < baseStart_128972 := by decide
  rcases family_descends (prefixWord ++ tailWord_128972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129000 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 3, 6]
def baseStart_129000 : Nat := 118140960795 + 129000 * 2 ^ 59
def prefixEnd_129000 : Nat := 4983230072969 + 3 ^ 40 * 129000 * 2
def baseEnd_129000 : Nat := 44159336286733680404497

theorem tailTrace_129000 : CollatzResearch.WordTrace tailWord_129000 prefixEnd_129000 44159336286733680404497 := by
  unfold tailWord_129000
  simp only [CollatzResearch.WordTrace]
  refine ⟨2352508266331253145548227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3136677688441670860730969 2352508266331253145548227)
  ·
    refine ⟨3528762399496879718322341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2352508266331253145548227 3528762399496879718322341)
    ·
      refine ⟨661642949905664947185439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3528762399496879718322341 661642949905664947185439)
      ·
        refine ⟨992464424858497420778159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661642949905664947185439 992464424858497420778159)
        ·
          refine ⟨1488696637287746131167239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992464424858497420778159 1488696637287746131167239)
          ·
            refine ⟨2233044955931619196750859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488696637287746131167239 2233044955931619196750859)
            ·
              refine ⟨3349567433897428795126289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2233044955931619196750859 3349567433897428795126289)
              ·
                refine ⟨2512175575423071596344717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3349567433897428795126289 2512175575423071596344717)
                ·
                  refine ⟨942065840783651848629269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2512175575423071596344717 942065840783651848629269)
                  ·
                    refine ⟨44159336286733680404497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 942065840783651848629269 44159336286733680404497)
                    ·
                      rfl

theorem cell22_129000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_129000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129000 prefixEnd_129000 := by exact prefixLift 129000
  have htrace : WordTrace (prefixWord ++ tailWord_129000) baseStart_129000 baseEnd_129000 := by
    simpa [prefixWord, tailWord_129000, baseEnd_129000] using wordTrace_append hprefix tailTrace_129000
  have hstable : (prefixWord ++ tailWord_129000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129000).length < 2 ^ (prefixWord ++ tailWord_129000).sum := by decide
  have hdescent : baseEnd_129000 < baseStart_129000 := by decide
  rcases family_descends (prefixWord ++ tailWord_129000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129032 : List Nat := [2, 1, 3, 2, 1, 2, 5, 6]
def baseStart_129032 : Nat := 118140960795 + 129032 * 2 ^ 59
def prefixEnd_129032 : Nat := 4983230072969 + 3 ^ 40 * 129032 * 2
def baseEnd_129032 : Nat := 4907810060077362622711

theorem tailTrace_129032 : CollatzResearch.WordTrace tailWord_129032 prefixEnd_129032 4907810060077362622711 := by
  unfold tailWord_129032
  simp only [CollatzResearch.WordTrace]
  refine ⟨2353091834273287878130675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3137455779031050504174233 2353091834273287878130675)
  ·
    refine ⟨3529637751409931817196013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2353091834273287878130675 3529637751409931817196013)
    ·
      refine ⟨1323614156778724431448505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3529637751409931817196013 1323614156778724431448505)
      ·
        refine ⟨992710617584043323586379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1323614156778724431448505 992710617584043323586379)
        ·
          refine ⟨1489065926376064985379569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992710617584043323586379 1489065926376064985379569)
          ·
            refine ⟨1116799444782048739034677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1489065926376064985379569 1116799444782048739034677)
            ·
              refine ⟨104699947948317069284501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1116799444782048739034677 104699947948317069284501)
              ·
                refine ⟨4907810060077362622711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104699947948317069284501 4907810060077362622711)
                ·
                  rfl

theorem cell22_129032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 6].length) (baseStart_129032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129032 prefixEnd_129032 := by exact prefixLift 129032
  have htrace : WordTrace (prefixWord ++ tailWord_129032) baseStart_129032 baseEnd_129032 := by
    simpa [prefixWord, tailWord_129032, baseEnd_129032] using wordTrace_append hprefix tailTrace_129032
  have hstable : (prefixWord ++ tailWord_129032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129032).length < 2 ^ (prefixWord ++ tailWord_129032).sum := by decide
  have hdescent : baseEnd_129032 < baseStart_129032 := by decide
  rcases family_descends (prefixWord ++ tailWord_129032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129077 : List Nat := [1, 3, 3, 1, 1, 1, 2, 5, 5]
def baseStart_129077 : Nat := 118140960795 + 129077 * 2 ^ 59
def prefixEnd_129077 : Nat := 4983230072969 + 3 ^ 40 * 129077 * 2
def baseEnd_129077 : Nat := 14728564986777048743087

theorem tailTrace_129077 : CollatzResearch.WordTrace tailWord_129077 prefixEnd_129077 14728564986777048743087 := by
  unfold tailWord_129077
  simp only [CollatzResearch.WordTrace]
  refine ⟨4707824953383548441649485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3138549968922365627766323 4707824953383548441649485)
  ·
    refine ⟨1765434357518830665618557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4707824953383548441649485 1765434357518830665618557)
    ·
      refine ⟨662037884069561499606959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1765434357518830665618557 662037884069561499606959)
      ·
        refine ⟨993056826104342249410439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662037884069561499606959 993056826104342249410439)
        ·
          refine ⟨1489585239156513374115659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993056826104342249410439 1489585239156513374115659)
          ·
            refine ⟨2234377858734770061173489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489585239156513374115659 2234377858734770061173489)
            ·
              refine ⟨1675783394051077545880117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2234377858734770061173489 1675783394051077545880117)
              ·
                refine ⟨157104693192288519926261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1675783394051077545880117 157104693192288519926261)
                ·
                  refine ⟨14728564986777048743087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157104693192288519926261 14728564986777048743087)
                  ·
                    rfl

theorem cell22_129077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_129077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129077 prefixEnd_129077 := by exact prefixLift 129077
  have htrace : WordTrace (prefixWord ++ tailWord_129077) baseStart_129077 baseEnd_129077 := by
    simpa [prefixWord, tailWord_129077, baseEnd_129077] using wordTrace_append hprefix tailTrace_129077
  have hstable : (prefixWord ++ tailWord_129077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129077).length < 2 ^ (prefixWord ++ tailWord_129077).sum := by decide
  have hdescent : baseEnd_129077 < baseStart_129077 := by decide
  rcases family_descends (prefixWord ++ tailWord_129077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129094 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_129094 : Nat := 118140960795 + 129094 * 2 ^ 59
def prefixEnd_129094 : Nat := 4983230072969 + 3 ^ 40 * 129094 * 2
def baseEnd_129094 : Nat := 14730504802582922851403

theorem tailTrace_129094 : CollatzResearch.WordTrace tailWord_129094 prefixEnd_129094 14730504802582922851403 := by
  unfold tailWord_129094
  simp only [CollatzResearch.WordTrace]
  refine ⟨147138906072561260781823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3138963329547973563345557 147138906072561260781823)
  ·
    refine ⟨220708359108841891172735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147138906072561260781823 220708359108841891172735)
    ·
      refine ⟨331062538663262836759103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220708359108841891172735 331062538663262836759103)
      ·
        refine ⟨496593807994894255138655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331062538663262836759103 496593807994894255138655)
        ·
          refine ⟨744890711992341382707983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496593807994894255138655 744890711992341382707983)
          ·
            refine ⟨1117336067988512074061975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744890711992341382707983 1117336067988512074061975)
            ·
              refine ⟨1676004101982768111092963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117336067988512074061975 1676004101982768111092963)
              ·
                refine ⟨2514006152974152166639445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676004101982768111092963 2514006152974152166639445)
                ·
                  refine ⟨14730504802582922851403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2514006152974152166639445 14730504802582922851403)
                  ·
                    rfl

theorem cell22_129094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_129094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129094 prefixEnd_129094 := by exact prefixLift 129094
  have htrace : WordTrace (prefixWord ++ tailWord_129094) baseStart_129094 baseEnd_129094 := by
    simpa [prefixWord, tailWord_129094, baseEnd_129094] using wordTrace_append hprefix tailTrace_129094
  have hstable : (prefixWord ++ tailWord_129094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129094).length < 2 ^ (prefixWord ++ tailWord_129094).sum := by decide
  have hdescent : baseEnd_129094 < baseStart_129094 := by decide
  rcases family_descends (prefixWord ++ tailWord_129094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129137 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 1, 5]
def baseStart_129137 : Nat := 118140960795 + 129137 * 2 ^ 59
def prefixEnd_129137 : Nat := 4983230072969 + 3 ^ 40 * 129137 * 2
def baseEnd_129137 : Nat := 44206234186510989729077

theorem tailTrace_129137 : CollatzResearch.WordTrace tailWord_129137 prefixEnd_129137 44206234186510989729077 := by
  unfold tailWord_129137
  simp only [CollatzResearch.WordTrace]
  refine ⟨4710013333166178688833665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3140008888777452459222443 4710013333166178688833665)
  ·
    refine ⟨3532509999874634016625249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4710013333166178688833665 3532509999874634016625249)
    ·
      refine ⟨2649382499905975512468937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3532509999874634016625249 2649382499905975512468937)
      ·
        refine ⟨1987036874929481634351703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2649382499905975512468937 1987036874929481634351703)
        ·
          refine ⟨2980555312394222451527555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987036874929481634351703 2980555312394222451527555)
          ·
            refine ⟨4470832968591333677291333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980555312394222451527555 4470832968591333677291333)
            ·
              refine ⟨838281181610875064492125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4470832968591333677291333 838281181610875064492125)
              ·
                refine ⟨314355443104078149184547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 838281181610875064492125 314355443104078149184547)
                ·
                  refine ⟨471533164656117223776821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314355443104078149184547 471533164656117223776821)
                  ·
                    refine ⟨44206234186510989729077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 471533164656117223776821 44206234186510989729077)
                    ·
                      rfl

theorem cell22_129137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_129137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129137 prefixEnd_129137 := by exact prefixLift 129137
  have htrace : WordTrace (prefixWord ++ tailWord_129137) baseStart_129137 baseEnd_129137 := by
    simpa [prefixWord, tailWord_129137, baseEnd_129137] using wordTrace_append hprefix tailTrace_129137
  have hstable : (prefixWord ++ tailWord_129137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129137).length < 2 ^ (prefixWord ++ tailWord_129137).sum := by decide
  have hdescent : baseEnd_129137 < baseStart_129137 := by decide
  rcases family_descends (prefixWord ++ tailWord_129137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129184 : List Nat := [2, 1, 1, 4, 2, 4, 1, 7]
def baseStart_129184 : Nat := 118140960795 + 129184 * 2 ^ 59
def prefixEnd_129184 : Nat := 4983230072969 + 3 ^ 40 * 129184 * 2
def baseEnd_129184 : Nat := 4913591471890948200437

theorem tailTrace_129184 : CollatzResearch.WordTrace tailWord_129184 prefixEnd_129184 4913591471890948200437 := by
  unfold tailWord_129184
  simp only [CollatzResearch.WordTrace]
  refine ⟨2355863781997952857897303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3141151709330603810529737 2355863781997952857897303)
  ·
    refine ⟨3533795672996929286845955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2355863781997952857897303 3533795672996929286845955)
    ·
      refine ⟨5300693509495393930268933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3533795672996929286845955 5300693509495393930268933)
      ·
        refine ⟨993880033030386361925425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5300693509495393930268933 993880033030386361925425)
        ·
          refine ⟨745410024772789771444069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 993880033030386361925425 745410024772789771444069)
          ·
            refine ⟨139764379644898082145763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 745410024772789771444069 139764379644898082145763)
            ·
              refine ⟨209646569467347123218645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139764379644898082145763 209646569467347123218645)
              ·
                refine ⟨4913591471890948200437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 209646569467347123218645 4913591471890948200437)
                ·
                  rfl

theorem cell22_129184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 7].length) (baseStart_129184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129184 prefixEnd_129184 := by exact prefixLift 129184
  have htrace : WordTrace (prefixWord ++ tailWord_129184) baseStart_129184 baseEnd_129184 := by
    simpa [prefixWord, tailWord_129184, baseEnd_129184] using wordTrace_append hprefix tailTrace_129184
  have hstable : (prefixWord ++ tailWord_129184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129184).length < 2 ^ (prefixWord ++ tailWord_129184).sum := by decide
  have hdescent : baseEnd_129184 < baseStart_129184 := by decide
  rcases family_descends (prefixWord ++ tailWord_129184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129201 : List Nat := [1, 2, 2, 5, 2, 1, 3, 6]
def baseStart_129201 : Nat := 118140960795 + 129201 * 2 ^ 59
def prefixEnd_129201 : Nat := 4983230072969 + 3 ^ 40 * 129201 * 2
def baseEnd_129201 : Nat := 4914238077159572903209

theorem tailTrace_129201 : CollatzResearch.WordTrace tailWord_129201 prefixEnd_129201 4914238077159572903209 := by
  unfold tailWord_129201
  simp only [CollatzResearch.WordTrace]
  refine ⟨4712347604934317619163457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3141565069956211746108971 4712347604934317619163457)
  ·
    refine ⟨3534260703700738214372593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4712347604934317619163457 3534260703700738214372593)
    ·
      refine ⟨2650695527775553660779445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3534260703700738214372593 2650695527775553660779445)
      ·
        refine ⟨248502705728958155698073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2650695527775553660779445 248502705728958155698073)
        ·
          refine ⟨186377029296718616773555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248502705728958155698073 186377029296718616773555)
          ·
            refine ⟨279565543945077925160333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186377029296718616773555 279565543945077925160333)
            ·
              refine ⟨104837078979404221935125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279565543945077925160333 104837078979404221935125)
              ·
                refine ⟨4914238077159572903209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104837078979404221935125 4914238077159572903209)
                ·
                  rfl

theorem cell22_129201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 6].length) (baseStart_129201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129201 prefixEnd_129201 := by exact prefixLift 129201
  have htrace : WordTrace (prefixWord ++ tailWord_129201) baseStart_129201 baseEnd_129201 := by
    simpa [prefixWord, tailWord_129201, baseEnd_129201] using wordTrace_append hprefix tailTrace_129201
  have hstable : (prefixWord ++ tailWord_129201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129201).length < 2 ^ (prefixWord ++ tailWord_129201).sum := by decide
  have hdescent : baseEnd_129201 < baseStart_129201 := by decide
  rcases family_descends (prefixWord ++ tailWord_129201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129227 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 4, 5]
def baseStart_129227 : Nat := 118140960795 + 129227 * 2 ^ 59
def prefixEnd_129227 : Nat := 4983230072969 + 3 ^ 40 * 129227 * 2
def baseEnd_129227 : Nat := 44237043025780754978801

theorem tailTrace_129227 : CollatzResearch.WordTrace tailWord_129227 prefixEnd_129227 44237043025780754978801 := by
  unfold tailWord_129227
  simp only [CollatzResearch.WordTrace]
  refine ⟨4713295902840124059609935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3142197268560082706406623 4713295902840124059609935)
  ·
    refine ⟨7069943854260186089414903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4713295902840124059609935 7069943854260186089414903)
    ·
      refine ⟨10604915781390279134122355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7069943854260186089414903 10604915781390279134122355)
      ·
        refine ⟨15907373672085418701183533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10604915781390279134122355 15907373672085418701183533)
        ·
          refine ⟨5965265127032032012943825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15907373672085418701183533 5965265127032032012943825)
          ·
            refine ⟨4473948845274024009707869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5965265127032032012943825 4473948845274024009707869)
            ·
              refine ⟨1677730816977759003640451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4473948845274024009707869 1677730816977759003640451)
              ·
                refine ⟨2516596225466638505460677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677730816977759003640451 2516596225466638505460677)
                ·
                  refine ⟨471861792274994719773877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2516596225466638505460677 471861792274994719773877)
                  ·
                    refine ⟨44237043025780754978801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 471861792274994719773877 44237043025780754978801)
                    ·
                      rfl

theorem cell22_129227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 5].length) (baseStart_129227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129227 prefixEnd_129227 := by exact prefixLift 129227
  have htrace : WordTrace (prefixWord ++ tailWord_129227) baseStart_129227 baseEnd_129227 := by
    simpa [prefixWord, tailWord_129227, baseEnd_129227] using wordTrace_append hprefix tailTrace_129227
  have hstable : (prefixWord ++ tailWord_129227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129227).length < 2 ^ (prefixWord ++ tailWord_129227).sum := by decide
  have hdescent : baseEnd_129227 < baseStart_129227 := by decide
  rcases family_descends (prefixWord ++ tailWord_129227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129276 : List Nat := [2, 2, 2, 1, 4, 1, 2, 3, 1, 4]
def baseStart_129276 : Nat := 118140960795 + 129276 * 2 ^ 59
def prefixEnd_129276 : Nat := 4983230072969 + 3 ^ 40 * 129276 * 2
def baseEnd_129276 : Nat := 44253816727160960503651

theorem tailTrace_129276 : CollatzResearch.WordTrace tailWord_129276 prefixEnd_129276 44253816727160960503651 := by
  unfold tailWord_129276
  simp only [CollatzResearch.WordTrace]
  refine ⟨2357541539831302714071841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3143388719775070285429121 2357541539831302714071841)
  ·
    refine ⟨1768156154873477035553881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2357541539831302714071841 1768156154873477035553881)
    ·
      refine ⟨1326117116155107776665411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1768156154873477035553881 1326117116155107776665411)
      ·
        refine ⟨1989175674232661664998117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326117116155107776665411 1989175674232661664998117)
        ·
          refine ⟨372970438918624062187147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1989175674232661664998117 372970438918624062187147)
          ·
            refine ⟨559455658377936093280721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372970438918624062187147 559455658377936093280721)
            ·
              refine ⟨419591743783452069960541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 559455658377936093280721 419591743783452069960541)
              ·
                refine ⟨157346903918794526235203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 419591743783452069960541 157346903918794526235203)
                ·
                  refine ⟨236020355878191789352805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157346903918794526235203 236020355878191789352805)
                  ·
                    refine ⟨44253816727160960503651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236020355878191789352805 44253816727160960503651)
                    ·
                      rfl

theorem cell22_129276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_129276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129276 prefixEnd_129276 := by exact prefixLift 129276
  have htrace : WordTrace (prefixWord ++ tailWord_129276) baseStart_129276 baseEnd_129276 := by
    simpa [prefixWord, tailWord_129276, baseEnd_129276] using wordTrace_append hprefix tailTrace_129276
  have hstable : (prefixWord ++ tailWord_129276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129276).length < 2 ^ (prefixWord ++ tailWord_129276).sum := by decide
  have hdescent : baseEnd_129276 < baseStart_129276 := by decide
  rcases family_descends (prefixWord ++ tailWord_129276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129304 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 4, 4]
def baseStart_129304 : Nat := 118140960795 + 129304 * 2 ^ 59
def prefixEnd_129304 : Nat := 4983230072969 + 3 ^ 40 * 129304 * 2
def baseEnd_129304 : Nat := 44263401699378220803565

theorem tailTrace_129304 : CollatzResearch.WordTrace tailWord_129304 prefixEnd_129304 44263401699378220803565 := by
  unfold tailWord_129304
  simp only [CollatzResearch.WordTrace]
  refine ⟨2358052161780583105081483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3144069549040777473441977 2358052161780583105081483)
  ·
    refine ⟨3537078242670874657622225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2358052161780583105081483 3537078242670874657622225)
    ·
      refine ⟨2652808682003155993216669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3537078242670874657622225 2652808682003155993216669)
      ·
        refine ⟨994803255751183497456251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2652808682003155993216669 994803255751183497456251)
        ·
          refine ⟨1492204883626775246184377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994803255751183497456251 1492204883626775246184377)
          ·
            refine ⟨1119153662720081434638283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1492204883626775246184377 1119153662720081434638283)
            ·
              refine ⟨1678730494080122151957425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119153662720081434638283 1678730494080122151957425)
              ·
                refine ⟨1259047870560091613968069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1678730494080122151957425 1259047870560091613968069)
                ·
                  refine ⟨236071475730017177619013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1259047870560091613968069 236071475730017177619013)
                  ·
                    refine ⟨44263401699378220803565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236071475730017177619013 44263401699378220803565)
                    ·
                      rfl

theorem cell22_129304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_129304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129304 prefixEnd_129304 := by exact prefixLift 129304
  have htrace : WordTrace (prefixWord ++ tailWord_129304) baseStart_129304 baseEnd_129304 := by
    simpa [prefixWord, tailWord_129304, baseEnd_129304] using wordTrace_append hprefix tailTrace_129304
  have hstable : (prefixWord ++ tailWord_129304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129304).length < 2 ^ (prefixWord ++ tailWord_129304).sum := by decide
  have hdescent : baseEnd_129304 < baseStart_129304 := by decide
  rcases family_descends (prefixWord ++ tailWord_129304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129310 : List Nat := [4, 3, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_129310 : Nat := 118140960795 + 129310 * 2 ^ 59
def prefixEnd_129310 : Nat := 4983230072969 + 3 ^ 40 * 129310 * 2
def baseEnd_129310 : Nat := 44265455621996205153547

theorem tailTrace_129310 : CollatzResearch.WordTrace tailWord_129310 prefixEnd_129310 44265455621996205153547 := by
  unfold tailWord_129310
  simp only [CollatzResearch.WordTrace]
  refine ⟨589540395192428654360173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3144215441026286156587589 589540395192428654360173)
  ·
    refine ⟨221077648197160745385065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 589540395192428654360173 221077648197160745385065)
    ·
      refine ⟨165808236147870559038799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221077648197160745385065 165808236147870559038799)
      ·
        refine ⟨248712354221805838558199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165808236147870559038799 248712354221805838558199)
        ·
          refine ⟨373068531332708757837299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248712354221805838558199 373068531332708757837299)
          ·
            refine ⟨559602796999063136755949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373068531332708757837299 559602796999063136755949)
            ·
              refine ⟨209851048874648676283481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559602796999063136755949 209851048874648676283481)
              ·
                refine ⟨157388286655986507212611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209851048874648676283481 157388286655986507212611)
                ·
                  refine ⟨236082429983979760818917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157388286655986507212611 236082429983979760818917)
                  ·
                    refine ⟨44265455621996205153547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236082429983979760818917 44265455621996205153547)
                    ·
                      rfl

theorem cell22_129310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_129310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129310 prefixEnd_129310 := by exact prefixLift 129310
  have htrace : WordTrace (prefixWord ++ tailWord_129310) baseStart_129310 baseEnd_129310 := by
    simpa [prefixWord, tailWord_129310, baseEnd_129310] using wordTrace_append hprefix tailTrace_129310
  have hstable : (prefixWord ++ tailWord_129310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129310).length < 2 ^ (prefixWord ++ tailWord_129310).sum := by decide
  have hdescent : baseEnd_129310 < baseStart_129310 := by decide
  rcases family_descends (prefixWord ++ tailWord_129310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129351 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 3, 3]
def baseStart_129351 : Nat := 118140960795 + 129351 * 2 ^ 59
def prefixEnd_129351 : Nat := 4983230072969 + 3 ^ 40 * 129351 * 2
def baseEnd_129351 : Nat := 44279490759885764878421

theorem tailTrace_129351 : CollatzResearch.WordTrace tailWord_129351 prefixEnd_129351 44279490759885764878421 := by
  unfold tailWord_129351
  simp only [CollatzResearch.WordTrace]
  refine ⟨4717818554390893237123907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3145212369593928824749271 4717818554390893237123907)
  ·
    refine ⟨7076727831586339855685861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4717818554390893237123907 7076727831586339855685861)
    ·
      refine ⟨1326886468422438722941099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7076727831586339855685861 1326886468422438722941099)
      ·
        refine ⟨1990329702633658084411649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326886468422438722941099 1990329702633658084411649)
        ·
          refine ⟨1492747276975243563308737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1990329702633658084411649 1492747276975243563308737)
          ·
            refine ⟨1119560457731432672481553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1492747276975243563308737 1119560457731432672481553)
            ·
              refine ⟨839670343298574504361165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119560457731432672481553 839670343298574504361165)
              ·
                refine ⟨314876378736965439135437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 839670343298574504361165 314876378736965439135437)
                ·
                  refine ⟨118078642026362039675789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314876378736965439135437 118078642026362039675789)
                  ·
                    refine ⟨44279490759885764878421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118078642026362039675789 44279490759885764878421)
                    ·
                      rfl

theorem cell22_129351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_129351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129351 prefixEnd_129351 := by exact prefixLift 129351
  have htrace : WordTrace (prefixWord ++ tailWord_129351) baseStart_129351 baseEnd_129351 := by
    simpa [prefixWord, tailWord_129351, baseEnd_129351] using wordTrace_append hprefix tailTrace_129351
  have hstable : (prefixWord ++ tailWord_129351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129351).length < 2 ^ (prefixWord ++ tailWord_129351).sum := by decide
  have hdescent : baseEnd_129351 < baseStart_129351 := by decide
  rcases family_descends (prefixWord ++ tailWord_129351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129372 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 2, 4]
def baseStart_129372 : Nat := 118140960795 + 129372 * 2 ^ 59
def prefixEnd_129372 : Nat := 4983230072969 + 3 ^ 40 * 129372 * 2
def baseEnd_129372 : Nat := 44286679489048710103357

theorem tailTrace_129372 : CollatzResearch.WordTrace tailWord_129372 prefixEnd_129372 44286679489048710103357 := by
  unfold tailWord_129372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2359292243657406911819185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3145722991543209215758913 2359292243657406911819185)
  ·
    refine ⟨1769469182743055183864389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2359292243657406911819185 1769469182743055183864389)
    ·
      refine ⟨331775471764322846974573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1769469182743055183864389 331775471764322846974573)
      ·
        refine ⟨124415801911621067615465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331775471764322846974573 124415801911621067615465)
        ·
          refine ⟨93311851433715800711599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124415801911621067615465 93311851433715800711599)
          ·
            refine ⟨139967777150573701067399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93311851433715800711599 139967777150573701067399)
            ·
              refine ⟨209951665725860551601099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139967777150573701067399 209951665725860551601099)
              ·
                refine ⟨314927498588790827401649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209951665725860551601099 314927498588790827401649)
                ·
                  refine ⟨236195623941593120551237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314927498588790827401649 236195623941593120551237)
                  ·
                    refine ⟨44286679489048710103357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236195623941593120551237 44286679489048710103357)
                    ·
                      rfl

theorem cell22_129372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_129372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129372 prefixEnd_129372 := by exact prefixLift 129372
  have htrace : WordTrace (prefixWord ++ tailWord_129372) baseStart_129372 baseEnd_129372 := by
    simpa [prefixWord, tailWord_129372, baseEnd_129372] using wordTrace_append hprefix tailTrace_129372
  have hstable : (prefixWord ++ tailWord_129372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129372).length < 2 ^ (prefixWord ++ tailWord_129372).sum := by decide
  have hdescent : baseEnd_129372 < baseStart_129372 := by decide
  rcases family_descends (prefixWord ++ tailWord_129372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129379 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 1, 7]
def baseStart_129379 : Nat := 118140960795 + 129379 * 2 ^ 59
def prefixEnd_129379 : Nat := 4983230072969 + 3 ^ 40 * 129379 * 2
def baseEnd_129379 : Nat := 44289075732103025178335

theorem tailTrace_129379 : CollatzResearch.WordTrace tailWord_129379 prefixEnd_129379 44289075732103025178335 := by
  unfold tailWord_129379
  simp only [CollatzResearch.WordTrace]
  refine ⟨4718839798289454019143191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3145893198859636012762127 4718839798289454019143191)
  ·
    refine ⟨7078259697434181028714787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4718839798289454019143191 7078259697434181028714787)
    ·
      refine ⟨10617389546151271543072181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7078259697434181028714787 10617389546151271543072181)
      ·
        refine ⟨995380269951681707163017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10617389546151271543072181 995380269951681707163017)
        ·
          refine ⟨746535202463761280372263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 995380269951681707163017 746535202463761280372263)
          ·
            refine ⟨1119802803695641920558395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746535202463761280372263 1119802803695641920558395)
            ·
              refine ⟨1679704205543462880837593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119802803695641920558395 1679704205543462880837593)
              ·
                refine ⟨1259778154157597160628195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1679704205543462880837593 1259778154157597160628195)
                ·
                  refine ⟨1889667231236395740942293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1259778154157597160628195 1889667231236395740942293)
                  ·
                    refine ⟨44289075732103025178335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1889667231236395740942293 44289075732103025178335)
                    ·
                      rfl

theorem cell22_129379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 7].length) (baseStart_129379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129379 prefixEnd_129379 := by exact prefixLift 129379
  have htrace : WordTrace (prefixWord ++ tailWord_129379) baseStart_129379 baseEnd_129379 := by
    simpa [prefixWord, tailWord_129379, baseEnd_129379] using wordTrace_append hprefix tailTrace_129379
  have hstable : (prefixWord ++ tailWord_129379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129379).length < 2 ^ (prefixWord ++ tailWord_129379).sum := by decide
  have hdescent : baseEnd_129379 < baseStart_129379 := by decide
  rcases family_descends (prefixWord ++ tailWord_129379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129424 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 7, 5]
def baseStart_129424 : Nat := 118140960795 + 129424 * 2 ^ 59
def prefixEnd_129424 : Nat := 4983230072969 + 3 ^ 40 * 129424 * 2
def baseEnd_129424 : Nat := 44304480151737907803197

theorem tailTrace_129424 : CollatzResearch.WordTrace tailWord_129424 prefixEnd_129424 44304480151737907803197 := by
  unfold tailWord_129424
  simp only [CollatzResearch.WordTrace]
  refine ⟨2360240541563213352265663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3146987388750951136354217 2360240541563213352265663)
  ·
    refine ⟨3540360812344820028398495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2360240541563213352265663 3540360812344820028398495)
    ·
      refine ⟨5310541218517230042597743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3540360812344820028398495 5310541218517230042597743)
      ·
        refine ⟨7965811827775845063896615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5310541218517230042597743 7965811827775845063896615)
        ·
          refine ⟨11948717741663767595844923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7965811827775845063896615 11948717741663767595844923)
          ·
            refine ⟨17923076612495651393767385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11948717741663767595844923 17923076612495651393767385)
            ·
              refine ⟨13442307459371738545325539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17923076612495651393767385 13442307459371738545325539)
              ·
                refine ⟨20163461189057607817988309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13442307459371738545325539 20163461189057607817988309)
                ·
                  refine ⟨472581121618537683234101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20163461189057607817988309 472581121618537683234101)
                  ·
                    refine ⟨44304480151737907803197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 472581121618537683234101 44304480151737907803197)
                    ·
                      rfl

theorem cell22_129424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_129424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129424 prefixEnd_129424 := by exact prefixLift 129424
  have htrace : WordTrace (prefixWord ++ tailWord_129424) baseStart_129424 baseEnd_129424 := by
    simpa [prefixWord, tailWord_129424, baseEnd_129424] using wordTrace_append hprefix tailTrace_129424
  have hstable : (prefixWord ++ tailWord_129424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129424).length < 2 ^ (prefixWord ++ tailWord_129424).sum := by decide
  have hdescent : baseEnd_129424 < baseStart_129424 := by decide
  rcases family_descends (prefixWord ++ tailWord_129424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129443 : List Nat := [1, 1, 1, 4, 1, 4, 3, 3, 4]
def baseStart_129443 : Nat := 118140960795 + 129443 * 2 ^ 59
def prefixEnd_129443 : Nat := 4983230072969 + 3 ^ 40 * 129443 * 2
def baseEnd_129443 : Nat := 14770328080009397192713

theorem tailTrace_129443 : CollatzResearch.WordTrace tailWord_129443 prefixEnd_129443 14770328080009397192713 := by
  unfold tailWord_129443
  simp only [CollatzResearch.WordTrace]
  refine ⟨4721174070057592949472983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3147449380038395299648655 4721174070057592949472983)
  ·
    refine ⟨7081761105086389424209475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4721174070057592949472983 7081761105086389424209475)
    ·
      refine ⟨10622641657629584136314213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7081761105086389424209475 10622641657629584136314213)
      ·
        refine ⟨1991745310805547025558915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10622641657629584136314213 1991745310805547025558915)
        ·
          refine ⟨2987617966208320538338373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991745310805547025558915 2987617966208320538338373)
          ·
            refine ⟨560178368664060100938445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2987617966208320538338373 560178368664060100938445)
            ·
              refine ⟨210066888249022537851917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 560178368664060100938445 210066888249022537851917)
              ·
                refine ⟨78775083093383451694469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210066888249022537851917 78775083093383451694469)
                ·
                  refine ⟨14770328080009397192713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78775083093383451694469 14770328080009397192713)
                  ·
                    rfl

theorem cell22_129443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 4].length) (baseStart_129443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129443 prefixEnd_129443 := by exact prefixLift 129443
  have htrace : WordTrace (prefixWord ++ tailWord_129443) baseStart_129443 baseEnd_129443 := by
    simpa [prefixWord, tailWord_129443, baseEnd_129443] using wordTrace_append hprefix tailTrace_129443
  have hstable : (prefixWord ++ tailWord_129443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129443).length < 2 ^ (prefixWord ++ tailWord_129443).sum := by decide
  have hdescent : baseEnd_129443 < baseStart_129443 := by decide
  rcases family_descends (prefixWord ++ tailWord_129443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129458 : List Nat := [3, 2, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_129458 : Nat := 118140960795 + 129458 * 2 ^ 59
def prefixEnd_129458 : Nat := 4983230072969 + 3 ^ 40 * 129458 * 2
def baseEnd_129458 : Nat := 44316119046573152453093

theorem tailTrace_129458 : CollatzResearch.WordTrace tailWord_129458 prefixEnd_129458 44316119046573152453093 := by
  unfold tailWord_129458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1180430291250812627817257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3147814110002167007512685 1180430291250812627817257)
  ·
    refine ⟨885322718438109470862943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1180430291250812627817257 885322718438109470862943)
    ·
      refine ⟨1327984077657164206294415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 885322718438109470862943 1327984077657164206294415)
      ·
        refine ⟨1991976116485746309441623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327984077657164206294415 1991976116485746309441623)
        ·
          refine ⟨2987964174728619464162435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991976116485746309441623 2987964174728619464162435)
          ·
            refine ⟨4481946262092929196243653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987964174728619464162435 4481946262092929196243653)
            ·
              refine ⟨840364924142424224295685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4481946262092929196243653 840364924142424224295685)
              ·
                refine ⟨157568423276704542055441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 840364924142424224295685 157568423276704542055441)
                ·
                  refine ⟨118176317457528406541581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157568423276704542055441 118176317457528406541581)
                  ·
                    refine ⟨44316119046573152453093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118176317457528406541581 44316119046573152453093)
                    ·
                      rfl

theorem cell22_129458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_129458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129458 prefixEnd_129458 := by exact prefixLift 129458
  have htrace : WordTrace (prefixWord ++ tailWord_129458) baseStart_129458 baseEnd_129458 := by
    simpa [prefixWord, tailWord_129458, baseEnd_129458] using wordTrace_append hprefix tailTrace_129458
  have hstable : (prefixWord ++ tailWord_129458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129458).length < 2 ^ (prefixWord ++ tailWord_129458).sum := by decide
  have hdescent : baseEnd_129458 < baseStart_129458 := by decide
  rcases family_descends (prefixWord ++ tailWord_129458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129520 : List Nat := [2, 1, 1, 1, 3, 3, 3, 4, 1, 3]
def baseStart_129520 : Nat := 118140960795 + 129520 * 2 ^ 59
def prefixEnd_129520 : Nat := 4983230072969 + 3 ^ 40 * 129520 * 2
def baseEnd_129520 : Nat := 44337342913625657402903

theorem tailTrace_129520 : CollatzResearch.WordTrace tailWord_129520 prefixEnd_129520 44337342913625657402903 := by
  unfold tailWord_129520
  simp only [CollatzResearch.WordTrace]
  refine ⟨2361991245389317550013007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3149321660519090066684009 2361991245389317550013007)
  ·
    refine ⟨3542986868083976325019511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2361991245389317550013007 3542986868083976325019511)
    ·
      refine ⟨5314480302125964487529267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3542986868083976325019511 5314480302125964487529267)
      ·
        refine ⟨7971720453188946731293901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5314480302125964487529267 7971720453188946731293901)
        ·
          refine ⟨2989395169945855024235213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7971720453188946731293901 2989395169945855024235213)
          ·
            refine ⟨1121023188729695634088205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2989395169945855024235213 1121023188729695634088205)
            ·
              refine ⟨420383695773635862783077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1121023188729695634088205 420383695773635862783077)
              ·
                refine ⟨78821942957556724271827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 420383695773635862783077 78821942957556724271827)
                ·
                  refine ⟨118232914436335086407741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78821942957556724271827 118232914436335086407741)
                  ·
                    refine ⟨44337342913625657402903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118232914436335086407741 44337342913625657402903)
                    ·
                      rfl

theorem cell22_129520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 1, 3].length) (baseStart_129520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129520 prefixEnd_129520 := by exact prefixLift 129520
  have htrace : WordTrace (prefixWord ++ tailWord_129520) baseStart_129520 baseEnd_129520 := by
    simpa [prefixWord, tailWord_129520, baseEnd_129520] using wordTrace_append hprefix tailTrace_129520
  have hstable : (prefixWord ++ tailWord_129520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129520).length < 2 ^ (prefixWord ++ tailWord_129520).sum := by decide
  have hdescent : baseEnd_129520 < baseStart_129520 := by decide
  rcases family_descends (prefixWord ++ tailWord_129520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129578 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 6]
def baseStart_129578 : Nat := 118140960795 + 129578 * 2 ^ 59
def prefixEnd_129578 : Nat := 4983230072969 + 3 ^ 40 * 129578 * 2
def baseEnd_129578 : Nat := 14785732499644279817575

theorem tailTrace_129578 : CollatzResearch.WordTrace tailWord_129578 prefixEnd_129578 14785732499644279817575 := by
  unfold tailWord_129578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1181524481142127751409347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3150731949712340670424925 1181524481142127751409347)
  ·
    refine ⟨1772286721713191627114021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1181524481142127751409347 1772286721713191627114021)
    ·
      refine ⟨332303760321223430083879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1772286721713191627114021 332303760321223430083879)
      ·
        refine ⟨498455640481835145125819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332303760321223430083879 498455640481835145125819)
        ·
          refine ⟨747683460722752717688729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498455640481835145125819 747683460722752717688729)
          ·
            refine ⟨560762595542064538266547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747683460722752717688729 560762595542064538266547)
            ·
              refine ⟨841143893313096807399821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560762595542064538266547 841143893313096807399821)
              ·
                refine ⟨315428959992411302774933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 841143893313096807399821 315428959992411302774933)
                ·
                  refine ⟨14785732499644279817575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 315428959992411302774933 14785732499644279817575)
                  ·
                    rfl

theorem cell22_129578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_129578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129578 prefixEnd_129578 := by exact prefixLift 129578
  have htrace : WordTrace (prefixWord ++ tailWord_129578) baseStart_129578 baseEnd_129578 := by
    simpa [prefixWord, tailWord_129578, baseEnd_129578] using wordTrace_append hprefix tailTrace_129578
  have hstable : (prefixWord ++ tailWord_129578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129578).length < 2 ^ (prefixWord ++ tailWord_129578).sum := by decide
  have hdescent : baseEnd_129578 < baseStart_129578 := by decide
  rcases family_descends (prefixWord ++ tailWord_129578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129591 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 3, 6]
def baseStart_129591 : Nat := 118140960795 + 129591 * 2 ^ 59
def prefixEnd_129591 : Nat := 4983230072969 + 3 ^ 40 * 129591 * 2
def baseEnd_129591 : Nat := 44361647664605138877685

theorem tailTrace_129591 : CollatzResearch.WordTrace tailWord_129591 prefixEnd_129591 44361647664605138877685 := by
  unfold tailWord_129591
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726572073521414225860627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3151048049014276150573751 4726572073521414225860627)
  ·
    refine ⟨7089858110282121338790941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4726572073521414225860627 7089858110282121338790941)
    ·
      refine ⟨2658696791355795502046603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7089858110282121338790941 2658696791355795502046603)
      ·
        refine ⟨3988045187033693253069905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2658696791355795502046603 3988045187033693253069905)
        ·
          refine ⟨2991033890275269939802429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3988045187033693253069905 2991033890275269939802429)
          ·
            refine ⟨1121637708853226227425911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2991033890275269939802429 1121637708853226227425911)
            ·
              refine ⟨1682456563279839341138867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121637708853226227425911 1682456563279839341138867)
              ·
                refine ⟨2523684844919759011708301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682456563279839341138867 2523684844919759011708301)
                ·
                  refine ⟨946381816844909629390613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2523684844919759011708301 946381816844909629390613)
                  ·
                    refine ⟨44361647664605138877685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 946381816844909629390613 44361647664605138877685)
                    ·
                      rfl

theorem cell22_129591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_129591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129591 prefixEnd_129591 := by exact prefixLift 129591
  have htrace : WordTrace (prefixWord ++ tailWord_129591) baseStart_129591 baseEnd_129591 := by
    simpa [prefixWord, tailWord_129591, baseEnd_129591] using wordTrace_append hprefix tailTrace_129591
  have hstable : (prefixWord ++ tailWord_129591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129591).length < 2 ^ (prefixWord ++ tailWord_129591).sum := by decide
  have hdescent : baseEnd_129591 < baseStart_129591 := by decide
  rcases family_descends (prefixWord ++ tailWord_129591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129640 : List Nat := [2, 1, 4, 3, 2, 1, 2, 7]
def baseStart_129640 : Nat := 118140960795 + 129640 * 2 ^ 59
def prefixEnd_129640 : Nat := 4983230072969 + 3 ^ 40 * 129640 * 2
def baseEnd_129640 : Nat := 4930935707331704933615

theorem tailTrace_129640 : CollatzResearch.WordTrace tailWord_129640 prefixEnd_129640 4930935707331704933615 := by
  unfold tailWord_129640
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364179625171947797197187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3152239500229263729596249 2364179625171947797197187)
  ·
    refine ⟨3546269437757921695795781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2364179625171947797197187 3546269437757921695795781)
    ·
      refine ⟨664925519579610317961709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3546269437757921695795781 664925519579610317961709)
      ·
        refine ⟨249347069842353869235641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 664925519579610317961709 249347069842353869235641)
        ·
          refine ⟨187010302381765401926731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249347069842353869235641 187010302381765401926731)
          ·
            refine ⟨280515453572648102890097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187010302381765401926731 280515453572648102890097)
            ·
              refine ⟨210386590179486077167573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280515453572648102890097 210386590179486077167573)
              ·
                refine ⟨4930935707331704933615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 210386590179486077167573 4930935707331704933615)
                ·
                  rfl

theorem cell22_129640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 7].length) (baseStart_129640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129640 prefixEnd_129640 := by exact prefixLift 129640
  have htrace : WordTrace (prefixWord ++ tailWord_129640) baseStart_129640 baseEnd_129640 := by
    simpa [prefixWord, tailWord_129640, baseEnd_129640] using wordTrace_append hprefix tailTrace_129640
  have hstable : (prefixWord ++ tailWord_129640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129640).length < 2 ^ (prefixWord ++ tailWord_129640).sum := by decide
  have hdescent : baseEnd_129640 < baseStart_129640 := by decide
  rcases family_descends (prefixWord ++ tailWord_129640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129651 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 9]
def baseStart_129651 : Nat := 118140960795 + 129651 * 2 ^ 59
def prefixEnd_129651 : Nat := 4983230072969 + 3 ^ 40 * 129651 * 2
def baseEnd_129651 : Nat := 14794062296928327459167

theorem tailTrace_129651 : CollatzResearch.WordTrace tailWord_129651 prefixEnd_129651 14794062296928327459167 := by
  unfold tailWord_129651
  simp only [CollatzResearch.WordTrace]
  refine ⟨4728760453304044473044807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3152506968869362982029871 4728760453304044473044807)
  ·
    refine ⟨7093140679956066709567211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4728760453304044473044807 7093140679956066709567211)
    ·
      refine ⟨10639711019934100064350817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7093140679956066709567211 10639711019934100064350817)
      ·
        refine ⟨7979783264950575048263113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10639711019934100064350817 7979783264950575048263113)
        ·
          refine ⟨5984837448712931286197335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7979783264950575048263113 5984837448712931286197335)
          ·
            refine ⟨8977256173069396929296003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5984837448712931286197335 8977256173069396929296003)
            ·
              refine ⟨13465884259604095393944005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8977256173069396929296003 13465884259604095393944005)
              ·
                refine ⟨2524853298675767886364501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13465884259604095393944005 2524853298675767886364501)
                ·
                  refine ⟨14794062296928327459167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2524853298675767886364501 14794062296928327459167)
                  ·
                    rfl

theorem cell22_129651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 9].length) (baseStart_129651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129651 prefixEnd_129651 := by exact prefixLift 129651
  have htrace : WordTrace (prefixWord ++ tailWord_129651) baseStart_129651 baseEnd_129651 := by
    simpa [prefixWord, tailWord_129651, baseEnd_129651] using wordTrace_append hprefix tailTrace_129651
  have hstable : (prefixWord ++ tailWord_129651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129651).length < 2 ^ (prefixWord ++ tailWord_129651).sum := by decide
  have hdescent : baseEnd_129651 < baseStart_129651 := by decide
  rcases family_descends (prefixWord ++ tailWord_129651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129732 : List Nat := [2, 3, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_129732 : Nat := 118140960795 + 129732 * 2 ^ 59
def prefixEnd_129732 : Nat := 4983230072969 + 3 ^ 40 * 129732 * 2
def baseEnd_129732 : Nat := 44409914846127771102253

theorem tailTrace_129732 : CollatzResearch.WordTrace tailWord_129732 prefixEnd_129732 44409914846127771102253 := by
  unfold tailWord_129732
  simp only [CollatzResearch.WordTrace]
  refine ⟨2365857383005297653371725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3154476510673730204495633 2365857383005297653371725)
  ·
    refine ⟨887196518626986620014397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2365857383005297653371725 887196518626986620014397)
    ·
      refine ⟨332698694485119982505399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 887196518626986620014397 332698694485119982505399)
      ·
        refine ⟨499048041727679973758099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332698694485119982505399 499048041727679973758099)
        ·
          refine ⟨748572062591519960637149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499048041727679973758099 748572062591519960637149)
          ·
            refine ⟨280714523471819985238931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 748572062591519960637149 280714523471819985238931)
            ·
              refine ⟨421071785207729977858397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280714523471819985238931 421071785207729977858397)
              ·
                refine ⟨157901919452898741696899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421071785207729977858397 157901919452898741696899)
                ·
                  refine ⟨236852879179348112545349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157901919452898741696899 236852879179348112545349)
                  ·
                    refine ⟨44409914846127771102253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236852879179348112545349 44409914846127771102253)
                    ·
                      rfl

theorem cell22_129732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_129732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129732 prefixEnd_129732 := by exact prefixLift 129732
  have htrace : WordTrace (prefixWord ++ tailWord_129732) baseStart_129732 baseEnd_129732 := by
    simpa [prefixWord, tailWord_129732, baseEnd_129732] using wordTrace_append hprefix tailTrace_129732
  have hstable : (prefixWord ++ tailWord_129732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129732).length < 2 ^ (prefixWord ++ tailWord_129732).sum := by decide
  have hdescent : baseEnd_129732 < baseStart_129732 := by decide
  rcases family_descends (prefixWord ++ tailWord_129732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129745 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 4, 3]
def baseStart_129745 : Nat := 118140960795 + 129745 * 2 ^ 59
def prefixEnd_129745 : Nat := 4983230072969 + 3 ^ 40 * 129745 * 2
def baseEnd_129745 : Nat := 44414365011800070527213

theorem tailTrace_129745 : CollatzResearch.WordTrace tailWord_129745 prefixEnd_129745 44414365011800070527213 := by
  unfold tailWord_129745
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732188914963498526966689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3154792609975665684644459 4732188914963498526966689)
  ·
    refine ⟨3549141686222623895225017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4732188914963498526966689 3549141686222623895225017)
    ·
      refine ⟨2661856264666967921418763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3549141686222623895225017 2661856264666967921418763)
      ·
        refine ⟨3992784397000451882128145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661856264666967921418763 3992784397000451882128145)
        ·
          refine ⟨2994588297750338911596109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3992784397000451882128145 2994588297750338911596109)
          ·
            refine ⟨1122970611656377091848541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2994588297750338911596109 1122970611656377091848541)
            ·
              refine ⟨421113979371141409443203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1122970611656377091848541 421113979371141409443203)
              ·
                refine ⟨631670969056712114164805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421113979371141409443203 631670969056712114164805)
                ·
                  refine ⟨118438306698133521405901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 631670969056712114164805 118438306698133521405901)
                  ·
                    refine ⟨44414365011800070527213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118438306698133521405901 44414365011800070527213)
                    ·
                      rfl

theorem cell22_129745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_129745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129745 prefixEnd_129745 := by exact prefixLift 129745
  have htrace : WordTrace (prefixWord ++ tailWord_129745) baseStart_129745 baseEnd_129745 := by
    simpa [prefixWord, tailWord_129745, baseEnd_129745] using wordTrace_append hprefix tailTrace_129745
  have hstable : (prefixWord ++ tailWord_129745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129745).length < 2 ^ (prefixWord ++ tailWord_129745).sum := by decide
  have hdescent : baseEnd_129745 < baseStart_129745 := by decide
  rcases family_descends (prefixWord ++ tailWord_129745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129775 : List Nat := [1, 1, 2, 1, 5, 2, 4, 6]
def baseStart_129775 : Nat := 118140960795 + 129775 * 2 ^ 59
def prefixEnd_129775 : Nat := 4983230072969 + 3 ^ 40 * 129775 * 2
def baseEnd_129775 : Nat := 4936070513876665808569

theorem tailTrace_129775 : CollatzResearch.WordTrace tailWord_129775 prefixEnd_129775 4936070513876665808569 := by
  unfold tailWord_129775
  simp only [CollatzResearch.WordTrace]
  refine ⟨4733283104854813650558779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3155522069903209100372519 4733283104854813650558779)
  ·
    refine ⟨7099924657282220475838169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4733283104854813650558779 7099924657282220475838169)
    ·
      refine ⟨5324943492961665356878627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7099924657282220475838169 5324943492961665356878627)
      ·
        refine ⟨7987415239442498035317941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5324943492961665356878627 7987415239442498035317941)
        ·
          refine ⟨748820178697734190811057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7987415239442498035317941 748820178697734190811057)
          ·
            refine ⟨561615134023300643108293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 748820178697734190811057 561615134023300643108293)
            ·
              refine ⟨105302837629368870582805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 561615134023300643108293 105302837629368870582805)
              ·
                refine ⟨4936070513876665808569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105302837629368870582805 4936070513876665808569)
                ·
                  rfl

theorem cell22_129775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 6].length) (baseStart_129775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129775 prefixEnd_129775 := by exact prefixLift 129775
  have htrace : WordTrace (prefixWord ++ tailWord_129775) baseStart_129775 baseEnd_129775 := by
    simpa [prefixWord, tailWord_129775, baseEnd_129775] using wordTrace_append hprefix tailTrace_129775
  have hstable : (prefixWord ++ tailWord_129775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129775).length < 2 ^ (prefixWord ++ tailWord_129775).sum := by decide
  have hdescent : baseEnd_129775 < baseStart_129775 := by decide
  rcases family_descends (prefixWord ++ tailWord_129775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129833 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 2, 8]
def baseStart_129833 : Nat := 118140960795 + 129833 * 2 ^ 59
def prefixEnd_129833 : Nat := 4983230072969 + 3 ^ 40 * 129833 * 2
def baseEnd_129833 : Nat := 44444489210197174326943

theorem tailTrace_129833 : CollatzResearch.WordTrace tailWord_129833 prefixEnd_129833 44444489210197174326943 := by
  unfold tailWord_129833
  simp only [CollatzResearch.WordTrace]
  refine ⟨4735398538644689556170153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3156932359096459704113435 4735398538644689556170153)
  ·
    refine ⟨3551548903983517167127615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4735398538644689556170153 3551548903983517167127615)
    ·
      refine ⟨5327323355975275750691423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3551548903983517167127615 5327323355975275750691423)
      ·
        refine ⟨7990985033962913626037135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5327323355975275750691423 7990985033962913626037135)
        ·
          refine ⟨11986477550944370439055703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7990985033962913626037135 11986477550944370439055703)
          ·
            refine ⟨17979716326416555658583555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11986477550944370439055703 17979716326416555658583555)
            ·
              refine ⟨26969574489624833487875333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17979716326416555658583555 26969574489624833487875333)
              ·
                refine ⟨5056795216804656278976625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26969574489624833487875333 5056795216804656278976625)
                ·
                  refine ⟨3792596412603492209232469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5056795216804656278976625 3792596412603492209232469)
                  ·
                    refine ⟨44444489210197174326943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3792596412603492209232469 44444489210197174326943)
                    ·
                      rfl

theorem cell22_129833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_129833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129833 prefixEnd_129833 := by exact prefixLift 129833
  have htrace : WordTrace (prefixWord ++ tailWord_129833) baseStart_129833 baseEnd_129833 := by
    simpa [prefixWord, tailWord_129833, baseEnd_129833] using wordTrace_append hprefix tailTrace_129833
  have hstable : (prefixWord ++ tailWord_129833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129833).length < 2 ^ (prefixWord ++ tailWord_129833).sum := by decide
  have hdescent : baseEnd_129833 < baseStart_129833 := by decide
  rcases family_descends (prefixWord ++ tailWord_129833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129854 : List Nat := [4, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_129854 : Nat := 118140960795 + 129854 * 2 ^ 59
def prefixEnd_129854 : Nat := 4983230072969 + 3 ^ 40 * 129854 * 2
def baseEnd_129854 : Nat := 14817225979786706517293

theorem tailTrace_129854 : CollatzResearch.WordTrace tailWord_129854 prefixEnd_129854 14817225979786706517293 := by
  unfold tailWord_129854
  simp only [CollatzResearch.WordTrace]
  refine ⟨592020558946076267835577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3157442981045740095123077 592020558946076267835577)
  ·
    refine ⟨444015419209557200876683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 592020558946076267835577 444015419209557200876683)
    ·
      refine ⟨666023128814335801315025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444015419209557200876683 666023128814335801315025)
      ·
        refine ⟨499517346610751850986269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666023128814335801315025 499517346610751850986269)
        ·
          refine ⟨187319004979031944119851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 499517346610751850986269 187319004979031944119851)
          ·
            refine ⟨280978507468547916179777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187319004979031944119851 280978507468547916179777)
            ·
              refine ⟨210733880601410937134833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280978507468547916179777 210733880601410937134833)
              ·
                refine ⟨158050410451058202851125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210733880601410937134833 158050410451058202851125)
                ·
                  refine ⟨14817225979786706517293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158050410451058202851125 14817225979786706517293)
                  ·
                    rfl

theorem cell22_129854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_129854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129854 prefixEnd_129854 := by exact prefixLift 129854
  have htrace : WordTrace (prefixWord ++ tailWord_129854) baseStart_129854 baseEnd_129854 := by
    simpa [prefixWord, tailWord_129854, baseEnd_129854] using wordTrace_append hprefix tailTrace_129854
  have hstable : (prefixWord ++ tailWord_129854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129854).length < 2 ^ (prefixWord ++ tailWord_129854).sum := by decide
  have hdescent : baseEnd_129854 < baseStart_129854 := by decide
  rcases family_descends (prefixWord ++ tailWord_129854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129869 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_129869 : Nat := 118140960795 + 129869 * 2 ^ 59
def prefixEnd_129869 : Nat := 4983230072969 + 3 ^ 40 * 129869 * 2
def baseEnd_129869 : Nat := 44456812745905080426833

theorem tailTrace_129869 : CollatzResearch.WordTrace tailWord_129869 prefixEnd_129869 44456812745905080426833 := by
  unfold tailWord_129869
  simp only [CollatzResearch.WordTrace]
  refine ⟨4736711566514267704480661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3157807711009511802987107 4736711566514267704480661)
  ·
    refine ⟨222033354680356298647531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4736711566514267704480661 222033354680356298647531)
    ·
      refine ⟨333050032020534447971297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222033354680356298647531 333050032020534447971297)
      ·
        refine ⟨249787524015400835978473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333050032020534447971297 249787524015400835978473)
        ·
          refine ⟨187340643011550626983855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249787524015400835978473 187340643011550626983855)
          ·
            refine ⟨281010964517325940475783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187340643011550626983855 281010964517325940475783)
            ·
              refine ⟨421516446775988910713675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281010964517325940475783 421516446775988910713675)
              ·
                refine ⟨632274670163983366070513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421516446775988910713675 632274670163983366070513)
                ·
                  refine ⟨474206002622987524552885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632274670163983366070513 474206002622987524552885)
                  ·
                    refine ⟨44456812745905080426833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 474206002622987524552885 44456812745905080426833)
                    ·
                      rfl

theorem cell22_129869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_129869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129869 prefixEnd_129869 := by exact prefixLift 129869
  have htrace : WordTrace (prefixWord ++ tailWord_129869) baseStart_129869 baseEnd_129869 := by
    simpa [prefixWord, tailWord_129869, baseEnd_129869] using wordTrace_append hprefix tailTrace_129869
  have hstable : (prefixWord ++ tailWord_129869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129869).length < 2 ^ (prefixWord ++ tailWord_129869).sum := by decide
  have hdescent : baseEnd_129869 < baseStart_129869 := by decide
  rcases family_descends (prefixWord ++ tailWord_129869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129955 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 7]
def baseStart_129955 : Nat := 118140960795 + 129955 * 2 ^ 59
def prefixEnd_129955 : Nat := 4983230072969 + 3 ^ 40 * 129955 * 2
def baseEnd_129955 : Nat := 14828750767809840925523

theorem tailTrace_129955 : CollatzResearch.WordTrace tailWord_129955 prefixEnd_129955 14828750767809840925523 := by
  unfold tailWord_129955
  simp only [CollatzResearch.WordTrace]
  refine ⟨4739848244202704392111319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3159898829468469594740879 4739848244202704392111319)
  ·
    refine ⟨7109772366304056588166979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4739848244202704392111319 7109772366304056588166979)
    ·
      refine ⟨10664658549456084882250469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7109772366304056588166979 10664658549456084882250469)
      ·
        refine ⟨1999623478023015915421963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10664658549456084882250469 1999623478023015915421963)
        ·
          refine ⟨2999435217034523873132945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1999623478023015915421963 2999435217034523873132945)
          ·
            refine ⟨2249576412775892904849709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2999435217034523873132945 2249576412775892904849709)
            ·
              refine ⟨843591154790959839318641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2249576412775892904849709 843591154790959839318641)
              ·
                refine ⟨632693366093219879488981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843591154790959839318641 632693366093219879488981)
                ·
                  refine ⟨14828750767809840925523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 632693366093219879488981 14828750767809840925523)
                  ·
                    rfl

theorem cell22_129955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 7].length) (baseStart_129955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_129955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_129955 prefixEnd_129955 := by exact prefixLift 129955
  have htrace : WordTrace (prefixWord ++ tailWord_129955) baseStart_129955 baseEnd_129955 := by
    simpa [prefixWord, tailWord_129955, baseEnd_129955] using wordTrace_append hprefix tailTrace_129955
  have hstable : (prefixWord ++ tailWord_129955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129955).length < 2 ^ (prefixWord ++ tailWord_129955).sum := by decide
  have hdescent : baseEnd_129955 < baseStart_129955 := by decide
  rcases family_descends (prefixWord ++ tailWord_129955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130000 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 8]
def baseStart_130000 : Nat := 118140960795 + 130000 * 2 ^ 59
def prefixEnd_130000 : Nat := 4983230072969 + 3 ^ 40 * 130000 * 2
def baseEnd_130000 : Nat := 14833885574354801800477

theorem tailTrace_130000 : CollatzResearch.WordTrace tailWord_130000 prefixEnd_130000 14833885574354801800477 := by
  unfold tailWord_130000
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370744764519838538749727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3160993019359784718332969 2370744764519838538749727)
  ·
    refine ⟨3556117146779757808124591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2370744764519838538749727 3556117146779757808124591)
    ·
      refine ⟨5334175720169636712186887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3556117146779757808124591 5334175720169636712186887)
      ·
        refine ⟨8001263580254455068280331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5334175720169636712186887 8001263580254455068280331)
        ·
          refine ⟨12001895370381682602420497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8001263580254455068280331 12001895370381682602420497)
          ·
            refine ⟨9001421527786261951815373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12001895370381682602420497 9001421527786261951815373)
            ·
              refine ⟨3375533072919848231930765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9001421527786261951815373 3375533072919848231930765)
              ·
                refine ⟨1265824902344943086974037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3375533072919848231930765 1265824902344943086974037)
                ·
                  refine ⟨14833885574354801800477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1265824902344943086974037 14833885574354801800477)
                  ·
                    rfl

theorem cell22_130000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_130000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130000 prefixEnd_130000 := by exact prefixLift 130000
  have htrace : WordTrace (prefixWord ++ tailWord_130000) baseStart_130000 baseEnd_130000 := by
    simpa [prefixWord, tailWord_130000, baseEnd_130000] using wordTrace_append hprefix tailTrace_130000
  have hstable : (prefixWord ++ tailWord_130000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130000).length < 2 ^ (prefixWord ++ tailWord_130000).sum := by decide
  have hdescent : baseEnd_130000 < baseStart_130000 := by decide
  rcases family_descends (prefixWord ++ tailWord_130000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130049 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 1, 5]
def baseStart_130049 : Nat := 118140960795 + 130049 * 2 ^ 59
def prefixEnd_130049 : Nat := 4983230072969 + 3 ^ 40 * 130049 * 2
def baseEnd_130049 : Nat := 44518430424444610926281

theorem tailTrace_130049 : CollatzResearch.WordTrace tailWord_130049 prefixEnd_130049 44518430424444610926281 := by
  unfold tailWord_130049
  simp only [CollatzResearch.WordTrace]
  refine ⟨4743276705862158446033201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3162184470574772297355467 4743276705862158446033201)
  ·
    refine ⟨3557457529396618834524901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4743276705862158446033201 3557457529396618834524901)
    ·
      refine ⟨667023286761866031473419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3557457529396618834524901 667023286761866031473419)
      ·
        refine ⟨1000534930142799047210129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667023286761866031473419 1000534930142799047210129)
        ·
          refine ⟨750401197607099285407597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1000534930142799047210129 750401197607099285407597)
          ·
            refine ⟨281400449102662232027849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 750401197607099285407597 281400449102662232027849)
            ·
              refine ⟨211050336826996674020887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281400449102662232027849 211050336826996674020887)
              ·
                refine ⟨316575505240495011031331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211050336826996674020887 316575505240495011031331)
                ·
                  refine ⟨474863257860742516546997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316575505240495011031331 474863257860742516546997)
                  ·
                    refine ⟨44518430424444610926281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 474863257860742516546997 44518430424444610926281)
                    ·
                      rfl

theorem cell22_130049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_130049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130049 prefixEnd_130049 := by exact prefixLift 130049
  have htrace : WordTrace (prefixWord ++ tailWord_130049) baseStart_130049 baseEnd_130049 := by
    simpa [prefixWord, tailWord_130049, baseEnd_130049] using wordTrace_append hprefix tailTrace_130049
  have hstable : (prefixWord ++ tailWord_130049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130049).length < 2 ^ (prefixWord ++ tailWord_130049).sum := by decide
  have hdescent : baseEnd_130049 < baseStart_130049 := by decide
  rcases family_descends (prefixWord ++ tailWord_130049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130100 : List Nat := [2, 5, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_130100 : Nat := 118140960795 + 130100 * 2 ^ 59
def prefixEnd_130100 : Nat := 4983230072969 + 3 ^ 40 * 130100 * 2
def baseEnd_130100 : Nat := 44535888766697477901125

theorem tailTrace_130100 : CollatzResearch.WordTrace tailWord_130100 prefixEnd_130100 44535888766697477901125 := by
  unfold tailWord_130100
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372568414338697078069877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3163424552451596104093169 2372568414338697078069877)
  ·
    refine ⟨222428288844252851069051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2372568414338697078069877 222428288844252851069051)
    ·
      refine ⟨333642433266379276603577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222428288844252851069051 333642433266379276603577)
      ·
        refine ⟨250231824949784457452683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333642433266379276603577 250231824949784457452683)
        ·
          refine ⟨375347737424676686179025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250231824949784457452683 375347737424676686179025)
          ·
            refine ⟨281510803068507514634269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375347737424676686179025 281510803068507514634269)
            ·
              refine ⟨105566551150690317987851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281510803068507514634269 105566551150690317987851)
              ·
                refine ⟨158349826726035476981777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105566551150690317987851 158349826726035476981777)
                ·
                  refine ⟨118762370044526607736333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158349826726035476981777 118762370044526607736333)
                  ·
                    refine ⟨44535888766697477901125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118762370044526607736333 44535888766697477901125)
                    ·
                      rfl

theorem cell22_130100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_130100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130100 prefixEnd_130100 := by exact prefixLift 130100
  have htrace : WordTrace (prefixWord ++ tailWord_130100) baseStart_130100 baseEnd_130100 := by
    simpa [prefixWord, tailWord_130100, baseEnd_130100] using wordTrace_append hprefix tailTrace_130100
  have hstable : (prefixWord ++ tailWord_130100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130100).length < 2 ^ (prefixWord ++ tailWord_130100).sum := by decide
  have hdescent : baseEnd_130100 < baseStart_130100 := by decide
  rcases family_descends (prefixWord ++ tailWord_130100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130113 : List Nat := [1, 2, 5, 1, 4, 1, 2, 6]
def baseStart_130113 : Nat := 118140960795 + 130113 * 2 ^ 59
def prefixEnd_130113 : Nat := 4983230072969 + 3 ^ 40 * 130113 * 2
def baseEnd_130113 : Nat := 4948926548041086369565

theorem tailTrace_130113 : CollatzResearch.WordTrace tailWord_130113 prefixEnd_130113 4948926548041086369565 := by
  unfold tailWord_130113
  simp only [CollatzResearch.WordTrace]
  refine ⟨4745610977630297376362993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3163740651753531584241995 4745610977630297376362993)
  ·
    refine ⟨3559208233222723032272245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4745610977630297376362993 3559208233222723032272245)
    ·
      refine ⟨333675771864630284275523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3559208233222723032272245 333675771864630284275523)
      ·
        refine ⟨500513657796945426413285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333675771864630284275523 500513657796945426413285)
        ·
          refine ⟨93846310836927267452491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 500513657796945426413285 93846310836927267452491)
          ·
            refine ⟨140769466255390901178737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93846310836927267452491 140769466255390901178737)
            ·
              refine ⟨105577099691543175884053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140769466255390901178737 105577099691543175884053)
              ·
                refine ⟨4948926548041086369565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105577099691543175884053 4948926548041086369565)
                ·
                  rfl

theorem cell22_130113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 6].length) (baseStart_130113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130113 prefixEnd_130113 := by exact prefixLift 130113
  have htrace : WordTrace (prefixWord ++ tailWord_130113) baseStart_130113 baseEnd_130113 := by
    simpa [prefixWord, tailWord_130113, baseEnd_130113] using wordTrace_append hprefix tailTrace_130113
  have hstable : (prefixWord ++ tailWord_130113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130113).length < 2 ^ (prefixWord ++ tailWord_130113).sum := by decide
  have hdescent : baseEnd_130113 < baseStart_130113 := by decide
  rcases family_descends (prefixWord ++ tailWord_130113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130122 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_130122 : Nat := 118140960795 + 130122 * 2 ^ 59
def prefixEnd_130122 : Nat := 4983230072969 + 3 ^ 40 * 130122 * 2
def baseEnd_130122 : Nat := 44543419816296753851057

theorem tailTrace_130122 : CollatzResearch.WordTrace tailWord_130122 prefixEnd_130122 44543419816296753851057 := by
  unfold tailWord_130122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1186484808649422978360155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3163959489731794608960413 1186484808649422978360155)
  ·
    refine ⟨1779727212974134467540233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1186484808649422978360155 1779727212974134467540233)
    ·
      refine ⟨1334795409730600850655175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1779727212974134467540233 1334795409730600850655175)
      ·
        refine ⟨2002193114595901275982763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334795409730600850655175 2002193114595901275982763)
        ·
          refine ⟨3003289671893851913974145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002193114595901275982763 3003289671893851913974145)
          ·
            refine ⟨2252467253920388935480609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3003289671893851913974145 2252467253920388935480609)
            ·
              refine ⟨1689350440440291701610457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2252467253920388935480609 1689350440440291701610457)
              ·
                refine ⟨1267012830330218776207843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1689350440440291701610457 1267012830330218776207843)
                ·
                  refine ⟨1900519245495328164311765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267012830330218776207843 1900519245495328164311765)
                  ·
                    refine ⟨44543419816296753851057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1900519245495328164311765 44543419816296753851057)
                    ·
                      rfl

theorem cell22_130122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_130122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130122 prefixEnd_130122 := by exact prefixLift 130122
  have htrace : WordTrace (prefixWord ++ tailWord_130122) baseStart_130122 baseEnd_130122 := by
    simpa [prefixWord, tailWord_130122, baseEnd_130122] using wordTrace_append hprefix tailTrace_130122
  have hstable : (prefixWord ++ tailWord_130122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130122).length < 2 ^ (prefixWord ++ tailWord_130122).sum := by decide
  have hdescent : baseEnd_130122 < baseStart_130122 := by decide
  rcases family_descends (prefixWord ++ tailWord_130122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130158 : List Nat := [4, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_130158 : Nat := 118140960795 + 130158 * 2 ^ 59
def prefixEnd_130158 : Nat := 4983230072969 + 3 ^ 40 * 130158 * 2
def baseEnd_130158 : Nat := 14851914450668219983649

theorem tailTrace_130158 : CollatzResearch.WordTrace tailWord_130158 prefixEnd_130158 14851914450668219983649 := by
  unfold tailWord_130158
  simp only [CollatzResearch.WordTrace]
  refine ⟨593406532808408757718891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3164834841644846707834085 593406532808408757718891)
  ·
    refine ⟨890109799212613136578337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 593406532808408757718891 890109799212613136578337)
    ·
      refine ⟨667582349409459852433753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 890109799212613136578337 667582349409459852433753)
      ·
        refine ⟨500686762057094889325315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667582349409459852433753 500686762057094889325315)
        ·
          refine ⟨751030143085642333987973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500686762057094889325315 751030143085642333987973)
          ·
            refine ⟨140818151828557937622745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 751030143085642333987973 140818151828557937622745)
            ·
              refine ⟨105613613871418453217059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140818151828557937622745 105613613871418453217059)
              ·
                refine ⟨158420420807127679825589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105613613871418453217059 158420420807127679825589)
                ·
                  refine ⟨14851914450668219983649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158420420807127679825589 14851914450668219983649)
                  ·
                    rfl

theorem cell22_130158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_130158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130158 prefixEnd_130158 := by exact prefixLift 130158
  have htrace : WordTrace (prefixWord ++ tailWord_130158) baseStart_130158 baseEnd_130158 := by
    simpa [prefixWord, tailWord_130158, baseEnd_130158] using wordTrace_append hprefix tailTrace_130158
  have hstable : (prefixWord ++ tailWord_130158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130158).length < 2 ^ (prefixWord ++ tailWord_130158).sum := by decide
  have hdescent : baseEnd_130158 < baseStart_130158 := by decide
  rcases family_descends (prefixWord ++ tailWord_130158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130186 : List Nat := [3, 1, 2, 3, 1, 1, 2, 5, 4]
def baseStart_130186 : Nat := 118140960795 + 130186 * 2 ^ 59
def prefixEnd_130186 : Nat := 4983230072969 + 3 ^ 40 * 130186 * 2
def baseEnd_130186 : Nat := 14855109441407306750287

theorem tailTrace_130186 : CollatzResearch.WordTrace tailWord_130186 prefixEnd_130186 14855109441407306750287 := by
  unfold tailWord_130186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1187068376591457710942603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3165515670910553895846941 1187068376591457710942603)
  ·
    refine ⟨1780602564887186566413905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1187068376591457710942603 1780602564887186566413905)
    ·
      refine ⟨1335451923665389924810429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1780602564887186566413905 1335451923665389924810429)
      ·
        refine ⟨500794471374521221803911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1335451923665389924810429 500794471374521221803911)
        ·
          refine ⟨751191707061781832705867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500794471374521221803911 751191707061781832705867)
          ·
            refine ⟨1126787560592672749058801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751191707061781832705867 1126787560592672749058801)
            ·
              refine ⟨845090670444504561794101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126787560592672749058801 845090670444504561794101)
              ·
                refine ⟨79227250354172302668197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 845090670444504561794101 79227250354172302668197)
                ·
                  refine ⟨14855109441407306750287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79227250354172302668197 14855109441407306750287)
                  ·
                    rfl

theorem cell22_130186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_130186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130186 prefixEnd_130186 := by exact prefixLift 130186
  have htrace : WordTrace (prefixWord ++ tailWord_130186) baseStart_130186 baseEnd_130186 := by
    simpa [prefixWord, tailWord_130186, baseEnd_130186] using wordTrace_append hprefix tailTrace_130186
  have hstable : (prefixWord ++ tailWord_130186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130186).length < 2 ^ (prefixWord ++ tailWord_130186).sum := by decide
  have hdescent : baseEnd_130186 < baseStart_130186 := by decide
  rcases family_descends (prefixWord ++ tailWord_130186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130218 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 1, 5]
def baseStart_130218 : Nat := 118140960795 + 130218 * 2 ^ 59
def prefixEnd_130218 : Nat := 4983230072969 + 3 ^ 40 * 130218 * 2
def baseEnd_130218 : Nat := 44576282578184503450763

theorem tailTrace_130218 : CollatzResearch.WordTrace tailWord_130218 prefixEnd_130218 44576282578184503450763 := by
  unfold tailWord_130218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1187360160562475077233827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3166293761499933539290205 1187360160562475077233827)
  ·
    refine ⟨1781040240843712615850741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1187360160562475077233827 1781040240843712615850741)
    ·
      refine ⟨166972522579098057736007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1781040240843712615850741 166972522579098057736007)
      ·
        refine ⟨250458783868647086604011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166972522579098057736007 250458783868647086604011)
        ·
          refine ⟨375688175802970629906017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250458783868647086604011 375688175802970629906017)
          ·
            refine ⟨281766131852227972429513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375688175802970629906017 281766131852227972429513)
            ·
              refine ⟨211324598889170979322135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281766131852227972429513 211324598889170979322135)
              ·
                refine ⟨316986898333756468983203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211324598889170979322135 316986898333756468983203)
                ·
                  refine ⟨475480347500634703474805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316986898333756468983203 475480347500634703474805)
                  ·
                    refine ⟨44576282578184503450763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 475480347500634703474805 44576282578184503450763)
                    ·
                      rfl

theorem cell22_130218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_130218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130218 prefixEnd_130218 := by exact prefixLift 130218
  have htrace : WordTrace (prefixWord ++ tailWord_130218) baseStart_130218 baseEnd_130218 := by
    simpa [prefixWord, tailWord_130218, baseEnd_130218] using wordTrace_append hprefix tailTrace_130218
  have hstable : (prefixWord ++ tailWord_130218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130218).length < 2 ^ (prefixWord ++ tailWord_130218).sum := by decide
  have hdescent : baseEnd_130218 < baseStart_130218 := by decide
  rcases family_descends (prefixWord ++ tailWord_130218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130263 : List Nat := [1, 1, 3, 2, 1, 2, 4, 4, 1, 3]
def baseStart_130263 : Nat := 118140960795 + 130263 * 2 ^ 59
def prefixEnd_130263 : Nat := 4983230072969 + 3 ^ 40 * 130263 * 2
def baseEnd_130263 : Nat := 44591686997819386075625

theorem tailTrace_130263 : CollatzResearch.WordTrace tailWord_130263 prefixEnd_130263 44591686997819386075625 := by
  unfold tailWord_130263
  simp only [CollatzResearch.WordTrace]
  refine ⟨4751081927086872994323443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3167387951391248662882295 4751081927086872994323443)
  ·
    refine ⟨7126622890630309491485165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4751081927086872994323443 7126622890630309491485165)
    ·
      refine ⟨2672483583986366059306937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7126622890630309491485165 2672483583986366059306937)
      ·
        refine ⟨2004362687989774544480203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2672483583986366059306937 2004362687989774544480203)
        ·
          refine ⟨3006544031984661816720305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2004362687989774544480203 3006544031984661816720305)
          ·
            refine ⟨2254908023988496362540229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3006544031984661816720305 2254908023988496362540229)
            ·
              refine ⟨422795254497843067976293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2254908023988496362540229 422795254497843067976293)
              ·
                refine ⟨79274110218345575245555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422795254497843067976293 79274110218345575245555)
                ·
                  refine ⟨118911165327518362868333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79274110218345575245555 118911165327518362868333)
                  ·
                    refine ⟨44591686997819386075625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118911165327518362868333 44591686997819386075625)
                    ·
                      rfl

theorem cell22_130263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_130263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130263 prefixEnd_130263 := by exact prefixLift 130263
  have htrace : WordTrace (prefixWord ++ tailWord_130263) baseStart_130263 baseEnd_130263 := by
    simpa [prefixWord, tailWord_130263, baseEnd_130263] using wordTrace_append hprefix tailTrace_130263
  have hstable : (prefixWord ++ tailWord_130263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130263).length < 2 ^ (prefixWord ++ tailWord_130263).sum := by decide
  have hdescent : baseEnd_130263 < baseStart_130263 := by decide
  rcases family_descends (prefixWord ++ tailWord_130263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130372 : List Nat := [2, 3, 4, 1, 1, 1, 4, 2, 4]
def baseStart_130372 : Nat := 118140960795 + 130372 * 2 ^ 59
def prefixEnd_130372 : Nat := 4983230072969 + 3 ^ 40 * 130372 * 2
def baseEnd_130372 : Nat := 14876333308459811700097

theorem tailTrace_130372 : CollatzResearch.WordTrace tailWord_130372 prefixEnd_130372 14876333308459811700097 := by
  unfold tailWord_130372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2377528741845992305020685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3170038322461323073360913 2377528741845992305020685)
  ·
    refine ⟨891573278192247114382757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2377528741845992305020685 891573278192247114382757)
    ·
      refine ⟨167169989661046333946767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 891573278192247114382757 167169989661046333946767)
      ·
        refine ⟨250754984491569500920151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167169989661046333946767 250754984491569500920151)
        ·
          refine ⟨376132476737354251380227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250754984491569500920151 376132476737354251380227)
          ·
            refine ⟨564198715106031377070341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376132476737354251380227 564198715106031377070341)
            ·
              refine ⟨105787259082380883200689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 564198715106031377070341 105787259082380883200689)
              ·
                refine ⟨79340444311785662400517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105787259082380883200689 79340444311785662400517)
                ·
                  refine ⟨14876333308459811700097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79340444311785662400517 14876333308459811700097)
                  ·
                    rfl

theorem cell22_130372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_130372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130372 prefixEnd_130372 := by exact prefixLift 130372
  have htrace : WordTrace (prefixWord ++ tailWord_130372) baseStart_130372 baseEnd_130372 := by
    simpa [prefixWord, tailWord_130372, baseEnd_130372] using wordTrace_append hprefix tailTrace_130372
  have hstable : (prefixWord ++ tailWord_130372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130372).length < 2 ^ (prefixWord ++ tailWord_130372).sum := by decide
  have hdescent : baseEnd_130372 < baseStart_130372 := by decide
  rcases family_descends (prefixWord ++ tailWord_130372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130415 : List Nat := [1, 1, 2, 1, 3, 1, 6, 3, 1, 3]
def baseStart_130415 : Nat := 118140960795 + 130415 * 2 ^ 59
def prefixEnd_130415 : Nat := 4983230072969 + 3 ^ 40 * 130415 * 2
def baseEnd_130415 : Nat := 44643719704141656275159

theorem tailTrace_130415 : CollatzResearch.WordTrace tailWord_130415 prefixEnd_130415 44643719704141656275159 := by
  unfold tailWord_130415
  simp only [CollatzResearch.WordTrace]
  refine ⟨4756625822536202953856699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3171083881690801969237799 4756625822536202953856699)
  ·
    refine ⟨7134938733804304430785049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4756625822536202953856699 7134938733804304430785049)
    ·
      refine ⟨5351204050353228323088787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7134938733804304430785049 5351204050353228323088787)
      ·
        refine ⟨8026806075529842484633181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351204050353228323088787 8026806075529842484633181)
        ·
          refine ⟨3010052278323690931737443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8026806075529842484633181 3010052278323690931737443)
          ·
            refine ⟨4515078417485536397606165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010052278323690931737443 4515078417485536397606165)
            ·
              refine ⟨211644300819634518637789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4515078417485536397606165 211644300819634518637789)
              ·
                refine ⟨79366612807362944489171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211644300819634518637789 79366612807362944489171)
                ·
                  refine ⟨119049919211044416733757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79366612807362944489171 119049919211044416733757)
                  ·
                    refine ⟨44643719704141656275159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119049919211044416733757 44643719704141656275159)
                    ·
                      rfl

theorem cell22_130415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 1, 3].length) (baseStart_130415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130415 prefixEnd_130415 := by exact prefixLift 130415
  have htrace : WordTrace (prefixWord ++ tailWord_130415) baseStart_130415 baseEnd_130415 := by
    simpa [prefixWord, tailWord_130415, baseEnd_130415] using wordTrace_append hprefix tailTrace_130415
  have hstable : (prefixWord ++ tailWord_130415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130415).length < 2 ^ (prefixWord ++ tailWord_130415).sum := by decide
  have hdescent : baseEnd_130415 < baseStart_130415 := by decide
  rcases family_descends (prefixWord ++ tailWord_130415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130488 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 4, 3]
def baseStart_130488 : Nat := 118140960795 + 130488 * 2 ^ 59
def prefixEnd_130488 : Nat := 4983230072969 + 3 ^ 40 * 130488 * 2
def baseEnd_130488 : Nat := 44668709095993799199935

theorem tailTrace_130488 : CollatzResearch.WordTrace tailWord_130488 prefixEnd_130488 44668709095993799199935 := by
  unfold tailWord_130488
  simp only [CollatzResearch.WordTrace]
  refine ⟨2379644175635868210632059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3172858900847824280842745 2379644175635868210632059)
  ·
    refine ⟨3569466263453802315948089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2379644175635868210632059 3569466263453802315948089)
    ·
      refine ⟨2677099697590351736961067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3569466263453802315948089 2677099697590351736961067)
      ·
        refine ⟨4015649546385527605441601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677099697590351736961067 4015649546385527605441601)
        ·
          refine ⟨3011737159789145704081201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4015649546385527605441601 3011737159789145704081201)
          ·
            refine ⟨2258802869841859278060901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3011737159789145704081201 2258802869841859278060901)
            ·
              refine ⟨423525538095348614636419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2258802869841859278060901 423525538095348614636419)
              ·
                refine ⟨635288307143022921954629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423525538095348614636419 635288307143022921954629)
                ·
                  refine ⟨119116557589316797866493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 635288307143022921954629 119116557589316797866493)
                  ·
                    refine ⟨44668709095993799199935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119116557589316797866493 44668709095993799199935)
                    ·
                      rfl

theorem cell22_130488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_130488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130488 prefixEnd_130488 := by exact prefixLift 130488
  have htrace : WordTrace (prefixWord ++ tailWord_130488) baseStart_130488 baseEnd_130488 := by
    simpa [prefixWord, tailWord_130488, baseEnd_130488] using wordTrace_append hprefix tailTrace_130488
  have hstable : (prefixWord ++ tailWord_130488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130488).length < 2 ^ (prefixWord ++ tailWord_130488).sum := by decide
  have hdescent : baseEnd_130488 < baseStart_130488 := by decide
  rcases family_descends (prefixWord ++ tailWord_130488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130541 : List Nat := [1, 5, 1, 3, 3, 1, 2, 2, 4]
def baseStart_130541 : Nat := 118140960795 + 130541 * 2 ^ 59
def prefixEnd_130541 : Nat := 4983230072969 + 3 ^ 40 * 130541 * 2
def baseEnd_130541 : Nat := 14895617359706442541591

theorem tailTrace_130541 : CollatzResearch.WordTrace tailWord_130541 prefixEnd_130541 14895617359706442541591 := by
  unfold tailWord_130541
  simp only [CollatzResearch.WordTrace]
  refine ⟨4761221420079726472943477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3174147613386484315295651 4761221420079726472943477)
  ·
    refine ⟨446364508132474356838451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4761221420079726472943477 446364508132474356838451)
    ·
      refine ⟨669546762198711535257677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446364508132474356838451 669546762198711535257677)
      ·
        refine ⟨251080035824516825721629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 669546762198711535257677 251080035824516825721629)
        ·
          refine ⟨94155013434193809645611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251080035824516825721629 94155013434193809645611)
          ·
            refine ⟨141232520151290714468417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94155013434193809645611 141232520151290714468417)
            ·
              refine ⟨105924390113468035851313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141232520151290714468417 105924390113468035851313)
              ·
                refine ⟨79443292585101026888485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105924390113468035851313 79443292585101026888485)
                ·
                  refine ⟨14895617359706442541591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79443292585101026888485 14895617359706442541591)
                  ·
                    rfl

theorem cell22_130541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_130541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130541 prefixEnd_130541 := by exact prefixLift 130541
  have htrace : WordTrace (prefixWord ++ tailWord_130541) baseStart_130541 baseEnd_130541 := by
    simpa [prefixWord, tailWord_130541, baseEnd_130541] using wordTrace_append hprefix tailTrace_130541
  have hstable : (prefixWord ++ tailWord_130541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130541).length < 2 ^ (prefixWord ++ tailWord_130541).sum := by decide
  have hdescent : baseEnd_130541 < baseStart_130541 := by decide
  rcases family_descends (prefixWord ++ tailWord_130541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130584 : List Nat := [2, 1, 2, 3, 4, 1, 2, 3, 1, 3]
def baseStart_130584 : Nat := 118140960795 + 130584 * 2 ^ 59
def prefixEnd_130584 : Nat := 4983230072969 + 3 ^ 40 * 130584 * 2
def baseEnd_130584 : Nat := 44701571857881548799641

theorem tailTrace_130584 : CollatzResearch.WordTrace tailWord_130584 prefixEnd_130584 44701571857881548799641 := by
  unfold tailWord_130584
  simp only [CollatzResearch.WordTrace]
  refine ⟨2381394879461972408379403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3175193172615963211172537 2381394879461972408379403)
  ·
    refine ⟨3572092319192958612569105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2381394879461972408379403 3572092319192958612569105)
    ·
      refine ⟨2679069239394718959426829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3572092319192958612569105 2679069239394718959426829)
      ·
        refine ⟨1004650964773019609785061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2679069239394718959426829 1004650964773019609785061)
        ·
          refine ⟨188372055894941176834699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1004650964773019609785061 188372055894941176834699)
          ·
            refine ⟨282558083842411765252049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188372055894941176834699 282558083842411765252049)
            ·
              refine ⟨211918562881808823939037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282558083842411765252049 211918562881808823939037)
              ·
                refine ⟨79469461080678308977139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211918562881808823939037 79469461080678308977139)
                ·
                  refine ⟨119204191621017463465709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79469461080678308977139 119204191621017463465709)
                  ·
                    refine ⟨44701571857881548799641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119204191621017463465709 44701571857881548799641)
                    ·
                      rfl

theorem cell22_130584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_130584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130584 prefixEnd_130584 := by exact prefixLift 130584
  have htrace : WordTrace (prefixWord ++ tailWord_130584) baseStart_130584 baseEnd_130584 := by
    simpa [prefixWord, tailWord_130584, baseEnd_130584] using wordTrace_append hprefix tailTrace_130584
  have hstable : (prefixWord ++ tailWord_130584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130584).length < 2 ^ (prefixWord ++ tailWord_130584).sum := by decide
  have hdescent : baseEnd_130584 < baseStart_130584 := by decide
  rcases family_descends (prefixWord ++ tailWord_130584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130590 : List Nat := [4, 3, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_130590 : Nat := 118140960795 + 130590 * 2 ^ 59
def prefixEnd_130590 : Nat := 4983230072969 + 3 ^ 40 * 130590 * 2
def baseEnd_130590 : Nat := 44703625780499533149623

theorem tailTrace_130590 : CollatzResearch.WordTrace tailWord_130590 prefixEnd_130590 44703625780499533149623 := by
  unfold tailWord_130590
  simp only [CollatzResearch.WordTrace]
  refine ⟨595376074612775980184653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3175339064601471894318149 595376074612775980184653)
  ·
    refine ⟨223266027979790992569245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 595376074612775980184653 223266027979790992569245)
    ·
      refine ⟨83724760492421622213467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223266027979790992569245 83724760492421622213467)
      ·
        refine ⟨125587140738632433320201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83724760492421622213467 125587140738632433320201)
        ·
          refine ⟨94190355553974324990151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125587140738632433320201 94190355553974324990151)
          ·
            refine ⟨141285533330961487485227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94190355553974324990151 141285533330961487485227)
            ·
              refine ⟨211928299996442231227841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141285533330961487485227 211928299996442231227841)
              ·
                refine ⟨158946224997331673420881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211928299996442231227841 158946224997331673420881)
                ·
                  refine ⟨119209668747998755065661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158946224997331673420881 119209668747998755065661)
                  ·
                    refine ⟨44703625780499533149623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119209668747998755065661 44703625780499533149623)
                    ·
                      rfl

theorem cell22_130590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_130590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130590 prefixEnd_130590 := by exact prefixLift 130590
  have htrace : WordTrace (prefixWord ++ tailWord_130590) baseStart_130590 baseEnd_130590 := by
    simpa [prefixWord, tailWord_130590, baseEnd_130590] using wordTrace_append hprefix tailTrace_130590
  have hstable : (prefixWord ++ tailWord_130590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130590).length < 2 ^ (prefixWord ++ tailWord_130590).sum := by decide
  have hdescent : baseEnd_130590 < baseStart_130590 := by decide
  rcases family_descends (prefixWord ++ tailWord_130590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130614 : List Nat := [5, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_130614 : Nat := 118140960795 + 130614 * 2 ^ 59
def prefixEnd_130614 : Nat := 4983230072969 + 3 ^ 40 * 130614 * 2
def baseEnd_130614 : Nat := 14903947156990490183183

theorem tailTrace_130614 : CollatzResearch.WordTrace tailWord_130614 prefixEnd_130614 14903947156990490183183 := by
  unfold tailWord_130614
  simp only [CollatzResearch.WordTrace]
  refine ⟨297742746800953746271931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3175922632543506626900597 297742746800953746271931)
  ·
    refine ⟨446614120201430619407897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297742746800953746271931 446614120201430619407897)
    ·
      refine ⟨334960590151072964555923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446614120201430619407897 334960590151072964555923)
      ·
        refine ⟨502440885226609446833885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334960590151072964555923 502440885226609446833885)
        ·
          refine ⟨188415331959978542562707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502440885226609446833885 188415331959978542562707)
          ·
            refine ⟨282622997939967813844061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188415331959978542562707 282622997939967813844061)
            ·
              refine ⟨105983624227487930191523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282622997939967813844061 105983624227487930191523)
              ·
                refine ⟨158975436341231895287285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105983624227487930191523 158975436341231895287285)
                ·
                  refine ⟨14903947156990490183183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158975436341231895287285 14903947156990490183183)
                  ·
                    rfl

theorem cell22_130614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_130614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130614 prefixEnd_130614 := by exact prefixLift 130614
  have htrace : WordTrace (prefixWord ++ tailWord_130614) baseStart_130614 baseEnd_130614 := by
    simpa [prefixWord, tailWord_130614, baseEnd_130614] using wordTrace_append hprefix tailTrace_130614
  have hstable : (prefixWord ++ tailWord_130614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130614).length < 2 ^ (prefixWord ++ tailWord_130614).sum := by decide
  have hdescent : baseEnd_130614 < baseStart_130614 := by decide
  rcases family_descends (prefixWord ++ tailWord_130614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130642 : List Nat := [3, 2, 2, 1, 2, 2, 3, 3, 4]
def baseStart_130642 : Nat := 118140960795 + 130642 * 2 ^ 59
def prefixEnd_130642 : Nat := 4983230072969 + 3 ^ 40 * 130642 * 2
def baseEnd_130642 : Nat := 14907142147729576949821

theorem tailTrace_130642 : CollatzResearch.WordTrace tailWord_130642 prefixEnd_130642 14907142147729576949821 := by
  unfold tailWord_130642
  simp only [CollatzResearch.WordTrace]
  refine ⟨1191226298178455180592545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3176603461809213814913453 1191226298178455180592545)
  ·
    refine ⟨893419723633841385444409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1191226298178455180592545 893419723633841385444409)
    ·
      refine ⟨670064792725381039083307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 893419723633841385444409 670064792725381039083307)
      ·
        refine ⟨1005097189088071558624961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670064792725381039083307 1005097189088071558624961)
        ·
          refine ⟨753822891816053668968721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1005097189088071558624961 753822891816053668968721)
          ·
            refine ⟨565367168862040251726541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753822891816053668968721 565367168862040251726541)
            ·
              refine ⟨212012688323265094397453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 565367168862040251726541 212012688323265094397453)
              ·
                refine ⟨79504758121224410399045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212012688323265094397453 79504758121224410399045)
                ·
                  refine ⟨14907142147729576949821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79504758121224410399045 14907142147729576949821)
                  ·
                    rfl

theorem cell22_130642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_130642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130642 prefixEnd_130642 := by exact prefixLift 130642
  have htrace : WordTrace (prefixWord ++ tailWord_130642) baseStart_130642 baseEnd_130642 := by
    simpa [prefixWord, tailWord_130642, baseEnd_130642] using wordTrace_append hprefix tailTrace_130642
  have hstable : (prefixWord ++ tailWord_130642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130642).length < 2 ^ (prefixWord ++ tailWord_130642).sum := by decide
  have hdescent : baseEnd_130642 < baseStart_130642 := by decide
  rcases family_descends (prefixWord ++ tailWord_130642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130674 : List Nat := [3, 2, 1, 2, 3, 1, 4, 1, 2, 3]
def baseStart_130674 : Nat := 118140960795 + 130674 * 2 ^ 59
def prefixEnd_130674 : Nat := 4983230072969 + 3 ^ 40 * 130674 * 2
def baseEnd_130674 : Nat := 44732380697151314049365

theorem tailTrace_130674 : CollatzResearch.WordTrace tailWord_130674 prefixEnd_130674 44732380697151314049365 := by
  unfold tailWord_130674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1191518082149472546883769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3177381552398593458356717 1191518082149472546883769)
  ·
    refine ⟨893638561612104410162827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1191518082149472546883769 893638561612104410162827)
    ·
      refine ⟨1340457842418156615244241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 893638561612104410162827 1340457842418156615244241)
      ·
        refine ⟨1005343381813617461433181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1340457842418156615244241 1005343381813617461433181)
        ·
          refine ⟨377003768180106548037443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1005343381813617461433181 377003768180106548037443)
          ·
            refine ⟨565505652270159822056165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377003768180106548037443 565505652270159822056165)
            ·
              refine ⟨106032309800654966635531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 565505652270159822056165 106032309800654966635531)
              ·
                refine ⟨159048464700982449953297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106032309800654966635531 159048464700982449953297)
                ·
                  refine ⟨119286348525736837464973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159048464700982449953297 119286348525736837464973)
                  ·
                    refine ⟨44732380697151314049365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119286348525736837464973 44732380697151314049365)
                    ·
                      rfl

theorem cell22_130674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_130674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130674 prefixEnd_130674 := by exact prefixLift 130674
  have htrace : WordTrace (prefixWord ++ tailWord_130674) baseStart_130674 baseEnd_130674 := by
    simpa [prefixWord, tailWord_130674, baseEnd_130674] using wordTrace_append hprefix tailTrace_130674
  have hstable : (prefixWord ++ tailWord_130674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130674).length < 2 ^ (prefixWord ++ tailWord_130674).sum := by decide
  have hdescent : baseEnd_130674 < baseStart_130674 := by decide
  rcases family_descends (prefixWord ++ tailWord_130674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130745 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 3, 4]
def baseStart_130745 : Nat := 118140960795 + 130745 * 2 ^ 59
def prefixEnd_130745 : Nat := 4983230072969 + 3 ^ 40 * 130745 * 2
def baseEnd_130745 : Nat := 44756685448130795524147

theorem tailTrace_130745 : CollatzResearch.WordTrace tailWord_130745 prefixEnd_130745 44756685448130795524147 := by
  unfold tailWord_130745
  simp only [CollatzResearch.WordTrace]
  refine ⟨4768661911340669313369689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3179107940893779542246459 4768661911340669313369689)
  ·
    refine ⟨3576496433505501985027267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4768661911340669313369689 3576496433505501985027267)
    ·
      refine ⟨5364744650258252977540901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3576496433505501985027267 5364744650258252977540901)
      ·
        refine ⟨1005889621923422433288919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5364744650258252977540901 1005889621923422433288919)
        ·
          refine ⟨1508834432885133649933379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005889621923422433288919 1508834432885133649933379)
          ·
            refine ⟨2263251649327700474900069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508834432885133649933379 2263251649327700474900069)
            ·
              refine ⟨424359684248943839043763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2263251649327700474900069 424359684248943839043763)
              ·
                refine ⟨636539526373415758565645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424359684248943839043763 636539526373415758565645)
                ·
                  refine ⟨238702322390030909462117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636539526373415758565645 238702322390030909462117)
                  ·
                    refine ⟨44756685448130795524147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 238702322390030909462117 44756685448130795524147)
                    ·
                      rfl

theorem cell22_130745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_130745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130745 prefixEnd_130745 := by exact prefixLift 130745
  have htrace : WordTrace (prefixWord ++ tailWord_130745) baseStart_130745 baseEnd_130745 := by
    simpa [prefixWord, tailWord_130745, baseEnd_130745] using wordTrace_append hprefix tailTrace_130745
  have hstable : (prefixWord ++ tailWord_130745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130745).length < 2 ^ (prefixWord ++ tailWord_130745).sum := by decide
  have hdescent : baseEnd_130745 < baseStart_130745 := by decide
  rcases family_descends (prefixWord ++ tailWord_130745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130777 : List Nat := [1, 2, 1, 2, 3, 3, 2, 4, 4]
def baseStart_130777 : Nat := 118140960795 + 130777 * 2 ^ 59
def prefixEnd_130777 : Nat := 4983230072969 + 3 ^ 40 * 130777 * 2
def baseEnd_130777 : Nat := 14922546567364459574683

theorem tailTrace_130777 : CollatzResearch.WordTrace tailWord_130777 prefixEnd_130777 14922546567364459574683 := by
  unfold tailWord_130777
  simp only [CollatzResearch.WordTrace]
  refine ⟨4769829047224738778534585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3179886031483159185689723 4769829047224738778534585)
  ·
    refine ⟨3577371785418554083900939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4769829047224738778534585 3577371785418554083900939)
    ·
      refine ⟨5366057678127831125851409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3577371785418554083900939 5366057678127831125851409)
      ·
        refine ⟨4024543258595873344388557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5366057678127831125851409 4024543258595873344388557)
        ·
          refine ⟨1509203721973452504145709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4024543258595873344388557 1509203721973452504145709)
          ·
            refine ⟨565951395740044689054641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1509203721973452504145709 565951395740044689054641)
            ·
              refine ⟨424463546805033516790981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565951395740044689054641 424463546805033516790981)
              ·
                refine ⟨79586915025943784398309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 424463546805033516790981 79586915025943784398309)
                ·
                  refine ⟨14922546567364459574683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79586915025943784398309 14922546567364459574683)
                  ·
                    rfl

theorem cell22_130777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 4].length) (baseStart_130777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130777 prefixEnd_130777 := by exact prefixLift 130777
  have htrace : WordTrace (prefixWord ++ tailWord_130777) baseStart_130777 baseEnd_130777 := by
    simpa [prefixWord, tailWord_130777, baseEnd_130777] using wordTrace_append hprefix tailTrace_130777
  have hstable : (prefixWord ++ tailWord_130777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130777).length < 2 ^ (prefixWord ++ tailWord_130777).sum := by decide
  have hdescent : baseEnd_130777 < baseStart_130777 := by decide
  rcases family_descends (prefixWord ++ tailWord_130777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130792 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 1, 5]
def baseStart_130792 : Nat := 118140960795 + 130792 * 2 ^ 59
def prefixEnd_130792 : Nat := 4983230072969 + 3 ^ 40 * 130792 * 2
def baseEnd_130792 : Nat := 44772774508638339599003

theorem tailTrace_130792 : CollatzResearch.WordTrace tailWord_130792 prefixEnd_130792 44772774508638339599003 := by
  unfold tailWord_130792
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385188071085198170165315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3180250761446930893553753 2385188071085198170165315)
  ·
    refine ⟨3577782106627797255247973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2385188071085198170165315 3577782106627797255247973)
    ·
      refine ⟨670834144992711985358995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3577782106627797255247973 670834144992711985358995)
      ·
        refine ⟨1006251217489067978038493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670834144992711985358995 1006251217489067978038493)
        ·
          refine ⟨377344206558400491764435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1006251217489067978038493 377344206558400491764435)
          ·
            refine ⟨566016309837600737646653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377344206558400491764435 566016309837600737646653)
            ·
              refine ⟨212256116189100276617495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 566016309837600737646653 212256116189100276617495)
              ·
                refine ⟨318384174283650414926243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212256116189100276617495 318384174283650414926243)
                ·
                  refine ⟨477576261425475622389365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318384174283650414926243 477576261425475622389365)
                  ·
                    refine ⟨44772774508638339599003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 477576261425475622389365 44772774508638339599003)
                    ·
                      rfl

theorem cell22_130792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_130792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130792 prefixEnd_130792 := by exact prefixLift 130792
  have htrace : WordTrace (prefixWord ++ tailWord_130792) baseStart_130792 baseEnd_130792 := by
    simpa [prefixWord, tailWord_130792, baseEnd_130792] using wordTrace_append hprefix tailTrace_130792
  have hstable : (prefixWord ++ tailWord_130792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130792).length < 2 ^ (prefixWord ++ tailWord_130792).sum := by decide
  have hdescent : baseEnd_130792 < baseStart_130792 := by decide
  rcases family_descends (prefixWord ++ tailWord_130792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130888 : List Nat := [2, 1, 3, 1, 1, 6, 2, 2, 1, 3]
def baseStart_130888 : Nat := 118140960795 + 130888 * 2 ^ 59
def prefixEnd_130888 : Nat := 4983230072969 + 3 ^ 40 * 130888 * 2
def baseEnd_130888 : Nat := 44805637270526089198709

theorem tailTrace_130888 : CollatzResearch.WordTrace tailWord_130888 prefixEnd_130888 44805637270526089198709 := by
  unfold tailWord_130888
  simp only [CollatzResearch.WordTrace]
  refine ⟨2386938774911302367912659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3182585033215069823883545 2386938774911302367912659)
  ·
    refine ⟨3580408162366953551868989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2386938774911302367912659 3580408162366953551868989)
    ·
      refine ⟨1342653060887607581950871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3580408162366953551868989 1342653060887607581950871)
      ·
        refine ⟨2013979591331411372926307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342653060887607581950871 2013979591331411372926307)
        ·
          refine ⟨3020969386997117059389461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013979591331411372926307 3020969386997117059389461)
          ·
            refine ⟨141607940015489862158881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3020969386997117059389461 141607940015489862158881)
            ·
              refine ⟨106205955011617396619161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141607940015489862158881 106205955011617396619161)
              ·
                refine ⟨79654466258713047464371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106205955011617396619161 79654466258713047464371)
                ·
                  refine ⟨119481699388069571196557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79654466258713047464371 119481699388069571196557)
                  ·
                    refine ⟨44805637270526089198709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119481699388069571196557 44805637270526089198709)
                    ·
                      rfl

theorem cell22_130888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_130888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130888 prefixEnd_130888 := by exact prefixLift 130888
  have htrace : WordTrace (prefixWord ++ tailWord_130888) baseStart_130888 baseEnd_130888 := by
    simpa [prefixWord, tailWord_130888, baseEnd_130888] using wordTrace_append hprefix tailTrace_130888
  have hstable : (prefixWord ++ tailWord_130888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130888).length < 2 ^ (prefixWord ++ tailWord_130888).sum := by decide
  have hdescent : baseEnd_130888 < baseStart_130888 := by decide
  rcases family_descends (prefixWord ++ tailWord_130888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130897 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 3, 4]
def baseStart_130897 : Nat := 118140960795 + 130897 * 2 ^ 59
def prefixEnd_130897 : Nat := 4983230072969 + 3 ^ 40 * 130897 * 2
def baseEnd_130897 : Nat := 44808718154453065723681

theorem tailTrace_130897 : CollatzResearch.WordTrace tailWord_130897 prefixEnd_130897 44808718154453065723681 := by
  unfold tailWord_130897
  simp only [CollatzResearch.WordTrace]
  refine ⟨4774205806789999272902945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3182803871193332848601963 4774205806789999272902945)
  ·
    refine ⟨3580654355092499454677209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4774205806789999272902945 3580654355092499454677209)
    ·
      refine ⟨2685490766319374591007907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3580654355092499454677209 2685490766319374591007907)
      ·
        refine ⟨4028236149479061886511861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2685490766319374591007907 4028236149479061886511861)
        ·
          refine ⟨377647139013662051860487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4028236149479061886511861 377647139013662051860487)
          ·
            refine ⟨566470708520493077790731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377647139013662051860487 566470708520493077790731)
            ·
              refine ⟨849706062780739616686097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566470708520493077790731 849706062780739616686097)
              ·
                refine ⟨637279547085554712514573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849706062780739616686097 637279547085554712514573)
                ·
                  refine ⟨238979830157083017192965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637279547085554712514573 238979830157083017192965)
                  ·
                    refine ⟨44808718154453065723681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 238979830157083017192965 44808718154453065723681)
                    ·
                      rfl

theorem cell22_130897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_130897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130897 prefixEnd_130897 := by exact prefixLift 130897
  have htrace : WordTrace (prefixWord ++ tailWord_130897) baseStart_130897 baseEnd_130897 := by
    simpa [prefixWord, tailWord_130897, baseEnd_130897] using wordTrace_append hprefix tailTrace_130897
  have hstable : (prefixWord ++ tailWord_130897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130897).length < 2 ^ (prefixWord ++ tailWord_130897).sum := by decide
  have hdescent : baseEnd_130897 < baseStart_130897 := by decide
  rcases family_descends (prefixWord ++ tailWord_130897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130912 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 6]
def baseStart_130912 : Nat := 118140960795 + 130912 * 2 ^ 59
def prefixEnd_130912 : Nat := 4983230072969 + 3 ^ 40 * 130912 * 2
def baseEnd_130912 : Nat := 14937950986999342199545

theorem tailTrace_130912 : CollatzResearch.WordTrace tailWord_130912 prefixEnd_130912 14937950986999342199545 := by
  unfold tailWord_130912
  simp only [CollatzResearch.WordTrace]
  refine ⟨2387376450867828417349495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3183168601157104556465993 2387376450867828417349495)
  ·
    refine ⟨3581064676301742626024243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2387376450867828417349495 3581064676301742626024243)
    ·
      refine ⟨5371597014452613939036365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3581064676301742626024243 5371597014452613939036365)
      ·
        refine ⟨2014348880419730227138637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5371597014452613939036365 2014348880419730227138637)
        ·
          refine ⟨755380830157398835176989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2014348880419730227138637 755380830157398835176989)
          ·
            refine ⟨283267811309024563191371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 755380830157398835176989 283267811309024563191371)
            ·
              refine ⟨424901716963536844787057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283267811309024563191371 424901716963536844787057)
              ·
                refine ⟨318676287722652633590293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424901716963536844787057 318676287722652633590293)
                ·
                  refine ⟨14937950986999342199545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 318676287722652633590293 14937950986999342199545)
                  ·
                    rfl

theorem cell22_130912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 6].length) (baseStart_130912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130912 prefixEnd_130912 := by exact prefixLift 130912
  have htrace : WordTrace (prefixWord ++ tailWord_130912) baseStart_130912 baseEnd_130912 := by
    simpa [prefixWord, tailWord_130912, baseEnd_130912] using wordTrace_append hprefix tailTrace_130912
  have hstable : (prefixWord ++ tailWord_130912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130912).length < 2 ^ (prefixWord ++ tailWord_130912).sum := by decide
  have hdescent : baseEnd_130912 < baseStart_130912 := by decide
  rcases family_descends (prefixWord ++ tailWord_130912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130914 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_130914 : Nat := 118140960795 + 130914 * 2 ^ 59
def prefixEnd_130914 : Nat := 4983230072969 + 3 ^ 40 * 130914 * 2
def baseEnd_130914 : Nat := 44814537601870688048629

theorem tailTrace_130914 : CollatzResearch.WordTrace tailWord_130914 prefixEnd_130914 44814537601870688048629 := by
  unfold tailWord_130914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1193706461932102794067949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3183217231818940784181197 1193706461932102794067949)
  ·
    refine ⟨447639923224538547775481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1193706461932102794067949 447639923224538547775481)
    ·
      refine ⟨335729942418403910831611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447639923224538547775481 335729942418403910831611)
      ·
        refine ⟨503594913627605866247417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335729942418403910831611 503594913627605866247417)
        ·
          refine ⟨377696185220704399685563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503594913627605866247417 377696185220704399685563)
          ·
            refine ⟨566544277831056599528345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377696185220704399685563 566544277831056599528345)
            ·
              refine ⟨424908208373292449646259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566544277831056599528345 424908208373292449646259)
              ·
                refine ⟨637362312559938674469389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424908208373292449646259 637362312559938674469389)
                ·
                  refine ⟨239010867209977002926021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637362312559938674469389 239010867209977002926021)
                  ·
                    refine ⟨44814537601870688048629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 239010867209977002926021 44814537601870688048629)
                    ·
                      rfl

theorem cell22_130914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_130914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130914 prefixEnd_130914 := by exact prefixLift 130914
  have htrace : WordTrace (prefixWord ++ tailWord_130914) baseStart_130914 baseEnd_130914 := by
    simpa [prefixWord, tailWord_130914, baseEnd_130914] using wordTrace_append hprefix tailTrace_130914
  have hstable : (prefixWord ++ tailWord_130914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130914).length < 2 ^ (prefixWord ++ tailWord_130914).sum := by decide
  have hdescent : baseEnd_130914 < baseStart_130914 := by decide
  rcases family_descends (prefixWord ++ tailWord_130914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130929 : List Nat := [1, 2, 2, 2, 1, 3, 4, 3, 4]
def baseStart_130929 : Nat := 118140960795 + 130929 * 2 ^ 59
def prefixEnd_130929 : Nat := 4983230072969 + 3 ^ 40 * 130929 * 2
def baseEnd_130929 : Nat := 14939890802805216307861

theorem tailTrace_130929 : CollatzResearch.WordTrace tailWord_130929 prefixEnd_130929 14939890802805216307861 := by
  unfold tailWord_130929
  simp only [CollatzResearch.WordTrace]
  refine ⟨4775372942674068738067841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3183581961782712492045227 4775372942674068738067841)
  ·
    refine ⟨3581529707005551553550881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4775372942674068738067841 3581529707005551553550881)
    ·
      refine ⟨2686147280254163665163161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3581529707005551553550881 2686147280254163665163161)
      ·
        refine ⟨2014610460190622748872371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2686147280254163665163161 2014610460190622748872371)
        ·
          refine ⟨3021915690285934123308557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014610460190622748872371 3021915690285934123308557)
          ·
            refine ⟨1133218383857225296240709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3021915690285934123308557 1133218383857225296240709)
            ·
              refine ⟨212478446973229743045133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1133218383857225296240709 212478446973229743045133)
              ·
                refine ⟨79679417614961153641925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212478446973229743045133 79679417614961153641925)
                ·
                  refine ⟨14939890802805216307861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79679417614961153641925 14939890802805216307861)
                  ·
                    rfl

theorem cell22_130929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 4].length) (baseStart_130929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_130929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_130929 prefixEnd_130929 := by exact prefixLift 130929
  have htrace : WordTrace (prefixWord ++ tailWord_130929) baseStart_130929 baseEnd_130929 := by
    simpa [prefixWord, tailWord_130929, baseEnd_130929] using wordTrace_append hprefix tailTrace_130929
  have hstable : (prefixWord ++ tailWord_130929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130929).length < 2 ^ (prefixWord ++ tailWord_130929).sum := by decide
  have hdescent : baseEnd_130929 < baseStart_130929 := by decide
  rcases family_descends (prefixWord ++ tailWord_130929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131006 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_131006 : Nat := 118140960795 + 131006 * 2 ^ 59
def prefixEnd_131006 : Nat := 4983230072969 + 3 ^ 40 * 131006 * 2
def baseEnd_131006 : Nat := 44846031082013114748347

theorem tailTrace_131006 : CollatzResearch.WordTrace tailWord_131006 prefixEnd_131006 44846031082013114748347 := by
  unfold tailWord_131006
  simp only [CollatzResearch.WordTrace]
  refine ⟨597272670424388861077609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3185454242263407259080581 597272670424388861077609)
  ·
    refine ⟨447954502818291645808207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 597272670424388861077609 447954502818291645808207)
    ·
      refine ⟨671931754227437468712311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447954502818291645808207 671931754227437468712311)
      ·
        refine ⟨1007897631341156203068467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671931754227437468712311 1007897631341156203068467)
        ·
          refine ⟨1511846447011734304602701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007897631341156203068467 1511846447011734304602701)
          ·
            refine ⟨566942417629400364226013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1511846447011734304602701 566942417629400364226013)
            ·
              refine ⟨212603406611025136584755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 566942417629400364226013 212603406611025136584755)
              ·
                refine ⟨318905109916537704877133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212603406611025136584755 318905109916537704877133)
                ·
                  refine ⟨119589416218701639328925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318905109916537704877133 119589416218701639328925)
                  ·
                    refine ⟨44846031082013114748347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119589416218701639328925 44846031082013114748347)
                    ·
                      rfl

theorem cell22_131006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_131006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131006 prefixEnd_131006 := by exact prefixLift 131006
  have htrace : WordTrace (prefixWord ++ tailWord_131006) baseStart_131006 baseEnd_131006 := by
    simpa [prefixWord, tailWord_131006, baseEnd_131006] using wordTrace_append hprefix tailTrace_131006
  have hstable : (prefixWord ++ tailWord_131006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131006).length < 2 ^ (prefixWord ++ tailWord_131006).sum := by decide
  have hdescent : baseEnd_131006 < baseStart_131006 := by decide
  rcases family_descends (prefixWord ++ tailWord_131006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131053 : List Nat := [1, 5, 1, 4, 1, 1, 2, 2, 5]
def baseStart_131053 : Nat := 118140960795 + 131053 * 2 ^ 59
def prefixEnd_131053 : Nat := 4983230072969 + 3 ^ 40 * 131053 * 2
def baseEnd_131053 : Nat := 14954040047506886274401

theorem tailTrace_131053 : CollatzResearch.WordTrace tailWord_131053 prefixEnd_131053 14954040047506886274401 := by
  unfold tailWord_131053
  simp only [CollatzResearch.WordTrace]
  refine ⟨4779895594224837915581813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3186597062816558610387875 4779895594224837915581813)
  ·
    refine ⟨448115211958578554585795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4779895594224837915581813 448115211958578554585795)
    ·
      refine ⟨672172817937867831878693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448115211958578554585795 672172817937867831878693)
      ·
        refine ⟨126032403363350218477255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 672172817937867831878693 126032403363350218477255)
        ·
          refine ⟨189048605045025327715883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126032403363350218477255 189048605045025327715883)
          ·
            refine ⟨283572907567537991573825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189048605045025327715883 283572907567537991573825)
            ·
              refine ⟨212679680675653493680369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283572907567537991573825 212679680675653493680369)
              ·
                refine ⟨159509760506740120260277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212679680675653493680369 159509760506740120260277)
                ·
                  refine ⟨14954040047506886274401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159509760506740120260277 14954040047506886274401)
                  ·
                    rfl

theorem cell22_131053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_131053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131053 prefixEnd_131053 := by exact prefixLift 131053
  have htrace : WordTrace (prefixWord ++ tailWord_131053) baseStart_131053 baseEnd_131053 := by
    simpa [prefixWord, tailWord_131053, baseEnd_131053] using wordTrace_append hprefix tailTrace_131053
  have hstable : (prefixWord ++ tailWord_131053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131053).length < 2 ^ (prefixWord ++ tailWord_131053).sum := by decide
  have hdescent : baseEnd_131053 < baseStart_131053 := by decide
  rcases family_descends (prefixWord ++ tailWord_131053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131057 : List Nat := [1, 2, 2, 2, 6, 1, 2, 2, 1, 3]
def baseStart_131057 : Nat := 118140960795 + 131057 * 2 ^ 59
def prefixEnd_131057 : Nat := 4983230072969 + 3 ^ 40 * 131057 * 2
def baseEnd_131057 : Nat := 44863489424265981723191

theorem tailTrace_131057 : CollatzResearch.WordTrace tailWord_131057 prefixEnd_131057 44863489424265981723191 := by
  unfold tailWord_131057
  simp only [CollatzResearch.WordTrace]
  refine ⟨4780041486210346598727425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3186694324140231065818283 4780041486210346598727425)
  ·
    refine ⟨3585031114657759949045569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4780041486210346598727425 3585031114657759949045569)
    ·
      refine ⟨2688773335993319961784177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3585031114657759949045569 2688773335993319961784177)
      ·
        refine ⟨2016580001994989971338133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2688773335993319961784177 2016580001994989971338133)
        ·
          refine ⟨94527187593515154906475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2016580001994989971338133 94527187593515154906475)
          ·
            refine ⟨141790781390272732359713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94527187593515154906475 141790781390272732359713)
            ·
              refine ⟨106343086042704549269785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141790781390272732359713 106343086042704549269785)
              ·
                refine ⟨79757314532028411952339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106343086042704549269785 79757314532028411952339)
                ·
                  refine ⟨119635971798042617928509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79757314532028411952339 119635971798042617928509)
                  ·
                    refine ⟨44863489424265981723191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119635971798042617928509 44863489424265981723191)
                    ·
                      rfl

theorem cell22_131057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_131057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131057 prefixEnd_131057 := by exact prefixLift 131057
  have htrace : WordTrace (prefixWord ++ tailWord_131057) baseStart_131057 baseEnd_131057 := by
    simpa [prefixWord, tailWord_131057, baseEnd_131057] using wordTrace_append hprefix tailTrace_131057
  have hstable : (prefixWord ++ tailWord_131057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131057).length < 2 ^ (prefixWord ++ tailWord_131057).sum := by decide
  have hdescent : baseEnd_131057 < baseStart_131057 := by decide
  rcases family_descends (prefixWord ++ tailWord_131057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131079 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 1, 5]
def baseStart_131079 : Nat := 118140960795 + 131079 * 2 ^ 59
def prefixEnd_131079 : Nat := 4983230072969 + 3 ^ 40 * 131079 * 2
def baseEnd_131079 : Nat := 44871020473865257673123

theorem tailTrace_131079 : CollatzResearch.WordTrace tailWord_131079 prefixEnd_131079 44871020473865257673123 := by
  unfold tailWord_131079
  simp only [CollatzResearch.WordTrace]
  refine ⟨4780843892130644356028291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3187229261420429570685527 4780843892130644356028291)
  ·
    refine ⟨7171265838195966534042437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4780843892130644356028291 7171265838195966534042437)
    ·
      refine ⟨1344612344661743725132957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7171265838195966534042437 1344612344661743725132957)
      ·
        refine ⟨504229629248153896924859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1344612344661743725132957 504229629248153896924859)
        ·
          refine ⟨756344443872230845387289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504229629248153896924859 756344443872230845387289)
          ·
            refine ⟨567258332904173134040467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756344443872230845387289 567258332904173134040467)
            ·
              refine ⟨850887499356259701060701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567258332904173134040467 850887499356259701060701)
              ·
                refine ⟨319082812258597387897763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 850887499356259701060701 319082812258597387897763)
                ·
                  refine ⟨478624218387896081846645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319082812258597387897763 478624218387896081846645)
                  ·
                    refine ⟨44871020473865257673123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 478624218387896081846645 44871020473865257673123)
                    ·
                      rfl

theorem cell22_131079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_131079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131079 prefixEnd_131079 := by exact prefixLift 131079
  have htrace : WordTrace (prefixWord ++ tailWord_131079) baseStart_131079 baseEnd_131079 := by
    simpa [prefixWord, tailWord_131079, baseEnd_131079] using wordTrace_append hprefix tailTrace_131079
  have hstable : (prefixWord ++ tailWord_131079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131079).length < 2 ^ (prefixWord ++ tailWord_131079).sum := by decide
  have hdescent : baseEnd_131079 < baseStart_131079 := by decide
  rcases family_descends (prefixWord ++ tailWord_131079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131175 : List Nat := [1, 1, 5, 1, 1, 2, 5, 2, 1, 3]
def baseStart_131175 : Nat := 118140960795 + 131175 * 2 ^ 59
def prefixEnd_131175 : Nat := 4983230072969 + 3 ^ 40 * 131175 * 2
def baseEnd_131175 : Nat := 44903883235753007272829

theorem tailTrace_131175 : CollatzResearch.WordTrace tailWord_131175 prefixEnd_131175 44903883235753007272829 := by
  unfold tailWord_131175
  simp only [CollatzResearch.WordTrace]
  refine ⟨4784345299782852751522979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3189563533188568501015319 4784345299782852751522979)
  ·
    refine ⟨7176517949674279127284469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4784345299782852751522979 7176517949674279127284469)
    ·
      refine ⟨672798557781963668182919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7176517949674279127284469 672798557781963668182919)
      ·
        refine ⟨1009197836672945502274379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672798557781963668182919 1009197836672945502274379)
        ·
          refine ⟨1513796755009418253411569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009197836672945502274379 1513796755009418253411569)
          ·
            refine ⟨1135347566257063690058677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1513796755009418253411569 1135347566257063690058677)
            ·
              refine ⟨106438834336599720943001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1135347566257063690058677 106438834336599720943001)
              ·
                refine ⟨79829125752449790707251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106438834336599720943001 79829125752449790707251)
                ·
                  refine ⟨119743688628674686060877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79829125752449790707251 119743688628674686060877)
                  ·
                    refine ⟨44903883235753007272829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119743688628674686060877 44903883235753007272829)
                    ·
                      rfl

theorem cell22_131175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_131175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131175 prefixEnd_131175 := by exact prefixLift 131175
  have htrace : WordTrace (prefixWord ++ tailWord_131175) baseStart_131175 baseEnd_131175 := by
    simpa [prefixWord, tailWord_131175, baseEnd_131175] using wordTrace_append hprefix tailTrace_131175
  have hstable : (prefixWord ++ tailWord_131175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131175).length < 2 ^ (prefixWord ++ tailWord_131175).sum := by decide
  have hdescent : baseEnd_131175 < baseStart_131175 := by decide
  rcases family_descends (prefixWord ++ tailWord_131175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131216 : List Nat := [2, 1, 1, 1, 1, 1, 6, 5, 4]
def baseStart_131216 : Nat := 118140960795 + 131216 * 2 ^ 59
def prefixEnd_131216 : Nat := 4983230072969 + 3 ^ 40 * 131216 * 2
def baseEnd_131216 : Nat := 14972639457880855665901

theorem tailTrace_131216 : CollatzResearch.WordTrace tailWord_131216 prefixEnd_131216 14972639457880855665901 := by
  unfold tailWord_131216
  simp only [CollatzResearch.WordTrace]
  refine ⟨2392920346317158376882751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3190560461756211169177001 2392920346317158376882751)
  ·
    refine ⟨3589380519475737565324127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2392920346317158376882751 3589380519475737565324127)
    ·
      refine ⟨5384070779213606347986191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3589380519475737565324127 5384070779213606347986191)
      ·
        refine ⟨8076106168820409521979287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5384070779213606347986191 8076106168820409521979287)
        ·
          refine ⟨12114159253230614282968931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8076106168820409521979287 12114159253230614282968931)
          ·
            refine ⟨18171238879845921424453397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12114159253230614282968931 18171238879845921424453397)
            ·
              refine ⟨851776822492777566771253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18171238879845921424453397 851776822492777566771253)
              ·
                refine ⟨79854077108697896884805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 851776822492777566771253 79854077108697896884805)
                ·
                  refine ⟨14972639457880855665901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79854077108697896884805 14972639457880855665901)
                  ·
                    rfl

theorem cell22_131216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 4].length) (baseStart_131216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131216 prefixEnd_131216 := by exact prefixLift 131216
  have htrace : WordTrace (prefixWord ++ tailWord_131216) baseStart_131216 baseEnd_131216 := by
    simpa [prefixWord, tailWord_131216, baseEnd_131216] using wordTrace_append hprefix tailTrace_131216
  have hstable : (prefixWord ++ tailWord_131216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131216).length < 2 ^ (prefixWord ++ tailWord_131216).sum := by decide
  have hdescent : baseEnd_131216 < baseStart_131216 := by decide
  rcases family_descends (prefixWord ++ tailWord_131216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131233 : List Nat := [1, 2, 3, 3, 1, 3, 1, 4, 4]
def baseStart_131233 : Nat := 118140960795 + 131233 * 2 ^ 59
def prefixEnd_131233 : Nat := 4983230072969 + 3 ^ 40 * 131233 * 2
def baseEnd_131233 : Nat := 14974579273686729774217

theorem tailTrace_131233 : CollatzResearch.WordTrace tailWord_131233 prefixEnd_131233 14974579273686729774217 := by
  unfold tailWord_131233
  simp only [CollatzResearch.WordTrace]
  refine ⟨4786460733572728657134353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3190973822381819104756235 4786460733572728657134353)
  ·
    refine ⟨3589845550179546492850765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4786460733572728657134353 3589845550179546492850765)
    ·
      refine ⟨1346192081317329934819037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3589845550179546492850765 1346192081317329934819037)
      ·
        refine ⟨504822030493998725557139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1346192081317329934819037 504822030493998725557139)
        ·
          refine ⟨757233045740998088335709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504822030493998725557139 757233045740998088335709)
          ·
            refine ⟨283962392152874283125891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 757233045740998088335709 283962392152874283125891)
            ·
              refine ⟨425943588229311424688837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283962392152874283125891 425943588229311424688837)
              ·
                refine ⟨79864422792995892129157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425943588229311424688837 79864422792995892129157)
                ·
                  refine ⟨14974579273686729774217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79864422792995892129157 14974579273686729774217)
                  ·
                    rfl

theorem cell22_131233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 4].length) (baseStart_131233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131233 prefixEnd_131233 := by exact prefixLift 131233
  have htrace : WordTrace (prefixWord ++ tailWord_131233) baseStart_131233 baseEnd_131233 := by
    simpa [prefixWord, tailWord_131233, baseEnd_131233] using wordTrace_append hprefix tailTrace_131233
  have hstable : (prefixWord ++ tailWord_131233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131233).length < 2 ^ (prefixWord ++ tailWord_131233).sum := by decide
  have hdescent : baseEnd_131233 < baseStart_131233 := by decide
  rcases family_descends (prefixWord ++ tailWord_131233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131357 : List Nat := [1, 4, 2, 3, 2, 2, 2, 1, 5]
def baseStart_131357 : Nat := 118140960795 + 131357 * 2 ^ 59
def prefixEnd_131357 : Nat := 4983230072969 + 3 ^ 40 * 131357 * 2
def baseEnd_131357 : Nat := 14988728518388399740757

theorem tailTrace_131357 : CollatzResearch.WordTrace tailWord_131357 prefixEnd_131357 14988728518388399740757 := by
  unfold tailWord_131357
  simp only [CollatzResearch.WordTrace]
  refine ⟨4790983385123497834648325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3193988923415665223098883 4790983385123497834648325)
  ·
    refine ⟨898309384710655843996561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4790983385123497834648325 898309384710655843996561)
    ·
      refine ⟨673732038532991882997421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 898309384710655843996561 673732038532991882997421)
      ·
        refine ⟨252649514449871956124033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 673732038532991882997421 252649514449871956124033)
        ·
          refine ⟨189487135837403967093025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252649514449871956124033 189487135837403967093025)
          ·
            refine ⟨142115351878052975319769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189487135837403967093025 142115351878052975319769)
            ·
              refine ⟨106586513908539731489827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142115351878052975319769 106586513908539731489827)
              ·
                refine ⟨159879770862809597234741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106586513908539731489827 159879770862809597234741)
                ·
                  refine ⟨14988728518388399740757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159879770862809597234741 14988728518388399740757)
                  ·
                    rfl

theorem cell22_131357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_131357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131357 prefixEnd_131357 := by exact prefixLift 131357
  have htrace : WordTrace (prefixWord ++ tailWord_131357) baseStart_131357 baseEnd_131357 := by
    simpa [prefixWord, tailWord_131357, baseEnd_131357] using wordTrace_append hprefix tailTrace_131357
  have hstable : (prefixWord ++ tailWord_131357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131357).length < 2 ^ (prefixWord ++ tailWord_131357).sum := by decide
  have hdescent : baseEnd_131357 < baseStart_131357 := by decide
  rcases family_descends (prefixWord ++ tailWord_131357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131370 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 3, 4]
def baseStart_131370 : Nat := 118140960795 + 131370 * 2 ^ 59
def prefixEnd_131370 : Nat := 4983230072969 + 3 ^ 40 * 131370 * 2
def baseEnd_131370 : Nat := 44970635720837498647231

theorem tailTrace_131370 : CollatzResearch.WordTrace tailWord_131370 prefixEnd_131370 44970635720837498647231 := by
  unfold tailWord_131370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1197864383519100263717891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3194305022717600703247709 1197864383519100263717891)
  ·
    refine ⟨1796796575278650395576837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1197864383519100263717891 1796796575278650395576837)
    ·
      refine ⟨336899357864746949170657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1796796575278650395576837 336899357864746949170657)
      ·
        refine ⟨252674518398560211877993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336899357864746949170657 252674518398560211877993)
        ·
          refine ⟨189505888798920158908495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252674518398560211877993 189505888798920158908495)
          ·
            refine ⟨284258833198380238362743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189505888798920158908495 284258833198380238362743)
            ·
              refine ⟨426388249797570357544115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284258833198380238362743 426388249797570357544115)
              ·
                refine ⟨639582374696355536316173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426388249797570357544115 639582374696355536316173)
                ·
                  refine ⟨239843390511133326118565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639582374696355536316173 239843390511133326118565)
                  ·
                    refine ⟨44970635720837498647231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 239843390511133326118565 44970635720837498647231)
                    ·
                      rfl

theorem cell22_131370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_131370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131370 prefixEnd_131370 := by exact prefixLift 131370
  have htrace : WordTrace (prefixWord ++ tailWord_131370) baseStart_131370 baseEnd_131370 := by
    simpa [prefixWord, tailWord_131370, baseEnd_131370] using wordTrace_append hprefix tailTrace_131370
  have hstable : (prefixWord ++ tailWord_131370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131370).length < 2 ^ (prefixWord ++ tailWord_131370).sum := by decide
  have hdescent : baseEnd_131370 < baseStart_131370 := by decide
  rcases family_descends (prefixWord ++ tailWord_131370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131441 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 7]
def baseStart_131441 : Nat := 118140960795 + 131441 * 2 ^ 59
def prefixEnd_131441 : Nat := 4983230072969 + 3 ^ 40 * 131441 * 2
def baseEnd_131441 : Nat := 14998313490605660040671

theorem tailTrace_131441 : CollatzResearch.WordTrace tailWord_131441 prefixEnd_131441 14998313490605660040671 := by
  unfold tailWord_131441
  simp only [CollatzResearch.WordTrace]
  refine ⟨4794047116819180180706177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3196031411212786787137451 4794047116819180180706177)
  ·
    refine ⟨3595535337614385135529633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4794047116819180180706177 3595535337614385135529633)
    ·
      refine ⟨2696651503210788851647225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3595535337614385135529633 2696651503210788851647225)
      ·
        refine ⟨2022488627408091638735419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2696651503210788851647225 2022488627408091638735419)
        ·
          refine ⟨3033732941112137458103129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2022488627408091638735419 3033732941112137458103129)
          ·
            refine ⟨2275299705834103093577347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3033732941112137458103129 2275299705834103093577347)
            ·
              refine ⟨3412949558751154640366021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2275299705834103093577347 3412949558751154640366021)
              ·
                refine ⟨639928042265841495068629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3412949558751154640366021 639928042265841495068629)
                ·
                  refine ⟨14998313490605660040671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 639928042265841495068629 14998313490605660040671)
                  ·
                    rfl

theorem cell22_131441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_131441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131441 prefixEnd_131441 := by exact prefixLift 131441
  have htrace : WordTrace (prefixWord ++ tailWord_131441) baseStart_131441 baseEnd_131441 := by
    simpa [prefixWord, tailWord_131441, baseEnd_131441] using wordTrace_append hprefix tailTrace_131441
  have hstable : (prefixWord ++ tailWord_131441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131441).length < 2 ^ (prefixWord ++ tailWord_131441).sum := by decide
  have hdescent : baseEnd_131441 < baseStart_131441 := by decide
  rcases family_descends (prefixWord ++ tailWord_131441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131496 : List Nat := [2, 1, 6, 1, 1, 3, 1, 3, 1, 3]
def baseStart_131496 : Nat := 118140960795 + 131496 * 2 ^ 59
def prefixEnd_131496 : Nat := 4983230072969 + 3 ^ 40 * 131496 * 2
def baseEnd_131496 : Nat := 45013768095815169996845

theorem tailTrace_131496 : CollatzResearch.WordTrace tailWord_131496 prefixEnd_131496 45013768095815169996845 := by
  unfold tailWord_131496
  simp only [CollatzResearch.WordTrace]
  refine ⟨2398026565809962286979171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3197368754413283049305561 2398026565809962286979171)
  ·
    refine ⟨3597039848714943430468757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2398026565809962286979171 3597039848714943430468757)
    ·
      refine ⟨168611242908512973303223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3597039848714943430468757 168611242908512973303223)
      ·
        refine ⟨252916864362769459954835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168611242908512973303223 252916864362769459954835)
        ·
          refine ⟨379375296544154189932253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252916864362769459954835 379375296544154189932253)
          ·
            refine ⟨142265736204057821224595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379375296544154189932253 142265736204057821224595)
            ·
              refine ⟨213398604306086731836893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142265736204057821224595 213398604306086731836893)
              ·
                refine ⟨80024476614782524438835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213398604306086731836893 80024476614782524438835)
                ·
                  refine ⟨120036714922173786658253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80024476614782524438835 120036714922173786658253)
                  ·
                    refine ⟨45013768095815169996845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120036714922173786658253 45013768095815169996845)
                    ·
                      rfl

theorem cell22_131496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_131496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131496 prefixEnd_131496 := by exact prefixLift 131496
  have htrace : WordTrace (prefixWord ++ tailWord_131496) baseStart_131496 baseEnd_131496 := by
    simpa [prefixWord, tailWord_131496, baseEnd_131496] using wordTrace_append hprefix tailTrace_131496
  have hstable : (prefixWord ++ tailWord_131496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131496).length < 2 ^ (prefixWord ++ tailWord_131496).sum := by decide
  have hdescent : baseEnd_131496 < baseStart_131496 := by decide
  rcases family_descends (prefixWord ++ tailWord_131496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131505 : List Nat := [1, 2, 2, 4, 1, 2, 2, 3, 1, 4]
def baseStart_131505 : Nat := 118140960795 + 131505 * 2 ^ 59
def prefixEnd_131505 : Nat := 4983230072969 + 3 ^ 40 * 131505 * 2
def baseEnd_131505 : Nat := 45016848979742146521817

theorem tailTrace_131505 : CollatzResearch.WordTrace tailWord_131505 prefixEnd_131505 45016848979742146521817 := by
  unfold tailWord_131505
  simp only [CollatzResearch.WordTrace]
  refine ⟨4796381388587319111035969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3197587592391546074023979 4796381388587319111035969)
  ·
    refine ⟨3597286041440489333276977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4796381388587319111035969 3597286041440489333276977)
    ·
      refine ⟨2697964531080366999957733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3597286041440489333276977 2697964531080366999957733)
      ·
        refine ⟨505868349577568812492075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2697964531080366999957733 505868349577568812492075)
        ·
          refine ⟨758802524366353218738113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505868349577568812492075 758802524366353218738113)
          ·
            refine ⟨569101893274764914053585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758802524366353218738113 569101893274764914053585)
            ·
              refine ⟨426826419956073685540189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 569101893274764914053585 426826419956073685540189)
              ·
                refine ⟨160059907483527632077571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426826419956073685540189 160059907483527632077571)
                ·
                  refine ⟨240089861225291448116357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160059907483527632077571 240089861225291448116357)
                  ·
                    refine ⟨45016848979742146521817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 240089861225291448116357 45016848979742146521817)
                    ·
                      rfl

theorem cell22_131505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_131505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131505 prefixEnd_131505 := by exact prefixLift 131505
  have htrace : WordTrace (prefixWord ++ tailWord_131505) baseStart_131505 baseEnd_131505 := by
    simpa [prefixWord, tailWord_131505, baseEnd_131505] using wordTrace_append hprefix tailTrace_131505
  have hstable : (prefixWord ++ tailWord_131505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131505).length < 2 ^ (prefixWord ++ tailWord_131505).sum := by decide
  have hdescent : baseEnd_131505 < baseStart_131505 := by decide
  rcases family_descends (prefixWord ++ tailWord_131505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131580 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 3, 3]
def baseStart_131580 : Nat := 118140960795 + 131580 * 2 ^ 59
def prefixEnd_131580 : Nat := 4983230072969 + 3 ^ 40 * 131580 * 2
def baseEnd_131580 : Nat := 45042523012466950896587

theorem tailTrace_131580 : CollatzResearch.WordTrace tailWord_131580 prefixEnd_131580 45042523012466950896587 := by
  unfold tailWord_131580
  simp only [CollatzResearch.WordTrace]
  refine ⟨2399558431657803460008097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3199411242210404613344129 2399558431657803460008097)
  ·
    refine ⟨1799668823743352595006073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2399558431657803460008097 1799668823743352595006073)
    ·
      refine ⟨1349751617807514446254555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1799668823743352595006073 1349751617807514446254555)
      ·
        refine ⟨2024627426711271669381833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1349751617807514446254555 2024627426711271669381833)
        ·
          refine ⟨1518470570033453752036375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2024627426711271669381833 1518470570033453752036375)
          ·
            refine ⟨2277705855050180628054563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1518470570033453752036375 2277705855050180628054563)
            ·
              refine ⟨3416558782575270942081845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2277705855050180628054563 3416558782575270942081845)
              ·
                refine ⟨320302385866431650820173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3416558782575270942081845 320302385866431650820173)
                ·
                  refine ⟨120113394699911869057565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320302385866431650820173 120113394699911869057565)
                  ·
                    refine ⟨45042523012466950896587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120113394699911869057565 45042523012466950896587)
                    ·
                      rfl

theorem cell22_131580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_131580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131580 prefixEnd_131580 := by exact prefixLift 131580
  have htrace : WordTrace (prefixWord ++ tailWord_131580) baseStart_131580 baseEnd_131580 := by
    simpa [prefixWord, tailWord_131580, baseEnd_131580] using wordTrace_append hprefix tailTrace_131580
  have hstable : (prefixWord ++ tailWord_131580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131580).length < 2 ^ (prefixWord ++ tailWord_131580).sum := by decide
  have hdescent : baseEnd_131580 < baseStart_131580 := by decide
  rcases family_descends (prefixWord ++ tailWord_131580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131655 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 6]
def baseStart_131655 : Nat := 118140960795 + 131655 * 2 ^ 59
def prefixEnd_131655 : Nat := 4983230072969 + 3 ^ 40 * 131655 * 2
def baseEnd_131655 : Nat := 15022732348397251757119

theorem tailTrace_131655 : CollatzResearch.WordTrace tailWord_131655 prefixEnd_131655 15022732348397251757119 := by
  unfold tailWord_131655
  simp only [CollatzResearch.WordTrace]
  refine ⟨4801852338043894728996419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3201234892029263152664279 4801852338043894728996419)
  ·
    refine ⟨7202778507065842093494629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4801852338043894728996419 7202778507065842093494629)
    ·
      refine ⟨1350520970074845392530243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7202778507065842093494629 1350520970074845392530243)
      ·
        refine ⟨2025781455112268088795365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1350520970074845392530243 2025781455112268088795365)
        ·
          refine ⟨379834022833550266649131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2025781455112268088795365 379834022833550266649131)
          ·
            refine ⟨569751034250325399973697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379834022833550266649131 569751034250325399973697)
            ·
              refine ⟨427313275687744049980273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 569751034250325399973697 427313275687744049980273)
              ·
                refine ⟨320484956765808037485205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427313275687744049980273 320484956765808037485205)
                ·
                  refine ⟨15022732348397251757119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 320484956765808037485205 15022732348397251757119)
                  ·
                    rfl

theorem cell22_131655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 6].length) (baseStart_131655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131655 prefixEnd_131655 := by exact prefixLift 131655
  have htrace : WordTrace (prefixWord ++ tailWord_131655) baseStart_131655 baseEnd_131655 := by
    simpa [prefixWord, tailWord_131655, baseEnd_131655] using wordTrace_append hprefix tailTrace_131655
  have hstable : (prefixWord ++ tailWord_131655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131655).length < 2 ^ (prefixWord ++ tailWord_131655).sum := by decide
  have hdescent : baseEnd_131655 < baseStart_131655 := by decide
  rcases family_descends (prefixWord ++ tailWord_131655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131672 : List Nat := [2, 1, 2, 2, 1, 2, 5, 3, 4]
def baseStart_131672 : Nat := 118140960795 + 131672 * 2 ^ 59
def prefixEnd_131672 : Nat := 4983230072969 + 3 ^ 40 * 131672 * 2
def baseEnd_131672 : Nat := 15024672164203125865435

theorem tailTrace_131672 : CollatzResearch.WordTrace tailWord_131672 prefixEnd_131672 15024672164203125865435 := by
  unfold tailWord_131672
  simp only [CollatzResearch.WordTrace]
  refine ⟨2401236189491153316182635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3201648252654871088243513 2401236189491153316182635)
  ·
    refine ⟨3601854284236729974273953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2401236189491153316182635 3601854284236729974273953)
    ·
      refine ⟨2701390713177547480705465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3601854284236729974273953 2701390713177547480705465)
      ·
        refine ⟨2026043034883160610529099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2701390713177547480705465 2026043034883160610529099)
        ·
          refine ⟨3039064552324740915793649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026043034883160610529099 3039064552324740915793649)
          ·
            refine ⟨2279298414243555686845237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3039064552324740915793649 2279298414243555686845237)
            ·
              refine ⟨213684226335333345641741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2279298414243555686845237 213684226335333345641741)
              ·
                refine ⟨80131584875750004615653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213684226335333345641741 80131584875750004615653)
                ·
                  refine ⟨15024672164203125865435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80131584875750004615653 15024672164203125865435)
                  ·
                    rfl

theorem cell22_131672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 4].length) (baseStart_131672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131672 prefixEnd_131672 := by exact prefixLift 131672
  have htrace : WordTrace (prefixWord ++ tailWord_131672) baseStart_131672 baseEnd_131672 := by
    simpa [prefixWord, tailWord_131672, baseEnd_131672] using wordTrace_append hprefix tailTrace_131672
  have hstable : (prefixWord ++ tailWord_131672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131672).length < 2 ^ (prefixWord ++ tailWord_131672).sum := by decide
  have hdescent : baseEnd_131672 < baseStart_131672 := by decide
  rcases family_descends (prefixWord ++ tailWord_131672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131687 : List Nat := [1, 1, 5, 1, 1, 1, 1, 6, 2, 3]
def baseStart_131687 : Nat := 118140960795 + 131687 * 2 ^ 59
def prefixEnd_131687 : Nat := 4983230072969 + 3 ^ 40 * 131687 * 2
def baseEnd_131687 : Nat := 45079151299154338471259

theorem tailTrace_131687 : CollatzResearch.WordTrace tailWord_131687 prefixEnd_131687 45079151299154338471259 := by
  unfold tailWord_131687
  simp only [CollatzResearch.WordTrace]
  refine ⟨4803019473927964194161315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3202012982618642796107543 4803019473927964194161315)
  ·
    refine ⟨7204529210891946291241973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4803019473927964194161315 7204529210891946291241973)
    ·
      refine ⟨675424613521119964803935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7204529210891946291241973 675424613521119964803935)
      ·
        refine ⟨1013136920281679947205903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675424613521119964803935 1013136920281679947205903)
        ·
          refine ⟨1519705380422519920808855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013136920281679947205903 1519705380422519920808855)
          ·
            refine ⟨2279558070633779881213283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519705380422519920808855 2279558070633779881213283)
            ·
              refine ⟨3419337105950669821819925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2279558070633779881213283 3419337105950669821819925)
              ·
                refine ⟨160281426841437647897809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3419337105950669821819925 160281426841437647897809)
                ·
                  refine ⟨120211070131078235923357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160281426841437647897809 120211070131078235923357)
                  ·
                    refine ⟨45079151299154338471259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120211070131078235923357 45079151299154338471259)
                    ·
                      rfl

theorem cell22_131687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_131687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131687 prefixEnd_131687 := by exact prefixLift 131687
  have htrace : WordTrace (prefixWord ++ tailWord_131687) baseStart_131687 baseEnd_131687 := by
    simpa [prefixWord, tailWord_131687, baseEnd_131687] using wordTrace_append hprefix tailTrace_131687
  have hstable : (prefixWord ++ tailWord_131687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131687).length < 2 ^ (prefixWord ++ tailWord_131687).sum := by decide
  have hdescent : baseEnd_131687 < baseStart_131687 := by decide
  rcases family_descends (prefixWord ++ tailWord_131687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131751 : List Nat := [1, 1, 6, 3, 2, 1, 1, 7]
def baseStart_131751 : Nat := 118140960795 + 131751 * 2 ^ 59
def prefixEnd_131751 : Nat := 4983230072969 + 3 ^ 40 * 131751 * 2
def baseEnd_131751 : Nat := 5011228867453278319007

theorem tailTrace_131751 : CollatzResearch.WordTrace tailWord_131751 prefixEnd_131751 5011228867453278319007 := by
  unfold tailWord_131751
  simp only [CollatzResearch.WordTrace]
  refine ⟨4805353745696103124491107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3203569163797402082994071 4805353745696103124491107)
  ·
    refine ⟨7208030618544154686736661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4805353745696103124491107 7208030618544154686736661)
    ·
      refine ⟨337876435244257250940781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7208030618544154686736661 337876435244257250940781)
      ·
        refine ⟨126703663216596469102793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337876435244257250940781 126703663216596469102793)
        ·
          refine ⟨95027747412447351827095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126703663216596469102793 95027747412447351827095)
          ·
            refine ⟨142541621118671027740643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95027747412447351827095 142541621118671027740643)
            ·
              refine ⟨213812431678006541610965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142541621118671027740643 213812431678006541610965)
              ·
                refine ⟨5011228867453278319007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 213812431678006541610965 5011228867453278319007)
                ·
                  rfl

theorem cell22_131751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 7].length) (baseStart_131751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131751 prefixEnd_131751 := by exact prefixLift 131751
  have htrace : WordTrace (prefixWord ++ tailWord_131751) baseStart_131751 baseEnd_131751 := by
    simpa [prefixWord, tailWord_131751, baseEnd_131751] using wordTrace_append hprefix tailTrace_131751
  have hstable : (prefixWord ++ tailWord_131751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131751).length < 2 ^ (prefixWord ++ tailWord_131751).sum := by decide
  have hdescent : baseEnd_131751 < baseStart_131751 := by decide
  rcases family_descends (prefixWord ++ tailWord_131751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131796 : List Nat := [2, 4, 1, 3, 2, 2, 1, 2, 5]
def baseStart_131796 : Nat := 118140960795 + 131796 * 2 ^ 59
def prefixEnd_131796 : Nat := 4983230072969 + 3 ^ 40 * 131796 * 2
def baseEnd_131796 : Nat := 15038821408904795831975

theorem tailTrace_131796 : CollatzResearch.WordTrace tailWord_131796 prefixEnd_131796 15038821408904795831975 := by
  unfold tailWord_131796
  simp only [CollatzResearch.WordTrace]
  refine ⟨2403497515266537904939621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3204663353688717206586161 2403497515266537904939621)
  ·
    refine ⟨450655784112475857176179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2403497515266537904939621 450655784112475857176179)
    ·
      refine ⟨675983676168713785764269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450655784112475857176179 675983676168713785764269)
      ·
        refine ⟨253493878563267669661601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 675983676168713785764269 253493878563267669661601)
        ·
          refine ⟨190120408922450752246201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253493878563267669661601 190120408922450752246201)
          ·
            refine ⟨142590306691838064184651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190120408922450752246201 142590306691838064184651)
            ·
              refine ⟨213885460037757096276977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142590306691838064184651 213885460037757096276977)
              ·
                refine ⟨160414095028317822207733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213885460037757096276977 160414095028317822207733)
                ·
                  refine ⟨15038821408904795831975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160414095028317822207733 15038821408904795831975)
                  ·
                    rfl

theorem cell22_131796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_131796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131796 prefixEnd_131796 := by exact prefixLift 131796
  have htrace : WordTrace (prefixWord ++ tailWord_131796) baseStart_131796 baseEnd_131796 := by
    simpa [prefixWord, tailWord_131796, baseEnd_131796] using wordTrace_append hprefix tailTrace_131796
  have hstable : (prefixWord ++ tailWord_131796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131796).length < 2 ^ (prefixWord ++ tailWord_131796).sum := by decide
  have hdescent : baseEnd_131796 < baseStart_131796 := by decide
  rcases family_descends (prefixWord ++ tailWord_131796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131807 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 6]
def baseStart_131807 : Nat := 118140960795 + 131807 * 2 ^ 59
def prefixEnd_131807 : Nat := 4983230072969 + 3 ^ 40 * 131807 * 2
def baseEnd_131807 : Nat := 15040076583838008490297

theorem tailTrace_131807 : CollatzResearch.WordTrace tailWord_131807 prefixEnd_131807 15040076583838008490297 := by
  unfold tailWord_131807
  simp only [CollatzResearch.WordTrace]
  refine ⟨4807396233493224688529675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3204930822328816459019783 4807396233493224688529675)
  ·
    refine ⟨7211094350239837032794513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4807396233493224688529675 7211094350239837032794513)
    ·
      refine ⟨5408320762679877774595885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7211094350239837032794513 5408320762679877774595885)
      ·
        refine ⟨2028120286004954165473457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5408320762679877774595885 2028120286004954165473457)
        ·
          refine ⟨1521090214503715624105093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2028120286004954165473457 1521090214503715624105093)
          ·
            refine ⟨285204415219446679519705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1521090214503715624105093 285204415219446679519705)
            ·
              refine ⟨213903311414585009639779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285204415219446679519705 213903311414585009639779)
              ·
                refine ⟨320854967121877514459669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213903311414585009639779 320854967121877514459669)
                ·
                  refine ⟨15040076583838008490297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 320854967121877514459669 15040076583838008490297)
                  ·
                    rfl

theorem cell22_131807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 6].length) (baseStart_131807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131807 prefixEnd_131807 := by exact prefixLift 131807
  have htrace : WordTrace (prefixWord ++ tailWord_131807) baseStart_131807 baseEnd_131807 := by
    simpa [prefixWord, tailWord_131807, baseEnd_131807] using wordTrace_append hprefix tailTrace_131807
  have hstable : (prefixWord ++ tailWord_131807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131807).length < 2 ^ (prefixWord ++ tailWord_131807).sum := by decide
  have hdescent : baseEnd_131807 < baseStart_131807 := by decide
  rcases family_descends (prefixWord ++ tailWord_131807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131837 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_131837 : Nat := 118140960795 + 131837 * 2 ^ 59
def prefixEnd_131837 : Nat := 4983230072969 + 3 ^ 40 * 131837 * 2
def baseEnd_131837 : Nat := 45130499364603947220799

theorem tailTrace_131837 : CollatzResearch.WordTrace tailWord_131837 prefixEnd_131837 45130499364603947220799 := by
  unfold tailWord_131837
  simp only [CollatzResearch.WordTrace]
  refine ⟨4808490423384539812121765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3205660282256359874747843 4808490423384539812121765)
  ·
    refine ⟨901591954384601214772831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4808490423384539812121765 901591954384601214772831)
    ·
      refine ⟨1352387931576901822159247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 901591954384601214772831 1352387931576901822159247)
      ·
        refine ⟨2028581897365352733238871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1352387931576901822159247 2028581897365352733238871)
        ·
          refine ⟨3042872846048029099858307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2028581897365352733238871 3042872846048029099858307)
          ·
            refine ⟨4564309269072043649787461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3042872846048029099858307 4564309269072043649787461)
            ·
              refine ⟨855807987951008184335149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4564309269072043649787461 855807987951008184335149)
              ·
                refine ⟨320927995481628069125681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 855807987951008184335149 320927995481628069125681)
                ·
                  refine ⟨240695996611221051844261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320927995481628069125681 240695996611221051844261)
                  ·
                    refine ⟨45130499364603947220799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 240695996611221051844261 45130499364603947220799)
                    ·
                      rfl

theorem cell22_131837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_131837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131837 prefixEnd_131837 := by exact prefixLift 131837
  have htrace : WordTrace (prefixWord ++ tailWord_131837) baseStart_131837 baseEnd_131837 := by
    simpa [prefixWord, tailWord_131837, baseEnd_131837] using wordTrace_append hprefix tailTrace_131837
  have hstable : (prefixWord ++ tailWord_131837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131837).length < 2 ^ (prefixWord ++ tailWord_131837).sum := by decide
  have hdescent : baseEnd_131837 < baseStart_131837 := by decide
  rcases family_descends (prefixWord ++ tailWord_131837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131858 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 6]
def baseStart_131858 : Nat := 118140960795 + 131858 * 2 ^ 59
def prefixEnd_131858 : Nat := 4983230072969 + 3 ^ 40 * 131858 * 2
def baseEnd_131858 : Nat := 15045896031255630815245

theorem tailTrace_131858 : CollatzResearch.WordTrace tailWord_131858 prefixEnd_131858 15045896031255630815245 := by
  unfold tailWord_131858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1202314089077115099659057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3206170904205640265757485 1202314089077115099659057)
  ·
    refine ⟨901735566807836324744293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1202314089077115099659057 901735566807836324744293)
    ·
      refine ⟨169075418776469310889555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 901735566807836324744293 169075418776469310889555)
      ·
        refine ⟨253613128164703966334333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169075418776469310889555 253613128164703966334333)
        ·
          refine ⟨95104923061763987375375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253613128164703966334333 95104923061763987375375)
          ·
            refine ⟨142657384592645981063063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95104923061763987375375 142657384592645981063063)
            ·
              refine ⟨213986076888968971594595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142657384592645981063063 213986076888968971594595)
              ·
                refine ⟨320979115333453457391893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213986076888968971594595 320979115333453457391893)
                ·
                  refine ⟨15045896031255630815245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 320979115333453457391893 15045896031255630815245)
                  ·
                    rfl

theorem cell22_131858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_131858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131858 prefixEnd_131858 := by exact prefixLift 131858
  have htrace : WordTrace (prefixWord ++ tailWord_131858) baseStart_131858 baseEnd_131858 := by
    simpa [prefixWord, tailWord_131858, baseEnd_131858] using wordTrace_append hprefix tailTrace_131858
  have hstable : (prefixWord ++ tailWord_131858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131858).length < 2 ^ (prefixWord ++ tailWord_131858).sum := by decide
  have hdescent : baseEnd_131858 < baseStart_131858 := by decide
  rcases family_descends (prefixWord ++ tailWord_131858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131912 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 2, 5]
def baseStart_131912 : Nat := 118140960795 + 131912 * 2 ^ 59
def prefixEnd_131912 : Nat := 4983230072969 + 3 ^ 40 * 131912 * 2
def baseEnd_131912 : Nat := 45156173397328751595569

theorem tailTrace_131912 : CollatzResearch.WordTrace tailWord_131912 prefixEnd_131912 45156173397328751595569 := by
  unfold tailWord_131912
  simp only [CollatzResearch.WordTrace]
  refine ⟨2405612949056413810550995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3207483932075218414067993 2405612949056413810550995)
  ·
    refine ⟨3608419423584620715826493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2405612949056413810550995 3608419423584620715826493)
    ·
      refine ⟨1353157283844232768434935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3608419423584620715826493 1353157283844232768434935)
      ·
        refine ⟨2029735925766349152652403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1353157283844232768434935 2029735925766349152652403)
        ·
          refine ⟨3044603888649523728978605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029735925766349152652403 3044603888649523728978605)
          ·
            refine ⟨1141726458243571398366977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3044603888649523728978605 1141726458243571398366977)
            ·
              refine ⟨856294843682678548775233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1141726458243571398366977 856294843682678548775233)
              ·
                refine ⟨642221132762008911581425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856294843682678548775233 642221132762008911581425)
                ·
                  refine ⟨481665849571506683686069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 642221132762008911581425 481665849571506683686069)
                  ·
                    refine ⟨45156173397328751595569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 481665849571506683686069 45156173397328751595569)
                    ·
                      rfl

theorem cell22_131912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_131912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131912 prefixEnd_131912 := by exact prefixLift 131912
  have htrace : WordTrace (prefixWord ++ tailWord_131912) baseStart_131912 baseEnd_131912 := by
    simpa [prefixWord, tailWord_131912, baseEnd_131912] using wordTrace_append hprefix tailTrace_131912
  have hstable : (prefixWord ++ tailWord_131912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131912).length < 2 ^ (prefixWord ++ tailWord_131912).sum := by decide
  have hdescent : baseEnd_131912 < baseStart_131912 := by decide
  rcases family_descends (prefixWord ++ tailWord_131912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131944 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 3, 4]
def baseStart_131944 : Nat := 118140960795 + 131944 * 2 ^ 59
def prefixEnd_131944 : Nat := 4983230072969 + 3 ^ 40 * 131944 * 2
def baseEnd_131944 : Nat := 45167127651291334795471

theorem tailTrace_131944 : CollatzResearch.WordTrace tailWord_131944 prefixEnd_131944 45167127651291334795471 := by
  unfold tailWord_131944
  simp only [CollatzResearch.WordTrace]
  refine ⟨2406196516998448543133443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3208262022664598057511257 2406196516998448543133443)
  ·
    refine ⟨3609294775497672814700165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2406196516998448543133443 3609294775497672814700165)
    ·
      refine ⟨676742770405813652756281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3609294775497672814700165 676742770405813652756281)
      ·
        refine ⟨507557077804360239567211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676742770405813652756281 507557077804360239567211)
        ·
          refine ⟨761335616706540359350817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507557077804360239567211 761335616706540359350817)
          ·
            refine ⟨571001712529905269513113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761335616706540359350817 571001712529905269513113)
            ·
              refine ⟨428251284397428952134835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571001712529905269513113 428251284397428952134835)
              ·
                refine ⟨642376926596143428202253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428251284397428952134835 642376926596143428202253)
                ·
                  refine ⟨240891347473553785575845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642376926596143428202253 240891347473553785575845)
                  ·
                    refine ⟨45167127651291334795471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 240891347473553785575845 45167127651291334795471)
                    ·
                      rfl

theorem cell22_131944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_131944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131944 prefixEnd_131944 := by exact prefixLift 131944
  have htrace : WordTrace (prefixWord ++ tailWord_131944) baseStart_131944 baseEnd_131944 := by
    simpa [prefixWord, tailWord_131944, baseEnd_131944] using wordTrace_append hprefix tailTrace_131944
  have hstable : (prefixWord ++ tailWord_131944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131944).length < 2 ^ (prefixWord ++ tailWord_131944).sum := by decide
  have hdescent : baseEnd_131944 < baseStart_131944 := by decide
  rcases family_descends (prefixWord ++ tailWord_131944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131961 : List Nat := [1, 2, 1, 3, 2, 3, 4, 1, 1, 4]
def baseStart_131961 : Nat := 118140960795 + 131961 * 2 ^ 59
def prefixEnd_131961 : Nat := 4983230072969 + 3 ^ 40 * 131961 * 2
def baseEnd_131961 : Nat := 45172947098708957120419

theorem tailTrace_131961 : CollatzResearch.WordTrace tailWord_131961 prefixEnd_131961 45172947098708957120419 := by
  unfold tailWord_131961
  simp only [CollatzResearch.WordTrace]
  refine ⟨4813013074935308989635737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3208675383290205993090491 4813013074935308989635737)
  ·
    refine ⟨3609759806201481742226803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4813013074935308989635737 3609759806201481742226803)
    ·
      refine ⟨5414639709302222613340205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3609759806201481742226803 5414639709302222613340205)
      ·
        refine ⟨2030489890988333480002577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5414639709302222613340205 2030489890988333480002577)
        ·
          refine ⟨1522867418241250110001933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2030489890988333480002577 1522867418241250110001933)
          ·
            refine ⟨571075281840468791250725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1522867418241250110001933 571075281840468791250725)
            ·
              refine ⟨107076615345087898359511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 571075281840468791250725 107076615345087898359511)
              ·
                refine ⟨160614923017631847539267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107076615345087898359511 160614923017631847539267)
                ·
                  refine ⟨240922384526447771308901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160614923017631847539267 240922384526447771308901)
                  ·
                    refine ⟨45172947098708957120419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 240922384526447771308901 45172947098708957120419)
                    ·
                      rfl

theorem cell22_131961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 1, 4].length) (baseStart_131961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131961 prefixEnd_131961 := by exact prefixLift 131961
  have htrace : WordTrace (prefixWord ++ tailWord_131961) baseStart_131961 baseEnd_131961 := by
    simpa [prefixWord, tailWord_131961, baseEnd_131961] using wordTrace_append hprefix tailTrace_131961
  have hstable : (prefixWord ++ tailWord_131961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131961).length < 2 ^ (prefixWord ++ tailWord_131961).sum := by decide
  have hdescent : baseEnd_131961 < baseStart_131961 := by decide
  rcases family_descends (prefixWord ++ tailWord_131961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131976 : List Nat := [2, 1, 3, 3, 2, 1, 2, 4, 4]
def baseStart_131976 : Nat := 118140960795 + 131976 * 2 ^ 59
def prefixEnd_131976 : Nat := 4983230072969 + 3 ^ 40 * 131976 * 2
def baseEnd_131976 : Nat := 15059360635084639331791

theorem tailTrace_131976 : CollatzResearch.WordTrace tailWord_131976 prefixEnd_131976 15059360635084639331791 := by
  unfold tailWord_131976
  simp only [CollatzResearch.WordTrace]
  refine ⟨2406780084940483275715891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3209040113253977700954521 2406780084940483275715891)
  ·
    refine ⟨3610170127410724913573837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2406780084940483275715891 3610170127410724913573837)
    ·
      refine ⟨1353813797779021842590189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3610170127410724913573837 1353813797779021842590189)
      ·
        refine ⟨507680174167133190971321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1353813797779021842590189 507680174167133190971321)
        ·
          refine ⟨380760130625349893228491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507680174167133190971321 380760130625349893228491)
          ·
            refine ⟨571140195938024839842737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380760130625349893228491 571140195938024839842737)
            ·
              refine ⟨428355146953518629882053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571140195938024839842737 428355146953518629882053)
              ·
                refine ⟨80316590053784743102885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 428355146953518629882053 80316590053784743102885)
                ·
                  refine ⟨15059360635084639331791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80316590053784743102885 15059360635084639331791)
                  ·
                    rfl

theorem cell22_131976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 4].length) (baseStart_131976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_131976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_131976 prefixEnd_131976 := by exact prefixLift 131976
  have htrace : WordTrace (prefixWord ++ tailWord_131976) baseStart_131976 baseEnd_131976 := by
    simpa [prefixWord, tailWord_131976, baseEnd_131976] using wordTrace_append hprefix tailTrace_131976
  have hstable : (prefixWord ++ tailWord_131976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131976).length < 2 ^ (prefixWord ++ tailWord_131976).sum := by decide
  have hdescent : baseEnd_131976 < baseStart_131976 := by decide
  rcases family_descends (prefixWord ++ tailWord_131976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132049 : List Nat := [1, 2, 2, 1, 2, 1, 5, 3, 5]
def baseStart_132049 : Nat := 118140960795 + 132049 * 2 ^ 59
def prefixEnd_132049 : Nat := 4983230072969 + 3 ^ 40 * 132049 * 2
def baseEnd_132049 : Nat := 15067690432368686973383

theorem tailTrace_132049 : CollatzResearch.WordTrace tailWord_132049 prefixEnd_132049 15067690432368686973383 := by
  unfold tailWord_132049
  simp only [CollatzResearch.WordTrace]
  refine ⟨4816222698616500018839201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3210815132411000012559467 4816222698616500018839201)
  ·
    refine ⟨3612167023962375014129401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4816222698616500018839201 3612167023962375014129401)
    ·
      refine ⟨2709125267971781260597051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3612167023962375014129401 2709125267971781260597051)
      ·
        refine ⟨4063687901957671890895577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2709125267971781260597051 4063687901957671890895577)
        ·
          refine ⟨3047765926468253918171683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4063687901957671890895577 3047765926468253918171683)
          ·
            refine ⟨4571648889702380877257525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3047765926468253918171683 4571648889702380877257525)
            ·
              refine ⟨428592083409598207242893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4571648889702380877257525 428592083409598207242893)
              ·
                refine ⟨160722031278599327716085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 428592083409598207242893 160722031278599327716085)
                ·
                  refine ⟨15067690432368686973383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160722031278599327716085 15067690432368686973383)
                  ·
                    rfl

theorem cell22_132049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 5].length) (baseStart_132049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132049 prefixEnd_132049 := by exact prefixLift 132049
  have htrace : WordTrace (prefixWord ++ tailWord_132049) baseStart_132049 baseEnd_132049 := by
    simpa [prefixWord, tailWord_132049, baseEnd_132049] using wordTrace_append hprefix tailTrace_132049
  have hstable : (prefixWord ++ tailWord_132049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132049).length < 2 ^ (prefixWord ++ tailWord_132049).sum := by decide
  have hdescent : baseEnd_132049 < baseStart_132049 := by decide
  rcases family_descends (prefixWord ++ tailWord_132049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132130 : List Nat := [3, 3, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_132130 : Nat := 118140960795 + 132130 * 2 ^ 59
def prefixEnd_132130 : Nat := 4983230072969 + 3 ^ 40 * 132130 * 2
def baseEnd_132130 : Nat := 45230799252448849644901

theorem tailTrace_132130 : CollatzResearch.WordTrace tailWord_132130 prefixEnd_132130 45230799252448849644901 := by
  unfold tailWord_132130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1204794252830762713134461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3212784674215367235025229 1204794252830762713134461)
  ·
    refine ⟨451797844811536017425423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1204794252830762713134461 451797844811536017425423)
    ·
      refine ⟨677696767217304026138135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451797844811536017425423 677696767217304026138135)
      ·
        refine ⟨1016545150825956039207203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677696767217304026138135 1016545150825956039207203)
        ·
          refine ⟨1524817726238934058810805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016545150825956039207203 1524817726238934058810805)
          ·
            refine ⟨142951661834900068013513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1524817726238934058810805 142951661834900068013513)
            ·
              refine ⟨107213746376175051010135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142951661834900068013513 107213746376175051010135)
              ·
                refine ⟨160820619564262576515203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107213746376175051010135 160820619564262576515203)
                ·
                  refine ⟨241230929346393864772805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160820619564262576515203 241230929346393864772805)
                  ·
                    refine ⟨45230799252448849644901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 241230929346393864772805 45230799252448849644901)
                    ·
                      rfl

theorem cell22_132130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_132130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132130 prefixEnd_132130 := by exact prefixLift 132130
  have htrace : WordTrace (prefixWord ++ tailWord_132130) baseStart_132130 baseEnd_132130 := by
    simpa [prefixWord, tailWord_132130, baseEnd_132130] using wordTrace_append hprefix tailTrace_132130
  have hstable : (prefixWord ++ tailWord_132130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132130).length < 2 ^ (prefixWord ++ tailWord_132130).sum := by decide
  have hdescent : baseEnd_132130 < baseStart_132130 := by decide
  rcases family_descends (prefixWord ++ tailWord_132130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132173 : List Nat := [1, 6, 1, 1, 1, 2, 4, 6]
def baseStart_132173 : Nat := 118140960795 + 132173 * 2 ^ 59
def prefixEnd_132173 : Nat := 4983230072969 + 3 ^ 40 * 132173 * 2
def baseEnd_132173 : Nat := 5027279892356785646641

theorem tailTrace_132173 : CollatzResearch.WordTrace tailWord_132173 prefixEnd_132173 5027279892356785646641 := by
  unfold tailWord_132173
  simp only [CollatzResearch.WordTrace]
  refine ⟨4820745350167269196353173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3213830233444846130902115 4820745350167269196353173)
  ·
    refine ⟨225972438289090743579055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4820745350167269196353173 225972438289090743579055)
    ·
      refine ⟨338958657433636115368583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225972438289090743579055 338958657433636115368583)
      ·
        refine ⟨508437986150454173052875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338958657433636115368583 508437986150454173052875)
        ·
          refine ⟨762656979225681259579313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508437986150454173052875 762656979225681259579313)
          ·
            refine ⟨571992734419260944684485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 762656979225681259579313 571992734419260944684485)
            ·
              refine ⟨107248637703611427128341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 571992734419260944684485 107248637703611427128341)
              ·
                refine ⟨5027279892356785646641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107248637703611427128341 5027279892356785646641)
                ·
                  rfl

theorem cell22_132173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 6].length) (baseStart_132173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132173 prefixEnd_132173 := by exact prefixLift 132173
  have htrace : WordTrace (prefixWord ++ tailWord_132173) baseStart_132173 baseEnd_132173 := by
    simpa [prefixWord, tailWord_132173, baseEnd_132173] using wordTrace_append hprefix tailTrace_132173
  have hstable : (prefixWord ++ tailWord_132173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132173).length < 2 ^ (prefixWord ++ tailWord_132173).sum := by decide
  have hdescent : baseEnd_132173 < baseStart_132173 := by decide
  rcases family_descends (prefixWord ++ tailWord_132173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132184 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 9]
def baseStart_132184 : Nat := 118140960795 + 132184 * 2 ^ 59
def prefixEnd_132184 : Nat := 4983230072969 + 3 ^ 40 * 132184 * 2
def baseEnd_132184 : Nat := 15083094852003569598245

theorem tailTrace_132184 : CollatzResearch.WordTrace tailWord_132184 prefixEnd_132184 15083094852003569598245 := by
  unfold tailWord_132184
  simp only [CollatzResearch.WordTrace]
  refine ⟨2410573276563709037501803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3214097702084945383335737 2410573276563709037501803)
  ·
    refine ⟨3615859914845563556252705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2410573276563709037501803 3615859914845563556252705)
    ·
      refine ⟨2711894936134172667189529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3615859914845563556252705 2711894936134172667189529)
      ·
        refine ⟨2033921202100629500392147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2711894936134172667189529 2033921202100629500392147)
        ·
          refine ⟨3050881803150944250588221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2033921202100629500392147 3050881803150944250588221)
          ·
            refine ⟨1144080676181604093970583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3050881803150944250588221 1144080676181604093970583)
            ·
              refine ⟨1716121014272406140955875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144080676181604093970583 1716121014272406140955875)
              ·
                refine ⟨2574181521408609211433813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1716121014272406140955875 2574181521408609211433813)
                ·
                  refine ⟨15083094852003569598245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2574181521408609211433813 15083094852003569598245)
                  ·
                    rfl

theorem cell22_132184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_132184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132184 prefixEnd_132184 := by exact prefixLift 132184
  have htrace : WordTrace (prefixWord ++ tailWord_132184) baseStart_132184 baseEnd_132184 := by
    simpa [prefixWord, tailWord_132184, baseEnd_132184] using wordTrace_append hprefix tailTrace_132184
  have hstable : (prefixWord ++ tailWord_132184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132184).length < 2 ^ (prefixWord ++ tailWord_132184).sum := by decide
  have hdescent : baseEnd_132184 < baseStart_132184 := by decide
  rcases family_descends (prefixWord ++ tailWord_132184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132190 : List Nat := [4, 4, 1, 1, 1, 3, 8]
def baseStart_132190 : Nat := 118140960795 + 132190 * 2 ^ 59
def prefixEnd_132190 : Nat := 4983230072969 + 3 ^ 40 * 132190 * 2
def baseEnd_132190 : Nat := 1675975499208470116471

theorem tailTrace_132190 : CollatzResearch.WordTrace tailWord_132190 prefixEnd_132190 1675975499208470116471 := by
  unfold tailWord_132190
  simp only [CollatzResearch.WordTrace]
  refine ⟨602670673888210137465253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3214243594070454066481349 602670673888210137465253)
  ·
    refine ⟨113000751354039400774735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 602670673888210137465253 113000751354039400774735)
    ·
      refine ⟨169501127031059101162103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113000751354039400774735 169501127031059101162103)
      ·
        refine ⟨254251690546588651743155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169501127031059101162103 254251690546588651743155)
        ·
          refine ⟨381377535819882977614733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254251690546588651743155 381377535819882977614733)
          ·
            refine ⟨143016575932456116605525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381377535819882977614733 143016575932456116605525)
            ·
              refine ⟨1675975499208470116471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 143016575932456116605525 1675975499208470116471)
              ·
                rfl

theorem cell22_132190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 8].length) (baseStart_132190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132190 prefixEnd_132190 := by exact prefixLift 132190
  have htrace : WordTrace (prefixWord ++ tailWord_132190) baseStart_132190 baseEnd_132190 := by
    simpa [prefixWord, tailWord_132190, baseEnd_132190] using wordTrace_append hprefix tailTrace_132190
  have hstable : (prefixWord ++ tailWord_132190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132190).length < 2 ^ (prefixWord ++ tailWord_132190).sum := by decide
  have hdescent : baseEnd_132190 < baseStart_132190 := by decide
  rcases family_descends (prefixWord ++ tailWord_132190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132205 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_132205 : Nat := 118140960795 + 132205 * 2 ^ 59
def prefixEnd_132205 : Nat := 4983230072969 + 3 ^ 40 * 132205 * 2
def baseEnd_132205 : Nat := 45256473285173654019671

theorem tailTrace_132205 : CollatzResearch.WordTrace tailWord_132205 prefixEnd_132205 45256473285173654019671 := by
  unfold tailWord_132205
  simp only [CollatzResearch.WordTrace]
  refine ⟨4821912486051338661518069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3214608324034225774345379 4821912486051338661518069)
  ·
    refine ⟨452054295567312999517319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4821912486051338661518069 452054295567312999517319)
    ·
      refine ⟨678081443350969499275979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452054295567312999517319 678081443350969499275979)
      ·
        refine ⟨1017122165026454248913969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678081443350969499275979 1017122165026454248913969)
        ·
          refine ⟨762841623769840686685477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1017122165026454248913969 762841623769840686685477)
          ·
            refine ⟨143032804456845128753527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 762841623769840686685477 143032804456845128753527)
            ·
              refine ⟨214549206685267693130291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143032804456845128753527 214549206685267693130291)
              ·
                refine ⟨321823810027901539695437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214549206685267693130291 321823810027901539695437)
                ·
                  refine ⟨120683928760463077385789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321823810027901539695437 120683928760463077385789)
                  ·
                    refine ⟨45256473285173654019671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120683928760463077385789 45256473285173654019671)
                    ·
                      rfl

theorem cell22_132205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_132205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132205 prefixEnd_132205 := by exact prefixLift 132205
  have htrace : WordTrace (prefixWord ++ tailWord_132205) baseStart_132205 baseEnd_132205 := by
    simpa [prefixWord, tailWord_132205, baseEnd_132205] using wordTrace_append hprefix tailTrace_132205
  have hstable : (prefixWord ++ tailWord_132205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132205).length < 2 ^ (prefixWord ++ tailWord_132205).sum := by decide
  have hdescent : baseEnd_132205 < baseStart_132205 := by decide
  rcases family_descends (prefixWord ++ tailWord_132205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132312 : List Nat := [2, 1, 2, 2, 5, 2, 1, 2, 2, 3]
def baseStart_132312 : Nat := 118140960795 + 132312 * 2 ^ 59
def prefixEnd_132312 : Nat := 4983230072969 + 3 ^ 40 * 132312 * 2
def baseEnd_132312 : Nat := 45293101571861041594343

theorem tailTrace_132312 : CollatzResearch.WordTrace tailWord_132312 prefixEnd_132312 45293101571861041594343 := by
  unfold tailWord_132312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2412907548331847967831595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3217210064442463957108793 2412907548331847967831595)
  ·
    refine ⟨3619361322497771951747393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2412907548331847967831595 3619361322497771951747393)
    ·
      refine ⟨2714520991873328963810545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3619361322497771951747393 2714520991873328963810545)
      ·
        refine ⟨2035890743904996722857909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2714520991873328963810545 2035890743904996722857909)
        ·
          refine ⟨190864757241093442767929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2035890743904996722857909 190864757241093442767929)
          ·
            refine ⟨143148567930820082075947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190864757241093442767929 143148567930820082075947)
            ·
              refine ⟨214722851896230123113921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143148567930820082075947 214722851896230123113921)
              ·
                refine ⟨161042138922172592335441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214722851896230123113921 161042138922172592335441)
                ·
                  refine ⟨120781604191629444251581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161042138922172592335441 120781604191629444251581)
                  ·
                    refine ⟨45293101571861041594343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120781604191629444251581 45293101571861041594343)
                    ·
                      rfl

theorem cell22_132312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_132312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132312 prefixEnd_132312 := by exact prefixLift 132312
  have htrace : WordTrace (prefixWord ++ tailWord_132312) baseStart_132312 baseEnd_132312 := by
    simpa [prefixWord, tailWord_132312, baseEnd_132312] using wordTrace_append hprefix tailTrace_132312
  have hstable : (prefixWord ++ tailWord_132312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132312).length < 2 ^ (prefixWord ++ tailWord_132312).sum := by decide
  have hdescent : baseEnd_132312 < baseStart_132312 := by decide
  rcases family_descends (prefixWord ++ tailWord_132312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132411 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 7, 6]
def baseStart_132411 : Nat := 118140960795 + 132411 * 2 ^ 59
def prefixEnd_132411 : Nat := 4983230072969 + 3 ^ 40 * 132411 * 2
def baseEnd_132411 : Nat := 45326991295057783369039

theorem tailTrace_132411 : CollatzResearch.WordTrace tailWord_132411 prefixEnd_132411 45326991295057783369039 := by
  unfold tailWord_132411
  simp only [CollatzResearch.WordTrace]
  refine ⟨4829425923305035843517087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3219617282203357229011391 4829425923305035843517087)
  ·
    refine ⟨7244138884957553765275631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4829425923305035843517087 7244138884957553765275631)
    ·
      refine ⟨10866208327436330647913447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7244138884957553765275631 10866208327436330647913447)
      ·
        refine ⟨16299312491154495971870171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10866208327436330647913447 16299312491154495971870171)
        ·
          refine ⟨24448968736731743957805257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16299312491154495971870171 24448968736731743957805257)
          ·
            refine ⟨18336726552548807968353943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24448968736731743957805257 18336726552548807968353943)
            ·
              refine ⟨27505089828823211952530915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18336726552548807968353943 27505089828823211952530915)
              ·
                refine ⟨41257634743234817928796373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27505089828823211952530915 41257634743234817928796373)
                ·
                  refine ⟨966975814294566045206165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 41257634743234817928796373 966975814294566045206165)
                  ·
                    refine ⟨45326991295057783369039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 966975814294566045206165 45326991295057783369039)
                    ·
                      rfl

theorem cell22_132411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 6].length) (baseStart_132411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_132411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_132411 prefixEnd_132411 := by exact prefixLift 132411
  have htrace : WordTrace (prefixWord ++ tailWord_132411) baseStart_132411 baseEnd_132411 := by
    simpa [prefixWord, tailWord_132411, baseEnd_132411] using wordTrace_append hprefix tailTrace_132411
  have hstable : (prefixWord ++ tailWord_132411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132411).length < 2 ^ (prefixWord ++ tailWord_132411).sum := by decide
  have hdescent : baseEnd_132411 < baseStart_132411 := by decide
  rcases family_descends (prefixWord ++ tailWord_132411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
