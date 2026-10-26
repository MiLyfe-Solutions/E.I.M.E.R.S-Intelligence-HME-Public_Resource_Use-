import V185TrunkScan23Chunk1303

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7723595 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 3, 5, 2]
def baseStart_7723595 : Nat := 118140960795 + 7723595 * 2 ^ 59
def prefixEnd_7723595 : Nat := 4983230072969 + 3 ^ 40 * 7723595 * 2
def baseEnd_7723595 : Nat := 3965916615662814132742339

theorem tailTrace_7723595 : CollatzResearch.WordTrace tailWord_7723595 prefixEnd_7723595 3965916615662814132742339 := by
  unfold tailWord_7723595
  simp only [CollatzResearch.WordTrace]
  refine ⟨281702652453741874853388239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187801768302494583235592159 281702652453741874853388239)
  ·
    refine ⟨422553978680612812280082359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281702652453741874853388239 422553978680612812280082359)
    ·
      refine ⟨633830968020919218420123539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422553978680612812280082359 633830968020919218420123539)
      ·
        refine ⟨950746452031378827630185309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633830968020919218420123539 950746452031378827630185309)
        ·
          refine ⟨356529919511767060361319491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 950746452031378827630185309 356529919511767060361319491)
          ·
            refine ⟨534794879267650590541979237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356529919511767060361319491 534794879267650590541979237)
            ·
              refine ⟨100274039862684485726621107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 534794879267650590541979237 100274039862684485726621107)
              ·
                refine ⟨150411059794026728589931661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100274039862684485726621107 150411059794026728589931661)
                ·
                  refine ⟨56404147422760023221224373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150411059794026728589931661 56404147422760023221224373)
                  ·
                    refine ⟨5287888820883752176989785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56404147422760023221224373 5287888820883752176989785)
                    ·
                      refine ⟨3965916615662814132742339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5287888820883752176989785 3965916615662814132742339)
                      ·
                        rfl

theorem cell23_7723595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 5, 2].length) (baseStart_7723595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723595 prefixEnd_7723595 := by exact prefixLift 7723595
  have htrace : WordTrace (prefixWord ++ tailWord_7723595) baseStart_7723595 baseEnd_7723595 := by
    simpa [prefixWord, tailWord_7723595, baseEnd_7723595] using wordTrace_append hprefix tailTrace_7723595
  have hstable : (prefixWord ++ tailWord_7723595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723595).length < 2 ^ (prefixWord ++ tailWord_7723595).sum := by decide
  have hdescent : baseEnd_7723595 < baseStart_7723595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723602 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_7723602 : Nat := 118140960795 + 7723602 * 2 ^ 59
def prefixEnd_7723602 : Nat := 4983230072969 + 3 ^ 40 * 7723602 * 2
def baseEnd_7723602 : Nat := 3965920210027395605354807

theorem tailTrace_7723602 : CollatzResearch.WordTrace tailWord_7723602 prefixEnd_7723602 3965920210027395605354807 := by
  unfold tailWord_7723602
  simp only [CollatzResearch.WordTrace]
  refine ⟨70425726941179128762223265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187801938509811010032595373 70425726941179128762223265)
  ·
    refine ⟨52819295205884346571667449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70425726941179128762223265 52819295205884346571667449)
    ·
      refine ⟨39614471404413259928750587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52819295205884346571667449 39614471404413259928750587)
      ·
        refine ⟨59421707106619889893125881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39614471404413259928750587 59421707106619889893125881)
        ·
          refine ⟨44566280329964917419844411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59421707106619889893125881 44566280329964917419844411)
          ·
            refine ⟨66849420494947376129766617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44566280329964917419844411 66849420494947376129766617)
            ·
              refine ⟨50137065371210532097324963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66849420494947376129766617 50137065371210532097324963)
              ·
                refine ⟨75205598056815798145987445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50137065371210532097324963 75205598056815798145987445)
                ·
                  refine ⟨7050524817826481076186323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75205598056815798145987445 7050524817826481076186323)
                  ·
                    refine ⟨10575787226739721614279485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7050524817826481076186323 10575787226739721614279485)
                    ·
                      refine ⟨3965920210027395605354807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10575787226739721614279485 3965920210027395605354807)
                      ·
                        rfl

theorem cell23_7723602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_7723602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723602 prefixEnd_7723602 := by exact prefixLift 7723602
  have htrace : WordTrace (prefixWord ++ tailWord_7723602) baseStart_7723602 baseEnd_7723602 := by
    simpa [prefixWord, tailWord_7723602, baseEnd_7723602] using wordTrace_append hprefix tailTrace_7723602
  have hstable : (prefixWord ++ tailWord_7723602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723602).length < 2 ^ (prefixWord ++ tailWord_7723602).sum := by decide
  have hdescent : baseEnd_7723602 < baseStart_7723602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723619 : List Nat := [1, 1, 1, 5, 1, 2, 2, 5, 1, 1, 3]
def baseStart_7723619 : Nat := 118140960795 + 7723619 * 2 ^ 59
def prefixEnd_7723619 : Nat := 4983230072969 + 3 ^ 40 * 7723619 * 2
def baseEnd_7723619 : Nat := 3965928939198522038842229

theorem tailTrace_7723619 : CollatzResearch.WordTrace tailWord_7723619 prefixEnd_7723619 3965928939198522038842229 := by
  unfold tailWord_7723619
  simp only [CollatzResearch.WordTrace]
  refine ⟨281703527805654926952261911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187802351870436617968174607 281703527805654926952261911)
  ·
    refine ⟨422555291708482390428392867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281703527805654926952261911 422555291708482390428392867)
    ·
      refine ⟨633832937562723585642589301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422555291708482390428392867 633832937562723585642589301)
      ·
        refine ⟨59421837896505336153992747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 633832937562723585642589301 59421837896505336153992747)
        ·
          refine ⟨89132756844758004230989121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59421837896505336153992747 89132756844758004230989121)
          ·
            refine ⟨66849567633568503173241841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89132756844758004230989121 66849567633568503173241841)
            ·
              refine ⟨50137175725176377379931381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66849567633568503173241841 50137175725176377379931381)
              ·
                refine ⟨4700360224235285379368567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50137175725176377379931381 4700360224235285379368567)
                ·
                  refine ⟨7050540336352928069052851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700360224235285379368567 7050540336352928069052851)
                  ·
                    refine ⟨10575810504529392103579277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7050540336352928069052851 10575810504529392103579277)
                    ·
                      refine ⟨3965928939198522038842229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10575810504529392103579277 3965928939198522038842229)
                      ·
                        rfl

theorem cell23_7723619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_7723619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723619 prefixEnd_7723619 := by exact prefixLift 7723619
  have htrace : WordTrace (prefixWord ++ tailWord_7723619) baseStart_7723619 baseEnd_7723619 := by
    simpa [prefixWord, tailWord_7723619, baseEnd_7723619] using wordTrace_append hprefix tailTrace_7723619
  have hstable : (prefixWord ++ tailWord_7723619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723619).length < 2 ^ (prefixWord ++ tailWord_7723619).sum := by decide
  have hdescent : baseEnd_7723619 < baseStart_7723619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723629 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_7723629 : Nat := 118140960795 + 7723629 * 2 ^ 59
def prefixEnd_7723629 : Nat := 4983230072969 + 3 ^ 40 * 7723629 * 2
def baseEnd_7723629 : Nat := 3965934074005066999717183

theorem tailTrace_7723629 : CollatzResearch.WordTrace tailWord_7723629 prefixEnd_7723629 3965934074005066999717183 := by
  unfold tailWord_7723629
  simp only [CollatzResearch.WordTrace]
  refine ⟨281703892535618698660125941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187802595023745799106750627 281703892535618698660125941)
  ·
    refine ⟨26409739925214252999386807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281703892535618698660125941 26409739925214252999386807)
    ·
      refine ⟨39614609887821379499080211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26409739925214252999386807 39614609887821379499080211)
      ·
        refine ⟨59421914831732069248620317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39614609887821379499080211 59421914831732069248620317)
        ·
          refine ⟨22283218061899525968232619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59421914831732069248620317 22283218061899525968232619)
          ·
            refine ⟨33424827092849288952348929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22283218061899525968232619 33424827092849288952348929)
            ·
              refine ⟨25068620319636966714261697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33424827092849288952348929 25068620319636966714261697)
              ·
                refine ⟨18801465239727725035696273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25068620319636966714261697 18801465239727725035696273)
                ·
                  refine ⟨14101098929795793776772205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18801465239727725035696273 14101098929795793776772205)
                  ·
                    refine ⟨5287912098673422666289577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14101098929795793776772205 5287912098673422666289577)
                    ·
                      refine ⟨3965934074005066999717183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5287912098673422666289577 3965934074005066999717183)
                      ·
                        rfl

theorem cell23_7723629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_7723629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723629 prefixEnd_7723629 := by exact prefixLift 7723629
  have htrace : WordTrace (prefixWord ++ tailWord_7723629) baseStart_7723629 baseEnd_7723629 := by
    simpa [prefixWord, tailWord_7723629, baseEnd_7723629] using wordTrace_append hprefix tailTrace_7723629
  have hstable : (prefixWord ++ tailWord_7723629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723629).length < 2 ^ (prefixWord ++ tailWord_7723629).sum := by decide
  have hdescent : baseEnd_7723629 < baseStart_7723629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723652 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_7723652 : Nat := 118140960795 + 7723652 * 2 ^ 59
def prefixEnd_7723652 : Nat := 4983230072969 + 3 ^ 40 * 7723652 * 2
def baseEnd_7723652 : Nat := 1321981961353373469909859

theorem tailTrace_7723652 : CollatzResearch.WordTrace tailWord_7723652 prefixEnd_7723652 1321981961353373469909859 := by
  unfold tailWord_7723652
  simp only [CollatzResearch.WordTrace]
  refine ⟨140852365707267686794106605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187803154276356915725475473 140852365707267686794106605)
  ·
    refine ⟨52819637140225382547789977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140852365707267686794106605 52819637140225382547789977)
    ·
      refine ⟨39614727855169036910842483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52819637140225382547789977 39614727855169036910842483)
      ·
        refine ⟨59422091782753555366263725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39614727855169036910842483 59422091782753555366263725)
        ·
          refine ⟨22283284418532583262348897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59422091782753555366263725 22283284418532583262348897)
          ·
            refine ⟨16712463313899437446761673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22283284418532583262348897 16712463313899437446761673)
            ·
              refine ⟨12534347485424578085071255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16712463313899437446761673 12534347485424578085071255)
              ·
                refine ⟨18801521228136867127606883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12534347485424578085071255 18801521228136867127606883)
                ·
                  refine ⟨28202281842205300691410325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18801521228136867127606883 28202281842205300691410325)
                  ·
                    refine ⟨1321981961353373469909859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28202281842205300691410325 1321981961353373469909859)
                    ·
                      rfl

theorem cell23_7723652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_7723652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723652 prefixEnd_7723652 := by exact prefixLift 7723652
  have htrace : WordTrace (prefixWord ++ tailWord_7723652) baseStart_7723652 baseEnd_7723652 := by
    simpa [prefixWord, tailWord_7723652, baseEnd_7723652] using wordTrace_append hprefix tailTrace_7723652
  have hstable : (prefixWord ++ tailWord_7723652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723652).length < 2 ^ (prefixWord ++ tailWord_7723652).sum := by decide
  have hdescent : baseEnd_7723652 < baseStart_7723652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723662 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_7723662 : Nat := 118140960795 + 7723662 * 2 ^ 59
def prefixEnd_7723662 : Nat := 4983230072969 + 3 ^ 40 * 7723662 * 2
def baseEnd_7723662 : Nat := 3965951018866665370604531

theorem tailTrace_7723662 : CollatzResearch.WordTrace tailWord_7723662 prefixEnd_7723662 3965951018866665370604531 := by
  unfold tailWord_7723662
  simp only [CollatzResearch.WordTrace]
  refine ⟨35213137018062393162009655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187803397429666096864051493 35213137018062393162009655)
  ·
    refine ⟨52819705527093589743014483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35213137018062393162009655 52819705527093589743014483)
    ·
      refine ⟨79229558290640384614521725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52819705527093589743014483 79229558290640384614521725)
      ·
        refine ⟨29711084358990144230445647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79229558290640384614521725 29711084358990144230445647)
        ·
          refine ⟨44566626538485216345668471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29711084358990144230445647 44566626538485216345668471)
          ·
            refine ⟨66849939807727824518502707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44566626538485216345668471 66849939807727824518502707)
            ·
              refine ⟨100274909711591736777754061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66849939807727824518502707 100274909711591736777754061)
              ·
                refine ⟨37603091141846901291657773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100274909711591736777754061 37603091141846901291657773)
                ·
                  refine ⟨14101159178192587984371665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37603091141846901291657773 14101159178192587984371665)
                  ·
                    refine ⟨10575869383644440988278749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14101159178192587984371665 10575869383644440988278749)
                    ·
                      refine ⟨3965951018866665370604531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10575869383644440988278749 3965951018866665370604531)
                      ·
                        rfl

theorem cell23_7723662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_7723662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723662 prefixEnd_7723662 := by exact prefixLift 7723662
  have htrace : WordTrace (prefixWord ++ tailWord_7723662) baseStart_7723662 baseEnd_7723662 := by
    simpa [prefixWord, tailWord_7723662, baseEnd_7723662] using wordTrace_append hprefix tailTrace_7723662
  have hstable : (prefixWord ++ tailWord_7723662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723662).length < 2 ^ (prefixWord ++ tailWord_7723662).sum := by decide
  have hdescent : baseEnd_7723662 < baseStart_7723662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723676 : List Nat := [2, 2, 3, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_7723676 : Nat := 118140960795 + 7723676 * 2 ^ 59
def prefixEnd_7723676 : Nat := 4983230072969 + 3 ^ 40 * 7723676 * 2
def baseEnd_7723676 : Nat := 3965958207595828315829467

theorem tailTrace_7723676 : CollatzResearch.WordTrace tailWord_7723676 prefixEnd_7723676 3965958207595828315829467 := by
  unfold tailWord_7723676
  simp only [CollatzResearch.WordTrace]
  refine ⟨140852803383224212843543441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187803737844298950458057921 140852803383224212843543441)
  ·
    refine ⟨105639602537418159632657581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140852803383224212843543441 105639602537418159632657581)
    ·
      refine ⟨39614850951531809862246593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105639602537418159632657581 39614850951531809862246593)
      ·
        refine ⟨29711138213648857396684945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39614850951531809862246593 29711138213648857396684945)
        ·
          refine ⟨22283353660236643047513709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29711138213648857396684945 22283353660236643047513709)
          ·
            refine ⟨8356257622588741142817641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22283353660236643047513709 8356257622588741142817641)
            ·
              refine ⟨6267193216941555857113231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8356257622588741142817641 6267193216941555857113231)
              ·
                refine ⟨9400789825412333785669847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6267193216941555857113231 9400789825412333785669847)
                ·
                  refine ⟨14101184738118500678504771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9400789825412333785669847 14101184738118500678504771)
                  ·
                    refine ⟨21151777107177751017757157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14101184738118500678504771 21151777107177751017757157)
                    ·
                      refine ⟨3965958207595828315829467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21151777107177751017757157 3965958207595828315829467)
                      ·
                        rfl

theorem cell23_7723676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_7723676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723676 prefixEnd_7723676 := by exact prefixLift 7723676
  have htrace : WordTrace (prefixWord ++ tailWord_7723676) baseStart_7723676 baseEnd_7723676 := by
    simpa [prefixWord, tailWord_7723676, baseEnd_7723676] using wordTrace_append hprefix tailTrace_7723676
  have hstable : (prefixWord ++ tailWord_7723676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723676).length < 2 ^ (prefixWord ++ tailWord_7723676).sum := by decide
  have hdescent : baseEnd_7723676 < baseStart_7723676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723693 : List Nat := [1, 5, 2, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_7723693 : Nat := 118140960795 + 7723693 * 2 ^ 59
def prefixEnd_7723693 : Nat := 4983230072969 + 3 ^ 40 * 7723693 * 2
def baseEnd_7723693 : Nat := 3965966936766954749316889

theorem tailTrace_7723693 : CollatzResearch.WordTrace tailWord_7723693 prefixEnd_7723693 3965966936766954749316889 := by
  unfold tailWord_7723693
  simp only [CollatzResearch.WordTrace]
  refine ⟨281706226807386837590455733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187804151204924558393637155 281706226807386837590455733)
  ·
    refine ⟨26409958763192516024105225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281706226807386837590455733 26409958763192516024105225)
    ·
      refine ⟨19807469072394387018078919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26409958763192516024105225 19807469072394387018078919)
      ·
        refine ⟨29711203608591580527118379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19807469072394387018078919 29711203608591580527118379)
        ·
          refine ⟨44566805412887370790677569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29711203608591580527118379 44566805412887370790677569)
          ·
            refine ⟨33425104059665528093008177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44566805412887370790677569 33425104059665528093008177)
            ·
              refine ⟨25068828044749146069756133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33425104059665528093008177 25068828044749146069756133)
              ·
                refine ⟨4700405258390464888079275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25068828044749146069756133 4700405258390464888079275)
                ·
                  refine ⟨7050607887585697332118913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700405258390464888079275 7050607887585697332118913)
                  ·
                    refine ⟨5287955915689272999089185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7050607887585697332118913 5287955915689272999089185)
                    ·
                      refine ⟨3965966936766954749316889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5287955915689272999089185 3965966936766954749316889)
                      ·
                        rfl

theorem cell23_7723693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_7723693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723693 prefixEnd_7723693 := by exact prefixLift 7723693
  have htrace : WordTrace (prefixWord ++ tailWord_7723693) baseStart_7723693 baseEnd_7723693 := by
    simpa [prefixWord, tailWord_7723693, baseEnd_7723693] using wordTrace_append hprefix tailTrace_7723693
  have hstable : (prefixWord ++ tailWord_7723693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723693).length < 2 ^ (prefixWord ++ tailWord_7723693).sum := by decide
  have hdescent : baseEnd_7723693 < baseStart_7723693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723709 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 1, 3, 3]
def baseStart_7723709 : Nat := 118140960795 + 7723709 * 2 ^ 59
def prefixEnd_7723709 : Nat := 4983230072969 + 3 ^ 40 * 7723709 * 2
def baseEnd_7723709 : Nat := 3965975152457426686716815

theorem tailTrace_7723709 : CollatzResearch.WordTrace tailWord_7723709 prefixEnd_7723709 3965975152457426686716815 := by
  unfold tailWord_7723709
  simp only [CollatzResearch.WordTrace]
  refine ⟨281706810375328872323038181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187804540250219248215358787 281706810375328872323038181)
  ·
    refine ⟨52820026945374163560569659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281706810375328872323038181 52820026945374163560569659)
    ·
      refine ⟨79230040418061245340854489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52820026945374163560569659 79230040418061245340854489)
      ·
        refine ⟨59422530313545934005640867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79230040418061245340854489 59422530313545934005640867)
        ·
          refine ⟨89133795470318901008461301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59422530313545934005640867 89133795470318901008461301)
          ·
            refine ⟨8356293325342396969543247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89133795470318901008461301 8356293325342396969543247)
            ·
              refine ⟨12534439988013595454314871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8356293325342396969543247 12534439988013595454314871)
              ·
                refine ⟨18801659982020393181472307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12534439988013595454314871 18801659982020393181472307)
                ·
                  refine ⟨28202489973030589772208461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18801659982020393181472307 28202489973030589772208461)
                  ·
                    refine ⟨10575933739886471164578173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28202489973030589772208461 10575933739886471164578173)
                    ·
                      refine ⟨3965975152457426686716815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10575933739886471164578173 3965975152457426686716815)
                      ·
                        rfl

theorem cell23_7723709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_7723709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723709 prefixEnd_7723709 := by exact prefixLift 7723709
  have htrace : WordTrace (prefixWord ++ tailWord_7723709) baseStart_7723709 baseEnd_7723709 := by
    simpa [prefixWord, tailWord_7723709, baseEnd_7723709] using wordTrace_append hprefix tailTrace_7723709
  have hstable : (prefixWord ++ tailWord_7723709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723709).length < 2 ^ (prefixWord ++ tailWord_7723709).sum := by decide
  have hdescent : baseEnd_7723709 < baseStart_7723709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723713 : List Nat := [1, 2, 6, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_7723713 : Nat := 118140960795 + 7723713 * 2 ^ 59
def prefixEnd_7723713 : Nat := 4983230072969 + 3 ^ 40 * 7723713 * 2
def baseEnd_7723713 : Nat := 3965977206380044671066797

theorem tailTrace_7723713 : CollatzResearch.WordTrace tailWord_7723713 prefixEnd_7723713 3965977206380044671066797 := by
  unfold tailWord_7723713
  simp only [CollatzResearch.WordTrace]
  refine ⟨281706956267314381006183793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187804637511542920670789195 281706956267314381006183793)
  ·
    refine ⟨211280217200485785754637845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281706956267314381006183793 211280217200485785754637845)
    ·
      refine ⟨9903760181272771207248649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 211280217200485785754637845 9903760181272771207248649)
      ·
        refine ⟨7427820135954578405436487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9903760181272771207248649 7427820135954578405436487)
        ·
          refine ⟨11141730203931867608154731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7427820135954578405436487 11141730203931867608154731)
          ·
            refine ⟨16712595305897801412232097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11141730203931867608154731 16712595305897801412232097)
            ·
              refine ⟨12534446479423351059174073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16712595305897801412232097 12534446479423351059174073)
              ·
                refine ⟨9400834859567513294380555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12534446479423351059174073 9400834859567513294380555)
                ·
                  refine ⟨14101252289351269941570833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9400834859567513294380555 14101252289351269941570833)
                  ·
                    refine ⟨10575939217013452456178125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14101252289351269941570833 10575939217013452456178125)
                    ·
                      refine ⟨3965977206380044671066797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10575939217013452456178125 3965977206380044671066797)
                      ·
                        rfl

theorem cell23_7723713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_7723713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723713 prefixEnd_7723713 := by exact prefixLift 7723713
  have htrace : WordTrace (prefixWord ++ tailWord_7723713) baseStart_7723713 baseEnd_7723713 := by
    simpa [prefixWord, tailWord_7723713, baseEnd_7723713] using wordTrace_append hprefix tailTrace_7723713
  have hstable : (prefixWord ++ tailWord_7723713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723713).length < 2 ^ (prefixWord ++ tailWord_7723713).sum := by decide
  have hdescent : baseEnd_7723713 < baseStart_7723713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723735 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_7723735 : Nat := 118140960795 + 7723735 * 2 ^ 59
def prefixEnd_7723735 : Nat := 4983230072969 + 3 ^ 40 * 7723735 * 2
def baseEnd_7723735 : Nat := 3965988502954443584991695

theorem tailTrace_7723735 : CollatzResearch.WordTrace tailWord_7723735 prefixEnd_7723735 3965988502954443584991695 := by
  unfold tailWord_7723735
  simp only [CollatzResearch.WordTrace]
  refine ⟨281707758673234678763484659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187805172448823119175656439 281707758673234678763484659)
  ·
    refine ⟨422561638009852018145226989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281707758673234678763484659 422561638009852018145226989)
    ·
      refine ⟨158460614253694506804460121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422561638009852018145226989 158460614253694506804460121)
      ·
        refine ⟨118845460690270880103345091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158460614253694506804460121 118845460690270880103345091)
        ·
          refine ⟨178268191035406320155017637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118845460690270880103345091 178268191035406320155017637)
          ·
            refine ⟨33425285819138685029065807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178268191035406320155017637 33425285819138685029065807)
            ·
              refine ⟨50137928728708027543598711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33425285819138685029065807 50137928728708027543598711)
              ·
                refine ⟨75206893093062041315398067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50137928728708027543598711 75206893093062041315398067)
                ·
                  refine ⟨112810339639593061973097101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75206893093062041315398067 112810339639593061973097101)
                  ·
                    refine ⟨42303877364847398239911413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112810339639593061973097101 42303877364847398239911413)
                    ·
                      refine ⟨3965988502954443584991695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42303877364847398239911413 3965988502954443584991695)
                      ·
                        rfl

theorem cell23_7723735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_7723735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723735 prefixEnd_7723735 := by exact prefixLift 7723735
  have htrace : WordTrace (prefixWord ++ tailWord_7723735) baseStart_7723735 baseEnd_7723735 := by
    simpa [prefixWord, tailWord_7723735, baseEnd_7723735] using wordTrace_append hprefix tailTrace_7723735
  have hstable : (prefixWord ++ tailWord_7723735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723735).length < 2 ^ (prefixWord ++ tailWord_7723735).sum := by decide
  have hdescent : baseEnd_7723735 < baseStart_7723735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723785 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 1, 7]
def baseStart_7723785 : Nat := 118140960795 + 7723785 * 2 ^ 59
def prefixEnd_7723785 : Nat := 4983230072969 + 3 ^ 40 * 7723785 * 2
def baseEnd_7723785 : Nat := 1322004725662389463122155

theorem tailTrace_7723785 : CollatzResearch.WordTrace tailWord_7723785 prefixEnd_7723785 1322004725662389463122155 := by
  unfold tailWord_7723785
  simp only [CollatzResearch.WordTrace]
  refine ⟨281709582323053537302804809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187806388215369024868536539 281709582323053537302804809)
  ·
    refine ⟨211282186742290152977103607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281709582323053537302804809 211282186742290152977103607)
    ·
      refine ⟨316923280113435229465655411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211282186742290152977103607 316923280113435229465655411)
      ·
        refine ⟨475384920170152844198483117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316923280113435229465655411 475384920170152844198483117)
        ·
          refine ⟨178269345063807316574431169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475384920170152844198483117 178269345063807316574431169)
          ·
            refine ⟨133702008797855487430823377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178269345063807316574431169 133702008797855487430823377)
            ·
              refine ⟨100276506598391615573117533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133702008797855487430823377 100276506598391615573117533)
              ·
                refine ⟨37603689974396855839919075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100276506598391615573117533 37603689974396855839919075)
                ·
                  refine ⟨56405534961595283759878613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37603689974396855839919075 56405534961595283759878613)
                  ·
                    refine ⟨1322004725662389463122155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56405534961595283759878613 1322004725662389463122155)
                    ·
                      rfl

theorem cell23_7723785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 7].length) (baseStart_7723785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723785 prefixEnd_7723785 := by exact prefixLift 7723785
  have htrace : WordTrace (prefixWord ++ tailWord_7723785) baseStart_7723785 baseEnd_7723785 := by
    simpa [prefixWord, tailWord_7723785, baseEnd_7723785] using wordTrace_append hprefix tailTrace_7723785
  have hstable : (prefixWord ++ tailWord_7723785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723785).length < 2 ^ (prefixWord ++ tailWord_7723785).sum := by decide
  have hdescent : baseEnd_7723785 < baseStart_7723785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723795 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 5]
def baseStart_7723795 : Nat := 118140960795 + 7723795 * 2 ^ 59
def prefixEnd_7723795 : Nat := 4983230072969 + 3 ^ 40 * 7723795 * 2
def baseEnd_7723795 : Nat := 3966019311793713350241419

theorem tailTrace_7723795 : CollatzResearch.WordTrace tailWord_7723795 prefixEnd_7723795 3966019311793713350241419 := by
  unfold tailWord_7723795
  simp only [CollatzResearch.WordTrace]
  refine ⟨281709947053017309010668839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187806631368678206007112559 281709947053017309010668839)
  ·
    refine ⟨422564920579525963516003259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281709947053017309010668839 422564920579525963516003259)
    ·
      refine ⟨633847380869288945274004889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422564920579525963516003259 633847380869288945274004889)
      ·
        refine ⟨475385535651966708955503667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633847380869288945274004889 475385535651966708955503667)
        ·
          refine ⟨713078303477950063433255501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475385535651966708955503667 713078303477950063433255501)
          ·
            refine ⟨267404363804231273787470813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 713078303477950063433255501 267404363804231273787470813)
            ·
              refine ⟨100276636426586727670301555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267404363804231273787470813 100276636426586727670301555)
              ·
                refine ⟨150414954639880091505452333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100276636426586727670301555 150414954639880091505452333)
                ·
                  refine ⟨56405607989955034314544625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150414954639880091505452333 56405607989955034314544625)
                  ·
                    refine ⟨42304205992466275735908469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56405607989955034314544625 42304205992466275735908469)
                    ·
                      refine ⟨3966019311793713350241419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42304205992466275735908469 3966019311793713350241419)
                      ·
                        rfl

theorem cell23_7723795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_7723795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723795 prefixEnd_7723795 := by exact prefixLift 7723795
  have htrace : WordTrace (prefixWord ++ tailWord_7723795) baseStart_7723795 baseEnd_7723795 := by
    simpa [prefixWord, tailWord_7723795, baseEnd_7723795] using wordTrace_append hprefix tailTrace_7723795
  have hstable : (prefixWord ++ tailWord_7723795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723795).length < 2 ^ (prefixWord ++ tailWord_7723795).sum := by decide
  have hdescent : baseEnd_7723795 < baseStart_7723795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723802 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 2, 5]
def baseStart_7723802 : Nat := 118140960795 + 7723802 * 2 ^ 59
def prefixEnd_7723802 : Nat := 4983230072969 + 3 ^ 40 * 7723802 * 2
def baseEnd_7723802 : Nat := 1322007635386098274284629

theorem tailTrace_7723802 : CollatzResearch.WordTrace tailWord_7723802 prefixEnd_7723802 1322007635386098274284629 := by
  unfold tailWord_7723802
  simp only [CollatzResearch.WordTrace]
  refine ⟨70427550590997987301543415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187806801575994632804115773 70427550590997987301543415)
  ·
    refine ⟨105641325886496980952315123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70427550590997987301543415 105641325886496980952315123)
    ·
      refine ⟨158461988829745471428472685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105641325886496980952315123 158461988829745471428472685)
      ·
        refine ⟨59423245811154551785677257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158461988829745471428472685 59423245811154551785677257)
        ·
          refine ⟨44567434358365913839257943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59423245811154551785677257 44567434358365913839257943)
          ·
            refine ⟨66851151537548870758886915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44567434358365913839257943 66851151537548870758886915)
            ·
              refine ⟨100276727306323306138330373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66851151537548870758886915 100276727306323306138330373)
              ·
                refine ⟨18801886369935619900936945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100276727306323306138330373 18801886369935619900936945)
                ·
                  refine ⟨14101414777451714925702709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18801886369935619900936945 14101414777451714925702709)
                  ·
                    refine ⟨1322007635386098274284629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14101414777451714925702709 1322007635386098274284629)
                    ·
                      rfl

theorem cell23_7723802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_7723802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723802 prefixEnd_7723802 := by exact prefixLift 7723802
  have htrace : WordTrace (prefixWord ++ tailWord_7723802) baseStart_7723802 baseEnd_7723802 := by
    simpa [prefixWord, tailWord_7723802, baseEnd_7723802] using wordTrace_append hprefix tailTrace_7723802
  have hstable : (prefixWord ++ tailWord_7723802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723802).length < 2 ^ (prefixWord ++ tailWord_7723802).sum := by decide
  have hdescent : baseEnd_7723802 < baseStart_7723802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723839 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 4]
def baseStart_7723839 : Nat := 118140960795 + 7723839 * 2 ^ 59
def prefixEnd_7723839 : Nat := 4983230072969 + 3 ^ 40 * 7723839 * 2
def baseEnd_7723839 : Nat := 3966041904942511178091217

theorem tailTrace_7723839 : CollatzResearch.WordTrace tailWord_7723839 prefixEnd_7723839 3966041904942511178091217 := by
  unfold tailWord_7723839
  simp only [CollatzResearch.WordTrace]
  refine ⟨281711551864857904525270571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187807701243238603016847047 281711551864857904525270571)
  ·
    refine ⟨422567327797286856787905857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281711551864857904525270571 422567327797286856787905857)
    ·
      refine ⟨316925495847965142590929393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422567327797286856787905857 316925495847965142590929393)
      ·
        refine ⟨237694121885973856943197045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316925495847965142590929393 237694121885973856943197045)
        ·
          refine ⟨22283823926810049088424723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237694121885973856943197045 22283823926810049088424723)
          ·
            refine ⟨33425735890215073632637085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22283823926810049088424723 33425735890215073632637085)
            ·
              refine ⟨12534650958830652612238907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33425735890215073632637085 12534650958830652612238907)
              ·
                refine ⟨18801976438245978918358361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12534650958830652612238907 18801976438245978918358361)
                ·
                  refine ⟨14101482328684484188768771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18801976438245978918358361 14101482328684484188768771)
                  ·
                    refine ⟨21152223493026726283153157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14101482328684484188768771 21152223493026726283153157)
                    ·
                      refine ⟨3966041904942511178091217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21152223493026726283153157 3966041904942511178091217)
                      ·
                        rfl

theorem cell23_7723839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_7723839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723839 prefixEnd_7723839 := by exact prefixLift 7723839
  have htrace : WordTrace (prefixWord ++ tailWord_7723839) baseStart_7723839 baseEnd_7723839 := by
    simpa [prefixWord, tailWord_7723839, baseEnd_7723839] using wordTrace_append hprefix tailTrace_7723839
  have hstable : (prefixWord ++ tailWord_7723839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723839).length < 2 ^ (prefixWord ++ tailWord_7723839).sum := by decide
  have hdescent : baseEnd_7723839 < baseStart_7723839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723852 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_7723852 : Nat := 118140960795 + 7723852 * 2 ^ 59
def prefixEnd_7723852 : Nat := 4983230072969 + 3 ^ 40 * 7723852 * 2
def baseEnd_7723852 : Nat := 3966048580191019627228657

theorem tailTrace_7723852 : CollatzResearch.WordTrace tailWord_7723852 prefixEnd_7723852 3966048580191019627228657 := by
  unfold tailWord_7723852
  simp only [CollatzResearch.WordTrace]
  refine ⟨140856013006905403872746905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187808017342540538496995873 140856013006905403872746905)
  ·
    refine ⟨105642009755179052904560179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140856013006905403872746905 105642009755179052904560179)
    ·
      refine ⟨158463014632768579356840269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105642009755179052904560179 158463014632768579356840269)
      ·
        refine ⟨59423630487288217258815101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158463014632768579356840269 59423630487288217258815101)
        ·
          refine ⟨22283861432733081472055663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59423630487288217258815101 22283861432733081472055663)
          ·
            refine ⟨33425792149099622208083495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22283861432733081472055663 33425792149099622208083495)
            ·
              refine ⟨50138688223649433312125243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33425792149099622208083495 50138688223649433312125243)
              ·
                refine ⟨75208032335474149968187865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50138688223649433312125243 75208032335474149968187865)
                ·
                  refine ⟨56406024251605612476140899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75208032335474149968187865 56406024251605612476140899)
                  ·
                    refine ⟨84609036377408418714211349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56406024251605612476140899 84609036377408418714211349)
                    ·
                      refine ⟨3966048580191019627228657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84609036377408418714211349 3966048580191019627228657)
                      ·
                        rfl

theorem cell23_7723852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_7723852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723852 prefixEnd_7723852 := by exact prefixLift 7723852
  have htrace : WordTrace (prefixWord ++ tailWord_7723852) baseStart_7723852 baseEnd_7723852 := by
    simpa [prefixWord, tailWord_7723852, baseEnd_7723852] using wordTrace_append hprefix tailTrace_7723852
  have hstable : (prefixWord ++ tailWord_7723852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723852).length < 2 ^ (prefixWord ++ tailWord_7723852).sum := by decide
  have hdescent : baseEnd_7723852 < baseStart_7723852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723855 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 7]
def baseStart_7723855 : Nat := 118140960795 + 7723855 * 2 ^ 59
def prefixEnd_7723855 : Nat := 4983230072969 + 3 ^ 40 * 7723855 * 2
def baseEnd_7723855 : Nat := 3966050120632983115491143

theorem tailTrace_7723855 : CollatzResearch.WordTrace tailWord_7723855 prefixEnd_7723855 3966050120632983115491143 := by
  unfold tailWord_7723855
  simp only [CollatzResearch.WordTrace]
  refine ⟨281712135432799939257853019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187808090288533292838568679 281712135432799939257853019)
  ·
    refine ⟨422568203149199908886779529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281712135432799939257853019 422568203149199908886779529)
    ·
      refine ⟨316926152361899931665084647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422568203149199908886779529 316926152361899931665084647)
      ·
        refine ⟨475389228542849897497626971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316926152361899931665084647 475389228542849897497626971)
        ·
          refine ⟨713083842814274846246440457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475389228542849897497626971 713083842814274846246440457)
          ·
            refine ⟨534812882110706134684830343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713083842814274846246440457 534812882110706134684830343)
            ·
              refine ⟨802219323166059202027245515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534812882110706134684830343 802219323166059202027245515)
              ·
                refine ⟨1203328984749088803040868273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802219323166059202027245515 1203328984749088803040868273)
                ·
                  refine ⟨902496738561816602280651205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1203328984749088803040868273 902496738561816602280651205)
                  ·
                    refine ⟨169218138480340612927622101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 902496738561816602280651205 169218138480340612927622101)
                    ·
                      refine ⟨3966050120632983115491143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169218138480340612927622101 3966050120632983115491143)
                      ·
                        rfl

theorem cell23_7723855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_7723855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723855 prefixEnd_7723855 := by exact prefixLift 7723855
  have htrace : WordTrace (prefixWord ++ tailWord_7723855) baseStart_7723855 baseEnd_7723855 := by
    simpa [prefixWord, tailWord_7723855, baseEnd_7723855] using wordTrace_append hprefix tailTrace_7723855
  have hstable : (prefixWord ++ tailWord_7723855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723855).length < 2 ^ (prefixWord ++ tailWord_7723855).sum := by decide
  have hdescent : baseEnd_7723855 < baseStart_7723855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723866 : List Nat := [3, 1, 1, 2, 1, 4, 2, 4, 1, 4]
def baseStart_7723866 : Nat := 118140960795 + 7723866 * 2 ^ 59
def prefixEnd_7723866 : Nat := 4983230072969 + 3 ^ 40 * 7723866 * 2
def baseEnd_7723866 : Nat := 1322018589640060857484531

theorem tailTrace_7723866 : CollatzResearch.WordTrace tailWord_7723866 prefixEnd_7723866 1322018589640060857484531 := by
  unfold tailWord_7723866
  simp only [CollatzResearch.WordTrace]
  refine ⟨70428134158940022034125863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187808357757173392091002301 70428134158940022034125863)
  ·
    refine ⟨105642201238410033051188795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70428134158940022034125863 105642201238410033051188795)
    ·
      refine ⟨158463301857615049576783193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105642201238410033051188795 158463301857615049576783193)
      ·
        refine ⟨118847476393211287182587395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158463301857615049576783193 118847476393211287182587395)
        ·
          refine ⟨178271214589816930773881093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118847476393211287182587395 178271214589816930773881093)
          ·
            refine ⟨33425852735590674520102705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178271214589816930773881093 33425852735590674520102705)
            ·
              refine ⟨25069389551693005890077029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33425852735590674520102705 25069389551693005890077029)
              ·
                refine ⟨4700510540942438604389443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25069389551693005890077029 4700510540942438604389443)
                ·
                  refine ⟨7050765811413657906584165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700510540942438604389443 7050765811413657906584165)
                  ·
                    refine ⟨1322018589640060857484531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7050765811413657906584165 1322018589640060857484531)
                    ·
                      rfl

theorem cell23_7723866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_7723866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723866 prefixEnd_7723866 := by exact prefixLift 7723866
  have htrace : WordTrace (prefixWord ++ tailWord_7723866) baseStart_7723866 baseEnd_7723866 := by
    simpa [prefixWord, tailWord_7723866, baseEnd_7723866] using wordTrace_append hprefix tailTrace_7723866
  have hstable : (prefixWord ++ tailWord_7723866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723866).length < 2 ^ (prefixWord ++ tailWord_7723866).sum := by decide
  have hdescent : baseEnd_7723866 < baseStart_7723866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723899 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 1, 5, 2]
def baseStart_7723899 : Nat := 118140960795 + 7723899 * 2 ^ 59
def prefixEnd_7723899 : Nat := 4983230072969 + 3 ^ 40 * 7723899 * 2
def baseEnd_7723899 : Nat := 3966072713781780943340941

theorem tailTrace_7723899 : CollatzResearch.WordTrace tailWord_7723899 prefixEnd_7723899 3966072713781780943340941 := by
  unfold tailWord_7723899
  simp only [CollatzResearch.WordTrace]
  refine ⟨281713740244640534772454751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187809160163093689848303167 281713740244640534772454751)
  ·
    refine ⟨422570610366960802158682127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281713740244640534772454751 422570610366960802158682127)
    ·
      refine ⟨633855915550441203238023191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422570610366960802158682127 633855915550441203238023191)
      ·
        refine ⟨950783873325661804857034787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633855915550441203238023191 950783873325661804857034787)
        ·
          refine ⟨1426175809988492707285552181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950783873325661804857034787 1426175809988492707285552181)
          ·
            refine ⟨133703982186421191308020517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1426175809988492707285552181 133703982186421191308020517)
            ·
              refine ⟨25069496659953973370253847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133703982186421191308020517 25069496659953973370253847)
              ·
                refine ⟨37604244989930960055380771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25069496659953973370253847 37604244989930960055380771)
                ·
                  refine ⟨56406367484896440083071157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37604244989930960055380771 56406367484896440083071157)
                  ·
                    refine ⟨5288096951709041257787921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56406367484896440083071157 5288096951709041257787921)
                    ·
                      refine ⟨3966072713781780943340941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288096951709041257787921 3966072713781780943340941)
                      ·
                        rfl

theorem cell23_7723899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 5, 2].length) (baseStart_7723899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723899 prefixEnd_7723899 := by exact prefixLift 7723899
  have htrace : WordTrace (prefixWord ++ tailWord_7723899) baseStart_7723899 baseEnd_7723899 := by
    simpa [prefixWord, tailWord_7723899, baseEnd_7723899] using wordTrace_append hprefix tailTrace_7723899
  have hstable : (prefixWord ++ tailWord_7723899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723899).length < 2 ^ (prefixWord ++ tailWord_7723899).sum := by decide
  have hdescent : baseEnd_7723899 < baseStart_7723899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723909 : List Nat := [1, 3, 1, 1, 3, 3, 2, 3, 1, 5]
def baseStart_7723909 : Nat := 118140960795 + 7723909 * 2 ^ 59
def prefixEnd_7723909 : Nat := 4983230072969 + 3 ^ 40 * 7723909 * 2
def baseEnd_7723909 : Nat := 1322025949529441968071965

theorem tailTrace_7723909 : CollatzResearch.WordTrace tailWord_7723909 prefixEnd_7723909 1322025949529441968071965 := by
  unfold tailWord_7723909
  simp only [CollatzResearch.WordTrace]
  refine ⟨281714104974604306480318781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187809403316402870986879187 281714104974604306480318781)
  ·
    refine ⟨105642789365476614930119543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281714104974604306480318781 105642789365476614930119543)
    ·
      refine ⟨158464184048214922395179315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105642789365476614930119543 158464184048214922395179315)
      ·
        refine ⟨237696276072322383592768973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158464184048214922395179315 237696276072322383592768973)
        ·
          refine ⟨89136103527120893847288365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237696276072322383592768973 89136103527120893847288365)
          ·
            refine ⟨33426038822670335192733137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89136103527120893847288365 33426038822670335192733137)
            ·
              refine ⟨25069529117002751394549853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33426038822670335192733137 25069529117002751394549853)
              ·
                refine ⟨9401073418876031772956195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25069529117002751394549853 9401073418876031772956195)
                ·
                  refine ⟨14101610128314047659434293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9401073418876031772956195 14101610128314047659434293)
                  ·
                    refine ⟨1322025949529441968071965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14101610128314047659434293 1322025949529441968071965)
                    ·
                      rfl

theorem cell23_7723909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_7723909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723909 prefixEnd_7723909 := by exact prefixLift 7723909
  have htrace : WordTrace (prefixWord ++ tailWord_7723909) baseStart_7723909 baseEnd_7723909 := by
    simpa [prefixWord, tailWord_7723909, baseEnd_7723909] using wordTrace_append hprefix tailTrace_7723909
  have hstable : (prefixWord ++ tailWord_7723909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723909).length < 2 ^ (prefixWord ++ tailWord_7723909).sum := by decide
  have hdescent : baseEnd_7723909 < baseStart_7723909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723943 : List Nat := [1, 1, 6, 1, 3, 2, 1, 2, 1, 5]
def baseStart_7723943 : Nat := 118140960795 + 7723943 * 2 ^ 59
def prefixEnd_7723943 : Nat := 4983230072969 + 3 ^ 40 * 7723943 * 2
def baseEnd_7723943 : Nat := 1322031768976859590396913

theorem tailTrace_7723943 : CollatzResearch.WordTrace tailWord_7723943 prefixEnd_7723943 1322031768976859590396913 := by
  unfold tailWord_7723943
  simp only [CollatzResearch.WordTrace]
  refine ⟨281715345056481130287056483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187810230037654086858037655 281715345056481130287056483)
  ·
    refine ⟨422573017584721695430584725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281715345056481130287056483 422573017584721695430584725)
    ·
      refine ⟨19808110199283829473308659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 422573017584721695430584725 19808110199283829473308659)
      ·
        refine ⟨29712165298925744209962989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19808110199283829473308659 29712165298925744209962989)
        ·
          refine ⟨11142061987097154078736121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29712165298925744209962989 11142061987097154078736121)
          ·
            refine ⟨8356546490322865559052091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11142061987097154078736121 8356546490322865559052091)
            ·
              refine ⟨12534819735484298338578137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8356546490322865559052091 12534819735484298338578137)
              ·
                refine ⟨9401114801613223753933603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12534819735484298338578137 9401114801613223753933603)
                ·
                  refine ⟨14101672202419835630900405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9401114801613223753933603 14101672202419835630900405)
                  ·
                    refine ⟨1322031768976859590396913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14101672202419835630900405 1322031768976859590396913)
                    ·
                      rfl

theorem cell23_7723943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_7723943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723943 prefixEnd_7723943 := by exact prefixLift 7723943
  have htrace : WordTrace (prefixWord ++ tailWord_7723943) baseStart_7723943 baseEnd_7723943 := by
    simpa [prefixWord, tailWord_7723943, baseEnd_7723943] using wordTrace_append hprefix tailTrace_7723943
  have hstable : (prefixWord ++ tailWord_7723943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723943).length < 2 ^ (prefixWord ++ tailWord_7723943).sum := by decide
  have hdescent : baseEnd_7723943 < baseStart_7723943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723956 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_7723956 : Nat := 118140960795 + 7723956 * 2 ^ 59
def prefixEnd_7723956 : Nat := 4983230072969 + 3 ^ 40 * 7723956 * 2
def baseEnd_7723956 : Nat := 1322033994059695740109393

theorem tailTrace_7723956 : CollatzResearch.WordTrace tailWord_7723956 prefixEnd_7723956 1322033994059695740109393 := by
  unfold tailWord_7723956
  simp only [CollatzResearch.WordTrace]
  refine ⟨140857909602717016753639861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187810546136956022338186481 140857909602717016753639861)
  ·
    refine ⟨13205429025254720320653737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140857909602717016753639861 13205429025254720320653737)
    ·
      refine ⟨9904071768941040240490303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13205429025254720320653737 9904071768941040240490303)
      ·
        refine ⟨14856107653411560360735455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9904071768941040240490303 14856107653411560360735455)
        ·
          refine ⟨22284161480117340541103183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14856107653411560360735455 22284161480117340541103183)
          ·
            refine ⟨33426242220176010811654775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22284161480117340541103183 33426242220176010811654775)
            ·
              refine ⟨50139363330264016217482163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33426242220176010811654775 50139363330264016217482163)
              ·
                refine ⟨75209044995396024326223245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50139363330264016217482163 75209044995396024326223245)
                ·
                  refine ⟨28203391873273509122333717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75209044995396024326223245 28203391873273509122333717)
                  ·
                    refine ⟨1322033994059695740109393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28203391873273509122333717 1322033994059695740109393)
                    ·
                      rfl

theorem cell23_7723956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_7723956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723956 prefixEnd_7723956 := by exact prefixLift 7723956
  have htrace : WordTrace (prefixWord ++ tailWord_7723956) baseStart_7723956 baseEnd_7723956 := by
    simpa [prefixWord, tailWord_7723956, baseEnd_7723956] using wordTrace_append hprefix tailTrace_7723956
  have hstable : (prefixWord ++ tailWord_7723956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723956).length < 2 ^ (prefixWord ++ tailWord_7723956).sum := by decide
  have hdescent : baseEnd_7723956 < baseStart_7723956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723980 : List Nat := [2, 2, 1, 4, 1, 1, 3, 4, 1, 2, 2]
def baseStart_7723980 : Nat := 118140960795 + 7723980 * 2 ^ 59
def prefixEnd_7723980 : Nat := 4983230072969 + 3 ^ 40 * 7723980 * 2
def baseEnd_7723980 : Nat := 3966114305714795126428069

theorem tailTrace_7723980 : CollatzResearch.WordTrace tailWord_7723980 prefixEnd_7723980 3966114305714795126428069 := by
  unfold tailWord_7723980
  simp only [CollatzResearch.WordTrace]
  refine ⟨140858347278673542803076697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187811129704898057070768929 140858347278673542803076697)
  ·
    refine ⟨105643760459005157102307523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140858347278673542803076697 105643760459005157102307523)
    ·
      refine ⟨158465640688507735653461285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105643760459005157102307523 158465640688507735653461285)
      ·
        refine ⟨29712307629095200435023991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158465640688507735653461285 29712307629095200435023991)
        ·
          refine ⟨44568461443642800652535987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29712307629095200435023991 44568461443642800652535987)
          ·
            refine ⟨66852692165464200978803981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44568461443642800652535987 66852692165464200978803981)
            ·
              refine ⟨25069759562049075367051493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66852692165464200978803981 25069759562049075367051493)
              ·
                refine ⟨4700579917884201631322155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25069759562049075367051493 4700579917884201631322155)
                ·
                  refine ⟨7050869876826302446983233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700579917884201631322155 7050869876826302446983233)
                  ·
                    refine ⟨5288152407619726835237425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7050869876826302446983233 5288152407619726835237425)
                    ·
                      refine ⟨3966114305714795126428069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288152407619726835237425 3966114305714795126428069)
                      ·
                        rfl

theorem cell23_7723980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_7723980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723980 prefixEnd_7723980 := by exact prefixLift 7723980
  have htrace : WordTrace (prefixWord ++ tailWord_7723980) baseStart_7723980 baseEnd_7723980 := by
    simpa [prefixWord, tailWord_7723980, baseEnd_7723980] using wordTrace_append hprefix tailTrace_7723980
  have hstable : (prefixWord ++ tailWord_7723980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723980).length < 2 ^ (prefixWord ++ tailWord_7723980).sum := by decide
  have hdescent : baseEnd_7723980 < baseStart_7723980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7723986 : List Nat := [3, 2, 2, 3, 1, 3, 1, 8]
def baseStart_7723986 : Nat := 118140960795 + 7723986 * 2 ^ 59
def prefixEnd_7723986 : Nat := 4983230072969 + 3 ^ 40 * 7723986 * 2
def baseEnd_7723986 : Nat := 146893236540693411220483

theorem tailTrace_7723986 : CollatzResearch.WordTrace tailWord_7723986 prefixEnd_7723986 146893236540693411220483 := by
  unfold tailWord_7723986
  simp only [CollatzResearch.WordTrace]
  refine ⟨70429228348831337157717953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187811275596883565753914541 70429228348831337157717953)
  ·
    refine ⟨52821921261623502868288465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70429228348831337157717953 52821921261623502868288465)
    ·
      refine ⟨39616440946217627151216349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52821921261623502868288465 39616440946217627151216349)
      ·
        refine ⟨14856165354831610181706131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39616440946217627151216349 14856165354831610181706131)
        ·
          refine ⟨22284248032247415272559197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14856165354831610181706131 22284248032247415272559197)
          ·
            refine ⟨8356593012092780727209699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22284248032247415272559197 8356593012092780727209699)
            ·
              refine ⟨12534889518139171090814549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8356593012092780727209699 12534889518139171090814549)
              ·
                refine ⟨146893236540693411220483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12534889518139171090814549 146893236540693411220483)
                ·
                  rfl

theorem cell23_7723986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 8].length) (baseStart_7723986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7723986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7723986 prefixEnd_7723986 := by exact prefixLift 7723986
  have htrace : WordTrace (prefixWord ++ tailWord_7723986) baseStart_7723986 baseEnd_7723986 := by
    simpa [prefixWord, tailWord_7723986, baseEnd_7723986] using wordTrace_append hprefix tailTrace_7723986
  have hstable : (prefixWord ++ tailWord_7723986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7723986).length < 2 ^ (prefixWord ++ tailWord_7723986).sum := by decide
  have hdescent : baseEnd_7723986 < baseStart_7723986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7723986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724020 : List Nat := [2, 6, 2, 1, 1, 1, 10]
def baseStart_7724020 : Nat := 118140960795 + 7724020 * 2 ^ 59
def prefixEnd_7724020 : Nat := 4983230072969 + 3 ^ 40 * 7724020 * 2
def baseEnd_7724020 : Nat := 48964627715320678641085

theorem tailTrace_7724020 : CollatzResearch.WordTrace tailWord_7724020 prefixEnd_7724020 48964627715320678641085 := by
  unfold tailWord_7724020
  simp only [CollatzResearch.WordTrace]
  refine ⟨140859076738601086218804757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187812102318134781625073009 140859076738601086218804757)
  ·
    refine ⟨6602769222121925916506473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140859076738601086218804757 6602769222121925916506473)
    ·
      refine ⟨4952076916591444437379855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6602769222121925916506473 4952076916591444437379855)
      ·
        refine ⟨7428115374887166656069783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4952076916591444437379855 7428115374887166656069783)
        ·
          refine ⟨11142173062330749984104675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7428115374887166656069783 11142173062330749984104675)
          ·
            refine ⟨16713259593496124976157013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11142173062330749984104675 16713259593496124976157013)
            ·
              refine ⟨48964627715320678641085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16713259593496124976157013 48964627715320678641085)
              ·
                rfl

theorem cell23_7724020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 10].length) (baseStart_7724020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724020 prefixEnd_7724020 := by exact prefixLift 7724020
  have htrace : WordTrace (prefixWord ++ tailWord_7724020) baseStart_7724020 baseEnd_7724020 := by
    simpa [prefixWord, tailWord_7724020, baseEnd_7724020] using wordTrace_append hprefix tailTrace_7724020
  have hstable : (prefixWord ++ tailWord_7724020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724020).length < 2 ^ (prefixWord ++ tailWord_7724020).sum := by decide
  have hdescent : baseEnd_7724020 < baseStart_7724020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724030 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_7724030 : Nat := 118140960795 + 7724030 * 2 ^ 59
def prefixEnd_7724030 : Nat := 4983230072969 + 3 ^ 40 * 7724030 * 2
def baseEnd_7724030 : Nat := 3966139979747519930802839

theorem tailTrace_7724030 : CollatzResearch.WordTrace tailWord_7724030 prefixEnd_7724030 3966139979747519930802839 := by
  unfold tailWord_7724030
  simp only [CollatzResearch.WordTrace]
  refine ⟨35214814775895743018184193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187812345471443962763649029 35214814775895743018184193)
  ·
    refine ⟨26411111081921807263638145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35214814775895743018184193 26411111081921807263638145)
    ·
      refine ⟨19808333311441355447728609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26411111081921807263638145 19808333311441355447728609)
      ·
        refine ⟨14856249983581016585796457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19808333311441355447728609 14856249983581016585796457)
        ·
          refine ⟨11142187487685762439347343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14856249983581016585796457 11142187487685762439347343)
          ·
            refine ⟨16713281231528643659021015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11142187487685762439347343 16713281231528643659021015)
            ·
              refine ⟨25069921847292965488531523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16713281231528643659021015 25069921847292965488531523)
              ·
                refine ⟨37604882770939448232797285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25069921847292965488531523 37604882770939448232797285)
                ·
                  refine ⟨7050915519551146543649491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37604882770939448232797285 7050915519551146543649491)
                  ·
                    refine ⟨10576373279326719815474237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7050915519551146543649491 10576373279326719815474237)
                    ·
                      refine ⟨3966139979747519930802839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10576373279326719815474237 3966139979747519930802839)
                      ·
                        rfl

theorem cell23_7724030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_7724030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724030 prefixEnd_7724030 := by exact prefixLift 7724030
  have htrace : WordTrace (prefixWord ++ tailWord_7724030) baseStart_7724030 baseEnd_7724030 := by
    simpa [prefixWord, tailWord_7724030, baseEnd_7724030] using wordTrace_append hprefix tailTrace_7724030
  have hstable : (prefixWord ++ tailWord_7724030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724030).length < 2 ^ (prefixWord ++ tailWord_7724030).sum := by decide
  have hdescent : baseEnd_7724030 < baseStart_7724030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724053 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 1, 4, 2]
def baseStart_7724053 : Nat := 118140960795 + 7724053 * 2 ^ 59
def prefixEnd_7724053 : Nat := 4983230072969 + 3 ^ 40 * 7724053 * 2
def baseEnd_7724053 : Nat := 3966151789802573340815233

theorem tailTrace_7724053 : CollatzResearch.WordTrace tailWord_7724053 prefixEnd_7724053 3966151789802573340815233 := by
  unfold tailWord_7724053
  simp only [CollatzResearch.WordTrace]
  refine ⟨281719357086082619073560813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187812904724055079382373875 281719357086082619073560813)
  ·
    refine ⟨105644758907280982152585305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281719357086082619073560813 105644758907280982152585305)
    ·
      refine ⟨79233569180460736614438979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105644758907280982152585305 79233569180460736614438979)
      ·
        refine ⟨118850353770691104921658469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79233569180460736614438979 118850353770691104921658469)
        ·
          refine ⟨22284441332004582172810963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118850353770691104921658469 22284441332004582172810963)
          ·
            refine ⟨33426661998006873259216445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22284441332004582172810963 33426661998006873259216445)
            ·
              refine ⟨12534998249252577472206167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33426661998006873259216445 12534998249252577472206167)
              ·
                refine ⟨18802497373878866208309251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12534998249252577472206167 18802497373878866208309251)
                ·
                  refine ⟨28203746060818299312463877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18802497373878866208309251 28203746060818299312463877)
                  ·
                    refine ⟨5288202386403431121086977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28203746060818299312463877 5288202386403431121086977)
                    ·
                      refine ⟨3966151789802573340815233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288202386403431121086977 3966151789802573340815233)
                      ·
                        rfl

theorem cell23_7724053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_7724053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724053 prefixEnd_7724053 := by exact prefixLift 7724053
  have htrace : WordTrace (prefixWord ++ tailWord_7724053) baseStart_7724053 baseEnd_7724053 := by
    simpa [prefixWord, tailWord_7724053, baseEnd_7724053] using wordTrace_append hprefix tailTrace_7724053
  have hstable : (prefixWord ++ tailWord_7724053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724053).length < 2 ^ (prefixWord ++ tailWord_7724053).sum := by decide
  have hdescent : baseEnd_7724053 < baseStart_7724053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724096 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 2, 5, 2]
def baseStart_7724096 : Nat := 118140960795 + 7724096 * 2 ^ 59
def prefixEnd_7724096 : Nat := 4983230072969 + 3 ^ 40 * 7724096 * 2
def baseEnd_7724096 : Nat := 3966173869470716672577535

theorem tailTrace_7724096 : CollatzResearch.WordTrace tailWord_7724096 prefixEnd_7724096 3966173869470716672577535 := by
  unfold tailWord_7724096
  simp only [CollatzResearch.WordTrace]
  refine ⟨140860462712463418708688071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187813950283284558278250761 140860462712463418708688071)
  ·
    refine ⟨211290694068695128063032107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140860462712463418708688071 211290694068695128063032107)
    ·
      refine ⟨316936041103042692094548161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211290694068695128063032107 316936041103042692094548161)
      ·
        refine ⟨237702030827282019070911121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316936041103042692094548161 237702030827282019070911121)
        ·
          refine ⟨178276523120461514303183341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237702030827282019070911121 178276523120461514303183341)
          ·
            refine ⟨66853696170173067863693753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178276523120461514303183341 66853696170173067863693753)
            ·
              refine ⟨50140272127629800897770315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66853696170173067863693753 50140272127629800897770315)
              ·
                refine ⟨75210408191444701346655473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50140272127629800897770315 75210408191444701346655473)
                ·
                  refine ⟨56407806143583526009991605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75210408191444701346655473 56407806143583526009991605)
                  ·
                    refine ⟨5288231825960955563436713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56407806143583526009991605 5288231825960955563436713)
                    ·
                      refine ⟨3966173869470716672577535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288231825960955563436713 3966173869470716672577535)
                      ·
                        rfl

theorem cell23_7724096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 5, 2].length) (baseStart_7724096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724096 prefixEnd_7724096 := by exact prefixLift 7724096
  have htrace : WordTrace (prefixWord ++ tailWord_7724096) baseStart_7724096 baseEnd_7724096 := by
    simpa [prefixWord, tailWord_7724096, baseEnd_7724096] using wordTrace_append hprefix tailTrace_7724096
  have hstable : (prefixWord ++ tailWord_7724096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724096).length < 2 ^ (prefixWord ++ tailWord_7724096).sum := by decide
  have hdescent : baseEnd_7724096 < baseStart_7724096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724099 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 5]
def baseStart_7724099 : Nat := 118140960795 + 7724099 * 2 ^ 59
def prefixEnd_7724099 : Nat := 4983230072969 + 3 ^ 40 * 7724099 * 2
def baseEnd_7724099 : Nat := 3966175409912680160840021

theorem tailTrace_7724099 : CollatzResearch.WordTrace tailWord_7724099 prefixEnd_7724099 3966175409912680160840021 := by
  unfold tailWord_7724099
  simp only [CollatzResearch.WordTrace]
  refine ⟨281721034843915968929735351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187814023229277312619823567 281721034843915968929735351)
  ·
    refine ⟨422581552265873953394603027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281721034843915968929735351 422581552265873953394603027)
    ·
      refine ⟨633872328398810930091904541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422581552265873953394603027 633872328398810930091904541)
      ·
        refine ⟨237702123149554098784464203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 633872328398810930091904541 237702123149554098784464203)
        ·
          refine ⟨356553184724331148176696305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237702123149554098784464203 356553184724331148176696305)
          ·
            refine ⟨267414888543248361132522229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356553184724331148176696305 267414888543248361132522229)
            ·
              refine ⟨25070145800929533856173959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267414888543248361132522229 25070145800929533856173959)
              ·
                refine ⟨37605218701394300784260939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25070145800929533856173959 37605218701394300784260939)
                ·
                  refine ⟨56407828052091451176391409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37605218701394300784260939 56407828052091451176391409)
                  ·
                    refine ⟨42305871039068588382293557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56407828052091451176391409 42305871039068588382293557)
                    ·
                      refine ⟨3966175409912680160840021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42305871039068588382293557 3966175409912680160840021)
                      ·
                        rfl

theorem cell23_7724099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_7724099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724099 prefixEnd_7724099 := by exact prefixLift 7724099
  have htrace : WordTrace (prefixWord ++ tailWord_7724099) baseStart_7724099 baseEnd_7724099 := by
    simpa [prefixWord, tailWord_7724099, baseEnd_7724099] using wordTrace_append hprefix tailTrace_7724099
  have hstable : (prefixWord ++ tailWord_7724099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724099).length < 2 ^ (prefixWord ++ tailWord_7724099).sum := by decide
  have hdescent : baseEnd_7724099 < baseStart_7724099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724193 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 5, 1, 3]
def baseStart_7724193 : Nat := 118140960795 + 7724193 * 2 ^ 59
def prefixEnd_7724193 : Nat := 4983230072969 + 3 ^ 40 * 7724193 * 2
def baseEnd_7724193 : Nat := 3966223677094202793064589

theorem tailTrace_7724193 : CollatzResearch.WordTrace tailWord_7724193 prefixEnd_7724193 3966223677094202793064589 := by
  unfold tailWord_7724193
  simp only [CollatzResearch.WordTrace]
  refine ⟨281724463305575422983657233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187816308870383615322438155 281724463305575422983657233)
  ·
    refine ⟨211293347479181567237742925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281724463305575422983657233 211293347479181567237742925)
    ·
      refine ⟨79235005304693087714153597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211293347479181567237742925 79235005304693087714153597)
      ·
        refine ⟨29713126989259907892807599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79235005304693087714153597 29713126989259907892807599)
        ·
          refine ⟨44569690483889861839211399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29713126989259907892807599 44569690483889861839211399)
          ·
            refine ⟨66854535725834792758817099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44569690483889861839211399 66854535725834792758817099)
            ·
              refine ⟨100281803588752189138225649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66854535725834792758817099 100281803588752189138225649)
              ·
                refine ⟨75211352691564141853669237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100281803588752189138225649 75211352691564141853669237)
                ·
                  refine ⟨7051064314834138298781491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75211352691564141853669237 7051064314834138298781491)
                  ·
                    refine ⟨10576596472251207448172237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7051064314834138298781491 10576596472251207448172237)
                    ·
                      refine ⟨3966223677094202793064589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10576596472251207448172237 3966223677094202793064589)
                      ·
                        rfl

theorem cell23_7724193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_7724193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724193 prefixEnd_7724193 := by exact prefixLift 7724193
  have htrace : WordTrace (prefixWord ++ tailWord_7724193) baseStart_7724193 baseEnd_7724193 := by
    simpa [prefixWord, tailWord_7724193, baseEnd_7724193] using wordTrace_append hprefix tailTrace_7724193
  have hstable : (prefixWord ++ tailWord_7724193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724193).length < 2 ^ (prefixWord ++ tailWord_7724193).sum := by decide
  have hdescent : baseEnd_7724193 < baseStart_7724193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724210 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3]
def baseStart_7724210 : Nat := 118140960795 + 7724210 * 2 ^ 59
def prefixEnd_7724210 : Nat := 4983230072969 + 3 ^ 40 * 7724210 * 2
def baseEnd_7724210 : Nat := 3966232406265329226552011

theorem tailTrace_7724210 : CollatzResearch.WordTrace tailWord_7724210 prefixEnd_7724210 3966232406265329226552011 := by
  unfold tailWord_7724210
  simp only [CollatzResearch.WordTrace]
  refine ⟨70431270836628458721756521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187816722231009223258017389 70431270836628458721756521)
  ·
    refine ⟨52823453127471344041317391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70431270836628458721756521 52823453127471344041317391)
    ·
      refine ⟨79235179691207016061976087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52823453127471344041317391 79235179691207016061976087)
      ·
        refine ⟨118852769536810524092964131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79235179691207016061976087 118852769536810524092964131)
        ·
          refine ⟨178279154305215786139446197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118852769536810524092964131 178279154305215786139446197)
          ·
            refine ⟨16713670716113979950573081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178279154305215786139446197 16713670716113979950573081)
            ·
              refine ⟨12535253037085484962929811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16713670716113979950573081 12535253037085484962929811)
              ·
                refine ⟨18802879555628227444394717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12535253037085484962929811 18802879555628227444394717)
                ·
                  refine ⟨7051079833360585291648019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18802879555628227444394717 7051079833360585291648019)
                  ·
                    refine ⟨10576619750040877937472029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7051079833360585291648019 10576619750040877937472029)
                    ·
                      refine ⟨3966232406265329226552011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10576619750040877937472029 3966232406265329226552011)
                      ·
                        rfl

theorem cell23_7724210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_7724210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724210 prefixEnd_7724210 := by exact prefixLift 7724210
  have htrace : WordTrace (prefixWord ++ tailWord_7724210) baseStart_7724210 baseEnd_7724210 := by
    simpa [prefixWord, tailWord_7724210, baseEnd_7724210] using wordTrace_append hprefix tailTrace_7724210
  have hstable : (prefixWord ++ tailWord_7724210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724210).length < 2 ^ (prefixWord ++ tailWord_7724210).sum := by decide
  have hdescent : baseEnd_7724210 < baseStart_7724210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724216 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 3, 1, 4]
def baseStart_7724216 : Nat := 118140960795 + 7724216 * 2 ^ 59
def prefixEnd_7724216 : Nat := 4983230072969 + 3 ^ 40 * 7724216 * 2
def baseEnd_7724216 : Nat := 3966235487149256203076983

theorem tailTrace_7724216 : CollatzResearch.WordTrace tailWord_7724216 prefixEnd_7724216 3966235487149256203076983 := by
  unfold tailWord_7724216
  simp only [CollatzResearch.WordTrace]
  refine ⟨140862651092246048955872251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187816868122994731941163001 140862651092246048955872251)
  ·
    refine ⟨211293976638369073433808377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140862651092246048955872251 211293976638369073433808377)
    ·
      refine ⟨158470482478776805075356283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211293976638369073433808377 158470482478776805075356283)
      ·
        refine ⟨237705723718165207613034425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158470482478776805075356283 237705723718165207613034425)
        ·
          refine ⟨178279292788623905709775819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237705723718165207613034425 178279292788623905709775819)
          ·
            refine ⟨267418939182935858564663729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178279292788623905709775819 267418939182935858564663729)
            ·
              refine ⟨200564204387201893923497797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267418939182935858564663729 200564204387201893923497797)
              ·
                refine ⟨37605788322600355110655837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200564204387201893923497797 37605788322600355110655837)
                ·
                  refine ⟨14102170620975133166495939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37605788322600355110655837 14102170620975133166495939)
                  ·
                    refine ⟨21153255931462699749743909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14102170620975133166495939 21153255931462699749743909)
                    ·
                      refine ⟨3966235487149256203076983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21153255931462699749743909 3966235487149256203076983)
                      ·
                        rfl

theorem cell23_7724216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_7724216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724216 prefixEnd_7724216 := by exact prefixLift 7724216
  have htrace : WordTrace (prefixWord ++ tailWord_7724216) baseStart_7724216 baseEnd_7724216 := by
    simpa [prefixWord, tailWord_7724216, baseEnd_7724216] using wordTrace_append hprefix tailTrace_7724216
  have hstable : (prefixWord ++ tailWord_7724216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724216).length < 2 ^ (prefixWord ++ tailWord_7724216).sum := by decide
  have hdescent : baseEnd_7724216 < baseStart_7724216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724256 : List Nat := [2, 1, 1, 3, 1, 6, 9]
def baseStart_7724256 : Nat := 118140960795 + 7724256 * 2 ^ 59
def prefixEnd_7724256 : Nat := 4983230072969 + 3 ^ 40 * 7724256 * 2
def baseEnd_7724256 : Nat := 48966123782412790698479

theorem tailTrace_7724256 : CollatzResearch.WordTrace tailWord_7724256 prefixEnd_7724256 48966123782412790698479 := by
  unfold tailWord_7724256
  simp only [CollatzResearch.WordTrace]
  refine ⟨140863380552173592371600311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187817840736231456495467081 140863380552173592371600311)
  ·
    refine ⟨211295070828260388557400467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140863380552173592371600311 211295070828260388557400467)
    ·
      refine ⟨316942606242390582836100701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211295070828260388557400467 316942606242390582836100701)
      ·
        refine ⟨118853477340896468563537763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316942606242390582836100701 118853477340896468563537763)
        ·
          refine ⟨178280216011344702845306645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118853477340896468563537763 178280216011344702845306645)
          ·
            refine ⟨8356885125531782945873749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 178280216011344702845306645 8356885125531782945873749)
            ·
              refine ⟨48966123782412790698479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8356885125531782945873749 48966123782412790698479)
              ·
                rfl

theorem cell23_7724256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 9].length) (baseStart_7724256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724256 prefixEnd_7724256 := by exact prefixLift 7724256
  have htrace : WordTrace (prefixWord ++ tailWord_7724256) baseStart_7724256 baseEnd_7724256 := by
    simpa [prefixWord, tailWord_7724256, baseEnd_7724256] using wordTrace_append hprefix tailTrace_7724256
  have hstable : (prefixWord ++ tailWord_7724256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724256).length < 2 ^ (prefixWord ++ tailWord_7724256).sum := by decide
  have hdescent : baseEnd_7724256 < baseStart_7724256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724267 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 3, 2, 2]
def baseStart_7724267 : Nat := 118140960795 + 7724267 * 2 ^ 59
def prefixEnd_7724267 : Nat := 4983230072969 + 3 ^ 40 * 7724267 * 2
def baseEnd_7724267 : Nat := 3966261674662635503539249

theorem tailTrace_7724267 : CollatzResearch.WordTrace tailWord_7724267 prefixEnd_7724267 3966261674662635503539249 := by
  unfold tailWord_7724267
  simp only [CollatzResearch.WordTrace]
  refine ⟨281727162307307333621851055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187818108204871555747900703 281727162307307333621851055)
  ·
    refine ⟨422590743460961000432776583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281727162307307333621851055 422590743460961000432776583)
    ·
      refine ⟨633886115191441500649164875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422590743460961000432776583 633886115191441500649164875)
      ·
        refine ⟨950829172787162250973747313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633886115191441500649164875 950829172787162250973747313)
        ·
          refine ⟨713121879590371688230310485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 950829172787162250973747313 713121879590371688230310485)
          ·
            refine ⟨8356897026449668221448951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 713121879590371688230310485 8356897026449668221448951)
            ·
              refine ⟨12535345539674502332173427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8356897026449668221448951 12535345539674502332173427)
              ·
                refine ⟨18803018309511753498260141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12535345539674502332173427 18803018309511753498260141)
                ·
                  refine ⟨7051131866066907561847553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18803018309511753498260141 7051131866066907561847553)
                  ·
                    refine ⟨5288348899550180671385665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7051131866066907561847553 5288348899550180671385665)
                    ·
                      refine ⟨3966261674662635503539249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288348899550180671385665 3966261674662635503539249)
                      ·
                        rfl

theorem cell23_7724267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 2, 2].length) (baseStart_7724267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724267 prefixEnd_7724267 := by exact prefixLift 7724267
  have htrace : WordTrace (prefixWord ++ tailWord_7724267) baseStart_7724267 baseEnd_7724267 := by
    simpa [prefixWord, tailWord_7724267, baseEnd_7724267] using wordTrace_append hprefix tailTrace_7724267
  have hstable : (prefixWord ++ tailWord_7724267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724267).length < 2 ^ (prefixWord ++ tailWord_7724267).sum := by decide
  have hdescent : baseEnd_7724267 < baseStart_7724267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724317 : List Nat := [1, 4, 2, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_7724317 : Nat := 118140960795 + 7724317 * 2 ^ 59
def prefixEnd_7724317 : Nat := 4983230072969 + 3 ^ 40 * 7724317 * 2
def baseEnd_7724317 : Nat := 3966287348695360307914019

theorem tailTrace_7724317 : CollatzResearch.WordTrace tailWord_7724317 prefixEnd_7724317 3966287348695360307914019 := by
  unfold tailWord_7724317
  simp only [CollatzResearch.WordTrace]
  refine ⟨281728985957126192161171205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187819323971417461440780803 281728985957126192161171205)
  ·
    refine ⟨52824184866961161030219601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281728985957126192161171205 52824184866961161030219601)
    ·
      refine ⟨39618138650220870772664701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52824184866961161030219601 39618138650220870772664701)
      ·
        refine ⟨14856801993832826539749263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39618138650220870772664701 14856801993832826539749263)
        ·
          refine ⟨22285202990749239809623895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14856801993832826539749263 22285202990749239809623895)
          ·
            refine ⟨33427804486123859714435843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22285202990749239809623895 33427804486123859714435843)
            ·
              refine ⟨50141706729185789571653765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33427804486123859714435843 50141706729185789571653765)
              ·
                refine ⟨9401570011722335544685081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50141706729185789571653765 9401570011722335544685081)
                ·
                  refine ⟨7051177508791751658513811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9401570011722335544685081 7051177508791751658513811)
                  ·
                    refine ⟨10576766263187627487770717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7051177508791751658513811 10576766263187627487770717)
                    ·
                      refine ⟨3966287348695360307914019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10576766263187627487770717 3966287348695360307914019)
                      ·
                        rfl

theorem cell23_7724317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_7724317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724317 prefixEnd_7724317 := by exact prefixLift 7724317
  have htrace : WordTrace (prefixWord ++ tailWord_7724317) baseStart_7724317 baseEnd_7724317 := by
    simpa [prefixWord, tailWord_7724317, baseEnd_7724317] using wordTrace_append hprefix tailTrace_7724317
  have hstable : (prefixWord ++ tailWord_7724317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724317).length < 2 ^ (prefixWord ++ tailWord_7724317).sum := by decide
  have hdescent : baseEnd_7724317 < baseStart_7724317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724318 : List Nat := [4, 3, 2, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_7724318 : Nat := 118140960795 + 7724318 * 2 ^ 59
def prefixEnd_7724318 : Nat := 4983230072969 + 3 ^ 40 * 7724318 * 2
def baseEnd_7724318 : Nat := 3966287862176014804001515

theorem tailTrace_7724318 : CollatzResearch.WordTrace tailWord_7724318 prefixEnd_7724318 3966287862176014804001515 := by
  unfold tailWord_7724318
  simp only [CollatzResearch.WordTrace]
  refine ⟨35216127803765321166494701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187819348286748379554638405 35216127803765321166494701)
  ·
    refine ⟨13206047926411995437435513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35216127803765321166494701 13206047926411995437435513)
    ·
      refine ⟨9904535944808996578076635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13206047926411995437435513 9904535944808996578076635)
      ·
        refine ⟨14856803917213494867114953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9904535944808996578076635 14856803917213494867114953)
        ·
          refine ⟨11142602937910121150336215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14856803917213494867114953 11142602937910121150336215)
          ·
            refine ⟨16713904406865181725504323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11142602937910121150336215 16713904406865181725504323)
            ·
              refine ⟨25070856610297772588256485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16713904406865181725504323 25070856610297772588256485)
              ·
                refine ⟨4700785614430832360298091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25070856610297772588256485 4700785614430832360298091)
                ·
                  refine ⟨7051178421646248540447137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700785614430832360298091 7051178421646248540447137)
                  ·
                    refine ⟨5288383816234686405335353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7051178421646248540447137 5288383816234686405335353)
                    ·
                      refine ⟨3966287862176014804001515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288383816234686405335353 3966287862176014804001515)
                      ·
                        rfl

theorem cell23_7724318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_7724318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724318 prefixEnd_7724318 := by exact prefixLift 7724318
  have htrace : WordTrace (prefixWord ++ tailWord_7724318) baseStart_7724318 baseEnd_7724318 := by
    simpa [prefixWord, tailWord_7724318, baseEnd_7724318] using wordTrace_append hprefix tailTrace_7724318
  have hstable : (prefixWord ++ tailWord_7724318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724318).length < 2 ^ (prefixWord ++ tailWord_7724318).sum := by decide
  have hdescent : baseEnd_7724318 < baseStart_7724318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724391 : List Nat := [1, 1, 5, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_7724391 : Nat := 118140960795 + 7724391 * 2 ^ 59
def prefixEnd_7724391 : Nat := 4983230072969 + 3 ^ 40 * 7724391 * 2
def baseEnd_7724391 : Nat := 3966325346263793018388679

theorem tailTrace_7724391 : CollatzResearch.WordTrace tailWord_7724391 prefixEnd_7724391 3966325346263793018388679 := by
  unfold tailWord_7724391
  simp only [CollatzResearch.WordTrace]
  refine ⟨281731684958858102799365027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187821123305905401866243351 281731684958858102799365027)
  ·
    refine ⟨422597527438287154199047541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281731684958858102799365027 422597527438287154199047541)
    ·
      refine ⟨39618518197339420706160707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 422597527438287154199047541 39618518197339420706160707)
      ·
        refine ⟨59427777296009131059241061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39618518197339420706160707 59427777296009131059241061)
        ·
          refine ⟨11142708243001712073607699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59427777296009131059241061 11142708243001712073607699)
          ·
            refine ⟨16714062364502568110411549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11142708243001712073607699 16714062364502568110411549)
            ·
              refine ⟨6267773386688463041404331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16714062364502568110411549 6267773386688463041404331)
              ·
                refine ⟨9401660080032694562106497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6267773386688463041404331 9401660080032694562106497)
                ·
                  refine ⟨7051245060024520921579873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9401660080032694562106497 7051245060024520921579873)
                  ·
                    refine ⟨5288433795018390691184905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7051245060024520921579873 5288433795018390691184905)
                    ·
                      refine ⟨3966325346263793018388679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288433795018390691184905 3966325346263793018388679)
                      ·
                        rfl

theorem cell23_7724391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_7724391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724391 prefixEnd_7724391 := by exact prefixLift 7724391
  have htrace : WordTrace (prefixWord ++ tailWord_7724391) baseStart_7724391 baseEnd_7724391 := by
    simpa [prefixWord, tailWord_7724391, baseEnd_7724391] using wordTrace_append hprefix tailTrace_7724391
  have hstable : (prefixWord ++ tailWord_7724391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724391).length < 2 ^ (prefixWord ++ tailWord_7724391).sum := by decide
  have hdescent : baseEnd_7724391 < baseStart_7724391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724413 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_7724413 : Nat := 118140960795 + 7724413 * 2 ^ 59
def prefixEnd_7724413 : Nat := 4983230072969 + 3 ^ 40 * 7724413 * 2
def baseEnd_7724413 : Nat := 3966336642838191932313577

theorem tailTrace_7724413 : CollatzResearch.WordTrace tailWord_7724413 prefixEnd_7724413 3966336642838191932313577 := by
  unfold tailWord_7724413
  simp only [CollatzResearch.WordTrace]
  refine ⟨281732487364778400556665893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187821658243185600371110595 281732487364778400556665893)
  ·
    refine ⟨52824841380895950104374855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281732487364778400556665893 52824841380895950104374855)
    ·
      refine ⟨79237262071343925156562283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52824841380895950104374855 79237262071343925156562283)
      ·
        refine ⟨118855893107015887734843425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79237262071343925156562283 118855893107015887734843425)
        ·
          refine ⟨89141919830261915801132569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118855893107015887734843425 89141919830261915801132569)
          ·
            refine ⟨66856439872696436850849427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89141919830261915801132569 66856439872696436850849427)
            ·
              refine ⟨100284659809044655276274141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66856439872696436850849427 100284659809044655276274141)
              ·
                refine ⟨37606747428391745728602803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100284659809044655276274141 37606747428391745728602803)
                ·
                  refine ⟨56410121142587618592904205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37606747428391745728602803 56410121142587618592904205)
                  ·
                    refine ⟨21153795428470356972339077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56410121142587618592904205 21153795428470356972339077)
                    ·
                      refine ⟨3966336642838191932313577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21153795428470356972339077 3966336642838191932313577)
                      ·
                        rfl

theorem cell23_7724413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_7724413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724413 prefixEnd_7724413 := by exact prefixLift 7724413
  have htrace : WordTrace (prefixWord ++ tailWord_7724413) baseStart_7724413 baseEnd_7724413 := by
    simpa [prefixWord, tailWord_7724413, baseEnd_7724413] using wordTrace_append hprefix tailTrace_7724413
  have hstable : (prefixWord ++ tailWord_7724413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724413).length < 2 ^ (prefixWord ++ tailWord_7724413).sum := by decide
  have hdescent : baseEnd_7724413 < baseStart_7724413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724463 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 3]
def baseStart_7724463 : Nat := 118140960795 + 7724463 * 2 ^ 59
def prefixEnd_7724463 : Nat := 4983230072969 + 3 ^ 40 * 7724463 * 2
def baseEnd_7724463 : Nat := 3966362316870916736688347

theorem tailTrace_7724463 : CollatzResearch.WordTrace tailWord_7724463 prefixEnd_7724463 3966362316870916736688347 := by
  unfold tailWord_7724463
  simp only [CollatzResearch.WordTrace]
  refine ⟨281734311014597259095986043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187822874009731506063990695 281734311014597259095986043)
  ·
    refine ⟨422601466521895888643979065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281734311014597259095986043 422601466521895888643979065)
    ·
      refine ⟨316951099891421916482984299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422601466521895888643979065 316951099891421916482984299)
      ·
        refine ⟨475426649837132874724476449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316951099891421916482984299 475426649837132874724476449)
        ·
          refine ⟨356569987377849656043357337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475426649837132874724476449 356569987377849656043357337)
          ·
            refine ⟨267427490533387242032518003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356569987377849656043357337 267427490533387242032518003)
            ·
              refine ⟨401141235800080863048777005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267427490533387242032518003 401141235800080863048777005)
              ·
                refine ⟨150427963425030323643291377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401141235800080863048777005 150427963425030323643291377)
                ·
                  refine ⟨112820972568772742732468533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150427963425030323643291377 112820972568772742732468533)
                  ·
                    refine ⟨10576966178322444631168925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112820972568772742732468533 10576966178322444631168925)
                    ·
                      refine ⟨3966362316870916736688347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10576966178322444631168925 3966362316870916736688347)
                      ·
                        rfl

theorem cell23_7724463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 3].length) (baseStart_7724463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724463 prefixEnd_7724463 := by exact prefixLift 7724463
  have htrace : WordTrace (prefixWord ++ tailWord_7724463) baseStart_7724463 baseEnd_7724463 := by
    simpa [prefixWord, tailWord_7724463, baseEnd_7724463] using wordTrace_append hprefix tailTrace_7724463
  have hstable : (prefixWord ++ tailWord_7724463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724463).length < 2 ^ (prefixWord ++ tailWord_7724463).sum := by decide
  have hdescent : baseEnd_7724463 < baseStart_7724463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724482 : List Nat := [3, 5, 2, 1, 2, 1, 2, 2, 5]
def baseStart_7724482 : Nat := 118140960795 + 7724482 * 2 ^ 59
def prefixEnd_7724482 : Nat := 4983230072969 + 3 ^ 40 * 7724482 * 2
def baseEnd_7724482 : Nat := 440708008111483573594529

theorem tailTrace_7724482 : CollatzResearch.WordTrace tailWord_7724482 prefixEnd_7724482 440708008111483573594529 := by
  unfold tailWord_7724482
  simp only [CollatzResearch.WordTrace]
  refine ⟨70433751000382106335231925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187823336001018950227285133 70433751000382106335231925)
  ·
    refine ⟨6603164156285822468927993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70433751000382106335231925 6603164156285822468927993)
    ·
      refine ⟨4952373117214366851695995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6603164156285822468927993 4952373117214366851695995)
      ·
        refine ⟨7428559675821550277543993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4952373117214366851695995 7428559675821550277543993)
        ·
          refine ⟨5571419756866162708157995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7428559675821550277543993 5571419756866162708157995)
          ·
            refine ⟨8357129635299244062236993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5571419756866162708157995 8357129635299244062236993)
            ·
              refine ⟨6267847226474433046677745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8357129635299244062236993 6267847226474433046677745)
              ·
                refine ⟨4700885419855824785008309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6267847226474433046677745 4700885419855824785008309)
                ·
                  refine ⟨440708008111483573594529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4700885419855824785008309 440708008111483573594529)
                  ·
                    rfl

theorem cell23_7724482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_7724482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724482 prefixEnd_7724482 := by exact prefixLift 7724482
  have htrace : WordTrace (prefixWord ++ tailWord_7724482) baseStart_7724482 baseEnd_7724482 := by
    simpa [prefixWord, tailWord_7724482, baseEnd_7724482] using wordTrace_append hprefix tailTrace_7724482
  have hstable : (prefixWord ++ tailWord_7724482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724482).length < 2 ^ (prefixWord ++ tailWord_7724482).sum := by decide
  have hdescent : baseEnd_7724482 < baseStart_7724482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724520 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_7724520 : Nat := 118140960795 + 7724520 * 2 ^ 59
def prefixEnd_7724520 : Nat := 4983230072969 + 3 ^ 40 * 7724520 * 2
def baseEnd_7724520 : Nat := 3966391585268223013675585

theorem tailTrace_7724520 : CollatzResearch.WordTrace tailWord_7724520 prefixEnd_7724520 3966391585268223013675585 := by
  unfold tailWord_7724520
  simp only [CollatzResearch.WordTrace]
  refine ⟨140868194987695378915405507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187824259983593838553874009 140868194987695378915405507)
  ·
    refine ⟨211302292481543068373108261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140868194987695378915405507 211302292481543068373108261)
    ·
      refine ⟨39619179840289325319957799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211302292481543068373108261 39619179840289325319957799)
      ·
        refine ⟨59428769760433987979936699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39619179840289325319957799 59428769760433987979936699)
        ·
          refine ⟨89143154640650981969905049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59428769760433987979936699 89143154640650981969905049)
          ·
            refine ⟨66857365980488236477428787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89143154640650981969905049 66857365980488236477428787)
            ·
              refine ⟨100286048970732354716143181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66857365980488236477428787 100286048970732354716143181)
              ·
                refine ⟨37607268364024633018553693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100286048970732354716143181 37607268364024633018553693)
                ·
                  refine ⟨14102725636509237381957635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37607268364024633018553693 14102725636509237381957635)
                  ·
                    refine ⟨21154088454763856072936453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14102725636509237381957635 21154088454763856072936453)
                    ·
                      refine ⟨3966391585268223013675585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21154088454763856072936453 3966391585268223013675585)
                      ·
                        rfl

theorem cell23_7724520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_7724520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724520 prefixEnd_7724520 := by exact prefixLift 7724520
  have htrace : WordTrace (prefixWord ++ tailWord_7724520) baseStart_7724520 baseEnd_7724520 := by
    simpa [prefixWord, tailWord_7724520, baseEnd_7724520] using wordTrace_append hprefix tailTrace_7724520
  have hstable : (prefixWord ++ tailWord_7724520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724520).length < 2 ^ (prefixWord ++ tailWord_7724520).sum := by decide
  have hdescent : baseEnd_7724520 < baseStart_7724520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724523 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 5]
def baseStart_7724523 : Nat := 118140960795 + 7724523 * 2 ^ 59
def prefixEnd_7724523 : Nat := 4983230072969 + 3 ^ 40 * 7724523 * 2
def baseEnd_7724523 : Nat := 3966393125710186501938071

theorem tailTrace_7724523 : CollatzResearch.WordTrace tailWord_7724523 prefixEnd_7724523 3966393125710186501938071 := by
  unfold tailWord_7724523
  simp only [CollatzResearch.WordTrace]
  refine ⟨281736499394379889343170223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187824332929586592895446815 281736499394379889343170223)
  ·
    refine ⟨422604749091569834014755335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281736499394379889343170223 422604749091569834014755335)
    ·
      refine ⟨633907123637354751022133003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422604749091569834014755335 633907123637354751022133003)
      ·
        refine ⟨950860685456032126533199505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633907123637354751022133003 950860685456032126533199505)
        ·
          refine ⟨713145514092024094899899629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 950860685456032126533199505 713145514092024094899899629)
          ·
            refine ⟨267429567784509035587462361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 713145514092024094899899629 267429567784509035587462361)
            ·
              refine ⟨200572175838381776690596771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267429567784509035587462361 200572175838381776690596771)
              ·
                refine ⟨300858263757572665035895157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200572175838381776690596771 300858263757572665035895157)
                ·
                  refine ⟨28205462227272437347115171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 300858263757572665035895157 28205462227272437347115171)
                  ·
                    refine ⟨42308193340908656020672757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28205462227272437347115171 42308193340908656020672757)
                    ·
                      refine ⟨3966393125710186501938071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42308193340908656020672757 3966393125710186501938071)
                      ·
                        rfl

theorem cell23_7724523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 5].length) (baseStart_7724523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724523 prefixEnd_7724523 := by exact prefixLift 7724523
  have htrace : WordTrace (prefixWord ++ tailWord_7724523) baseStart_7724523 baseEnd_7724523 := by
    simpa [prefixWord, tailWord_7724523, baseEnd_7724523] using wordTrace_append hprefix tailTrace_7724523
  have hstable : (prefixWord ++ tailWord_7724523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724523).length < 2 ^ (prefixWord ++ tailWord_7724523).sum := by decide
  have hdescent : baseEnd_7724523 < baseStart_7724523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724534 : List Nat := [5, 1, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_7724534 : Nat := 118140960795 + 7724534 * 2 ^ 59
def prefixEnd_7724534 : Nat := 4983230072969 + 3 ^ 40 * 7724534 * 2
def baseEnd_7724534 : Nat := 1322132924665795319633507

theorem tailTrace_7724534 : CollatzResearch.WordTrace tailWord_7724534 prefixEnd_7724534 1322132924665795319633507 := by
  unfold tailWord_7724534
  simp only [CollatzResearch.WordTrace]
  refine ⟨17608556287333752388863791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187824600398226692147880437 17608556287333752388863791)
  ·
    refine ⟨26412834431000628583295687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17608556287333752388863791 26412834431000628583295687)
    ·
      refine ⟨39619251646500942874943531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26412834431000628583295687 39619251646500942874943531)
      ·
        refine ⟨59428877469751414312415297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39619251646500942874943531 59428877469751414312415297)
        ·
          refine ⟨44571658102313560734311473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59428877469751414312415297 44571658102313560734311473)
          ·
            refine ⟨33428743576735170550733605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44571658102313560734311473 33428743576735170550733605)
            ·
              refine ⟨6267889420637844478262551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33428743576735170550733605 6267889420637844478262551)
              ·
                refine ⟨9401834130956766717393827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6267889420637844478262551 9401834130956766717393827)
                ·
                  refine ⟨14102751196435150076090741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9401834130956766717393827 14102751196435150076090741)
                  ·
                    refine ⟨1322132924665795319633507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14102751196435150076090741 1322132924665795319633507)
                    ·
                      rfl

theorem cell23_7724534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_7724534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724534 prefixEnd_7724534 := by exact prefixLift 7724534
  have htrace : WordTrace (prefixWord ++ tailWord_7724534) baseStart_7724534 baseEnd_7724534 := by
    simpa [prefixWord, tailWord_7724534, baseEnd_7724534] using wordTrace_append hprefix tailTrace_7724534
  have hstable : (prefixWord ++ tailWord_7724534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724534).length < 2 ^ (prefixWord ++ tailWord_7724534).sum := by decide
  have hdescent : baseEnd_7724534 < baseStart_7724534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724537 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 7, 2, 2]
def baseStart_7724537 : Nat := 118140960795 + 7724537 * 2 ^ 59
def prefixEnd_7724537 : Nat := 4983230072969 + 3 ^ 40 * 7724537 * 2
def baseEnd_7724537 : Nat := 3966400314439349447163007

theorem tailTrace_7724537 : CollatzResearch.WordTrace tailWord_7724537 prefixEnd_7724537 3966400314439349447163007 := by
  unfold tailWord_7724537
  simp only [CollatzResearch.WordTrace]
  refine ⟨281737010016329169734179865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187824673344219446489453243 281737010016329169734179865)
  ·
    refine ⟨211302757512246877300634899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281737010016329169734179865 211302757512246877300634899)
    ·
      refine ⟨316954136268370315950952349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211302757512246877300634899 316954136268370315950952349)
      ·
        refine ⟨118857801100638868481607131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316954136268370315950952349 118857801100638868481607131)
        ·
          refine ⟨178286701650958302722410697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118857801100638868481607131 178286701650958302722410697)
          ·
            refine ⟨133715026238218727041808023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178286701650958302722410697 133715026238218727041808023)
            ·
              refine ⟨200572539357328090562712035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133715026238218727041808023 200572539357328090562712035)
              ·
                refine ⟨300858809035992135844068053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200572539357328090562712035 300858809035992135844068053)
                ·
                  refine ⟨7051378336781065683845345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 300858809035992135844068053 7051378336781065683845345)
                  ·
                    refine ⟨5288533752585799262884009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7051378336781065683845345 5288533752585799262884009)
                    ·
                      refine ⟨3966400314439349447163007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288533752585799262884009 3966400314439349447163007)
                      ·
                        rfl

theorem cell23_7724537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_7724537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724537 prefixEnd_7724537 := by exact prefixLift 7724537
  have htrace : WordTrace (prefixWord ++ tailWord_7724537) baseStart_7724537 baseEnd_7724537 := by
    simpa [prefixWord, tailWord_7724537, baseEnd_7724537] using wordTrace_append hprefix tailTrace_7724537
  have hstable : (prefixWord ++ tailWord_7724537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724537).length < 2 ^ (prefixWord ++ tailWord_7724537).sum := by decide
  have hdescent : baseEnd_7724537 < baseStart_7724537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724554 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 3, 2, 2]
def baseStart_7724554 : Nat := 118140960795 + 7724554 * 2 ^ 59
def prefixEnd_7724554 : Nat := 4983230072969 + 3 ^ 40 * 7724554 * 2
def baseEnd_7724554 : Nat := 3966409043610475880650429

theorem tailTrace_7724554 : CollatzResearch.WordTrace tailWord_7724554 prefixEnd_7724554 3966409043610475880650429 := by
  unfold tailWord_7724554
  simp only [CollatzResearch.WordTrace]
  refine ⟨70434407514316895409387179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187825086704845054425032477 70434407514316895409387179)
  ·
    refine ⟨105651611271475343114080769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70434407514316895409387179 105651611271475343114080769)
    ·
      refine ⟨79238708453606507335560577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105651611271475343114080769 79238708453606507335560577)
      ·
        refine ⟨59429031340204880501670433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79238708453606507335560577 59429031340204880501670433)
        ·
          refine ⟨44571773505153660376252825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59429031340204880501670433 44571773505153660376252825)
          ·
            refine ⟨33428830128865245282189619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44571773505153660376252825 33428830128865245282189619)
            ·
              refine ⟨50143245193297867923284429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33428830128865245282189619 50143245193297867923284429)
              ·
                refine ⟨18803716947486700471231661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50143245193297867923284429 18803716947486700471231661)
                ·
                  refine ⟨7051393855307512676711873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18803716947486700471231661 7051393855307512676711873)
                  ·
                    refine ⟨5288545391480634507533905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7051393855307512676711873 5288545391480634507533905)
                    ·
                      refine ⟨3966409043610475880650429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288545391480634507533905 3966409043610475880650429)
                      ·
                        rfl

theorem cell23_7724554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_7724554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724554 prefixEnd_7724554 := by exact prefixLift 7724554
  have htrace : WordTrace (prefixWord ++ tailWord_7724554) baseStart_7724554 baseEnd_7724554 := by
    simpa [prefixWord, tailWord_7724554, baseEnd_7724554] using wordTrace_append hprefix tailTrace_7724554
  have hstable : (prefixWord ++ tailWord_7724554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724554).length < 2 ^ (prefixWord ++ tailWord_7724554).sum := by decide
  have hdescent : baseEnd_7724554 < baseStart_7724554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724577 : List Nat := [1, 2, 3, 2, 2, 4, 2, 7]
def baseStart_7724577 : Nat := 118140960795 + 7724577 * 2 ^ 59
def prefixEnd_7724577 : Nat := 4983230072969 + 3 ^ 40 * 7724577 * 2
def baseEnd_7724577 : Nat := 146904476061686270024549

theorem tailTrace_7724577 : CollatzResearch.WordTrace tailWord_7724577 prefixEnd_7724577 146904476061686270024549 := by
  unfold tailWord_7724577
  simp only [CollatzResearch.WordTrace]
  refine ⟨281738468936184256565635985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187825645957456171043757323 281738468936184256565635985)
  ·
    refine ⟨211303851702138192424226989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281738468936184256565635985 211303851702138192424226989)
    ·
      refine ⟨79238944388301822159085121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211303851702138192424226989 79238944388301822159085121)
      ·
        refine ⟨59429208291226366619313841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79238944388301822159085121 59429208291226366619313841)
        ·
          refine ⟨44571906218419774964485381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59429208291226366619313841 44571906218419774964485381)
          ·
            refine ⟨8357232415953707805841009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44571906218419774964485381 8357232415953707805841009)
            ·
              refine ⟨6267924311965280854380757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8357232415953707805841009 6267924311965280854380757)
              ·
                refine ⟨146904476061686270024549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6267924311965280854380757 146904476061686270024549)
                ·
                  rfl

theorem cell23_7724577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 7].length) (baseStart_7724577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724577 prefixEnd_7724577 := by exact prefixLift 7724577
  have htrace : WordTrace (prefixWord ++ tailWord_7724577) baseStart_7724577 baseEnd_7724577 := by
    simpa [prefixWord, tailWord_7724577, baseEnd_7724577] using wordTrace_append hprefix tailTrace_7724577
  have hstable : (prefixWord ++ tailWord_7724577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724577).length < 2 ^ (prefixWord ++ tailWord_7724577).sum := by decide
  have hdescent : baseEnd_7724577 < baseStart_7724577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724605 : List Nat := [1, 4, 1, 3, 3, 1, 3, 2, 1, 2, 2]
def baseStart_7724605 : Nat := 118140960795 + 7724605 * 2 ^ 59
def prefixEnd_7724605 : Nat := 4983230072969 + 3 ^ 40 * 7724605 * 2
def baseEnd_7724605 : Nat := 3966435231123855181112695

theorem tailTrace_7724605 : CollatzResearch.WordTrace tailWord_7724605 prefixEnd_7724605 3966435231123855181112695 := by
  unfold tailWord_7724605
  simp only [CollatzResearch.WordTrace]
  refine ⟨281739490180082817347655269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187826326786721878231770179 281739490180082817347655269)
  ·
    refine ⟨52826154408765528252685363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281739490180082817347655269 52826154408765528252685363)
    ·
      refine ⟨79239231613148292379028045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52826154408765528252685363 79239231613148292379028045)
      ·
        refine ⟨29714711854930609642135517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79239231613148292379028045 29714711854930609642135517)
        ·
          refine ⟨11143016945598978615800819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29714711854930609642135517 11143016945598978615800819)
          ·
            refine ⟨16714525418398467923701229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11143016945598978615800819 16714525418398467923701229)
            ·
              refine ⟨6267947031899425471387961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16714525418398467923701229 6267947031899425471387961)
              ·
                refine ⟨4700960273924569103540971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6267947031899425471387961 4700960273924569103540971)
                ·
                  refine ⟨7051440410886853655311457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4700960273924569103540971 7051440410886853655311457)
                  ·
                    refine ⟨5288580308165140241483593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7051440410886853655311457 5288580308165140241483593)
                    ·
                      refine ⟨3966435231123855181112695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288580308165140241483593 3966435231123855181112695)
                      ·
                        rfl

theorem cell23_7724605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_7724605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724605 prefixEnd_7724605 := by exact prefixLift 7724605
  have htrace : WordTrace (prefixWord ++ tailWord_7724605) baseStart_7724605 baseEnd_7724605 := by
    simpa [prefixWord, tailWord_7724605, baseEnd_7724605] using wordTrace_append hprefix tailTrace_7724605
  have hstable : (prefixWord ++ tailWord_7724605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724605).length < 2 ^ (prefixWord ++ tailWord_7724605).sum := by decide
  have hdescent : baseEnd_7724605 < baseStart_7724605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724631 : List Nat := [1, 1, 3, 2, 2, 5, 1, 2, 1, 3, 2]
def baseStart_7724631 : Nat := 118140960795 + 7724631 * 2 ^ 59
def prefixEnd_7724631 : Nat := 4983230072969 + 3 ^ 40 * 7724631 * 2
def baseEnd_7724631 : Nat := 3966448581620872079387575

theorem tailTrace_7724631 : CollatzResearch.WordTrace tailWord_7724631 prefixEnd_7724631 3966448581620872079387575 := by
  unfold tailWord_7724631
  simp only [CollatzResearch.WordTrace]
  refine ⟨281740438477988623788101747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187826958985325749192067831 281740438477988623788101747)
  ·
    refine ⟨422610657716982935682152621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281740438477988623788101747 422610657716982935682152621)
    ·
      refine ⟨158478996643868600880807233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422610657716982935682152621 158478996643868600880807233)
      ·
        refine ⟨118859247482901450660605425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158478996643868600880807233 118859247482901450660605425)
        ·
          refine ⟨89144435612176087995454069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118859247482901450660605425 89144435612176087995454069)
          ·
            refine ⟨8357290838641508249573819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89144435612176087995454069 8357290838641508249573819)
            ·
              refine ⟨12535936257962262374360729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8357290838641508249573819 12535936257962262374360729)
              ·
                refine ⟨9401952193471696780770547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12535936257962262374360729 9401952193471696780770547)
                ·
                  refine ⟨14102928290207545171155821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9401952193471696780770547 14102928290207545171155821)
                  ·
                    refine ⟨5288598108827829439183433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14102928290207545171155821 5288598108827829439183433)
                    ·
                      refine ⟨3966448581620872079387575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288598108827829439183433 3966448581620872079387575)
                      ·
                        rfl

theorem cell23_7724631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_7724631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724631 prefixEnd_7724631 := by exact prefixLift 7724631
  have htrace : WordTrace (prefixWord ++ tailWord_7724631) baseStart_7724631 baseEnd_7724631 := by
    simpa [prefixWord, tailWord_7724631, baseEnd_7724631] using wordTrace_append hprefix tailTrace_7724631
  have hstable : (prefixWord ++ tailWord_7724631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724631).length < 2 ^ (prefixWord ++ tailWord_7724631).sum := by decide
  have hdescent : baseEnd_7724631 < baseStart_7724631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724640 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 4]
def baseStart_7724640 : Nat := 118140960795 + 7724640 * 2 ^ 59
def prefixEnd_7724640 : Nat := 4983230072969 + 3 ^ 40 * 7724640 * 2
def baseEnd_7724640 : Nat := 3966453202946762544175033

theorem tailTrace_7724640 : CollatzResearch.WordTrace tailWord_7724640 prefixEnd_7724640 3966453202946762544175033 := by
  unfold tailWord_7724640
  simp only [CollatzResearch.WordTrace]
  refine ⟨140870383367478009162589687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187827177823304012216786249 140870383367478009162589687)
  ·
    refine ⟨211305575051217013743884531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140870383367478009162589687 211305575051217013743884531)
    ·
      refine ⟨316958362576825520615826797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211305575051217013743884531 316958362576825520615826797)
      ·
        refine ⟨118859385966309570230935049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316958362576825520615826797 118859385966309570230935049)
        ·
          refine ⟨89144539474732177673201287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118859385966309570230935049 89144539474732177673201287)
          ·
            refine ⟨133716809212098266509801931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89144539474732177673201287 133716809212098266509801931)
            ·
              refine ⟨200575213818147399764702897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133716809212098266509801931 200575213818147399764702897)
              ·
                refine ⟨150431410363610549823527173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200575213818147399764702897 150431410363610549823527173)
                ·
                  refine ⟨28205889443176978091911345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150431410363610549823527173 28205889443176978091911345)
                  ·
                    refine ⟨21154417082382733568933509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28205889443176978091911345 21154417082382733568933509)
                    ·
                      refine ⟨3966453202946762544175033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21154417082382733568933509 3966453202946762544175033)
                      ·
                        rfl

theorem cell23_7724640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_7724640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724640 prefixEnd_7724640 := by exact prefixLift 7724640
  have htrace : WordTrace (prefixWord ++ tailWord_7724640) baseStart_7724640 baseEnd_7724640 := by
    simpa [prefixWord, tailWord_7724640, baseEnd_7724640] using wordTrace_append hprefix tailTrace_7724640
  have hstable : (prefixWord ++ tailWord_7724640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724640).length < 2 ^ (prefixWord ++ tailWord_7724640).sum := by decide
  have hdescent : baseEnd_7724640 < baseStart_7724640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724644 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 1, 4, 2]
def baseStart_7724644 : Nat := 118140960795 + 7724644 * 2 ^ 59
def prefixEnd_7724644 : Nat := 4983230072969 + 3 ^ 40 * 7724644 * 2
def baseEnd_7724644 : Nat := 3966455256869380528525015

theorem tailTrace_7724644 : CollatzResearch.WordTrace tailWord_7724644 prefixEnd_7724644 3966455256869380528525015 := by
  unfold tailWord_7724644
  simp only [CollatzResearch.WordTrace]
  refine ⟨140870456313470763504162493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187827275084627684672216657 140870456313470763504162493)
  ·
    refine ⟨52826421117551536314060935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140870456313470763504162493 52826421117551536314060935)
    ·
      refine ⟨79239631676327304471091403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52826421117551536314060935 79239631676327304471091403)
      ·
        refine ⟨118859447514490956706637105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79239631676327304471091403 118859447514490956706637105)
        ·
          refine ⟨89144585635868217529977829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118859447514490956706637105 89144585635868217529977829)
          ·
            refine ⟨16714609806725290786870843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89144585635868217529977829 16714609806725290786870843)
            ·
              refine ⟨25071914710087936180306265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16714609806725290786870843 25071914710087936180306265)
              ·
                refine ⟨18803936032565952135229699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25071914710087936180306265 18803936032565952135229699)
                ·
                  refine ⟨28205904048848928202844549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18803936032565952135229699 28205904048848928202844549)
                  ·
                    refine ⟨5288607009159174038033353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28205904048848928202844549 5288607009159174038033353)
                    ·
                      refine ⟨3966455256869380528525015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288607009159174038033353 3966455256869380528525015)
                      ·
                        rfl

theorem cell23_7724644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_7724644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724644 prefixEnd_7724644 := by exact prefixLift 7724644
  have htrace : WordTrace (prefixWord ++ tailWord_7724644) baseStart_7724644 baseEnd_7724644 := by
    simpa [prefixWord, tailWord_7724644, baseEnd_7724644] using wordTrace_append hprefix tailTrace_7724644
  have hstable : (prefixWord ++ tailWord_7724644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724644).length < 2 ^ (prefixWord ++ tailWord_7724644).sum := by decide
  have hdescent : baseEnd_7724644 < baseStart_7724644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724648 : List Nat := [2, 1, 4, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_7724648 : Nat := 118140960795 + 7724648 * 2 ^ 59
def prefixEnd_7724648 : Nat := 4983230072969 + 3 ^ 40 * 7724648 * 2
def baseEnd_7724648 : Nat := 3966457310791998512874997

theorem tailTrace_7724648 : CollatzResearch.WordTrace tailWord_7724648 prefixEnd_7724648 3966457310791998512874997 := by
  unfold tailWord_7724648
  simp only [CollatzResearch.WordTrace]
  refine ⟨140870529259463517845735299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187827372345951357127647065 140870529259463517845735299)
  ·
    refine ⟨211305793889195276768602949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140870529259463517845735299 211305793889195276768602949)
    ·
      refine ⟨39619836354224114394113053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211305793889195276768602949 39619836354224114394113053)
      ·
        refine ⟨14857438632834042897792395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39619836354224114394113053 14857438632834042897792395)
        ·
          refine ⟨22286157949251064346688593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14857438632834042897792395 22286157949251064346688593)
          ·
            refine ⟨16714618461938298260016445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22286157949251064346688593 16714618461938298260016445)
            ·
              refine ⟨6267981923226861847506167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16714618461938298260016445 6267981923226861847506167)
              ·
                refine ⟨9401972884840292771259251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6267981923226861847506167 9401972884840292771259251)
                ·
                  refine ⟨14102959327260439156888877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9401972884840292771259251 14102959327260439156888877)
                  ·
                    refine ⟨5288609747722664683833329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14102959327260439156888877 5288609747722664683833329)
                    ·
                      refine ⟨3966457310791998512874997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288609747722664683833329 3966457310791998512874997)
                      ·
                        rfl

theorem cell23_7724648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_7724648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724648 prefixEnd_7724648 := by exact prefixLift 7724648
  have htrace : WordTrace (prefixWord ++ tailWord_7724648) baseStart_7724648 baseEnd_7724648 := by
    simpa [prefixWord, tailWord_7724648, baseEnd_7724648] using wordTrace_append hprefix tailTrace_7724648
  have hstable : (prefixWord ++ tailWord_7724648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724648).length < 2 ^ (prefixWord ++ tailWord_7724648).sum := by decide
  have hdescent : baseEnd_7724648 < baseStart_7724648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724667 : List Nat := [1, 1, 1, 1, 1, 4, 5, 4, 5]
def baseStart_7724667 : Nat := 118140960795 + 7724667 * 2 ^ 59
def prefixEnd_7724667 : Nat := 4983230072969 + 3 ^ 40 * 7724667 * 2
def baseEnd_7724667 : Nat := 440718562991603770948601

theorem tailTrace_7724667 : CollatzResearch.WordTrace tailWord_7724667 prefixEnd_7724667 440718562991603770948601 := by
  unfold tailWord_7724667
  simp only [CollatzResearch.WordTrace]
  refine ⟨281741751505858201936412255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187827834337238801290941503 281741751505858201936412255)
  ·
    refine ⟨422612627258787302904618383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281741751505858201936412255 422612627258787302904618383)
    ·
      refine ⟨633918940888180954356927575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422612627258787302904618383 633918940888180954356927575)
      ·
        refine ⟨950878411332271431535391363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633918940888180954356927575 950878411332271431535391363)
        ·
          refine ⟨1426317616998407147303087045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950878411332271431535391363 1426317616998407147303087045)
          ·
            refine ⟨267434553187201340119328821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1426317616998407147303087045 267434553187201340119328821)
            ·
              refine ⟨25071989361300125636187077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267434553187201340119328821 25071989361300125636187077)
              ·
                refine ⟨4700998005243773556785077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25071989361300125636187077 4700998005243773556785077)
                ·
                  refine ⟨440718562991603770948601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4700998005243773556785077 440718562991603770948601)
                  ·
                    rfl

theorem cell23_7724667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 5].length) (baseStart_7724667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724667 prefixEnd_7724667 := by exact prefixLift 7724667
  have htrace : WordTrace (prefixWord ++ tailWord_7724667) baseStart_7724667 baseEnd_7724667 := by
    simpa [prefixWord, tailWord_7724667, baseEnd_7724667] using wordTrace_append hprefix tailTrace_7724667
  have hstable : (prefixWord ++ tailWord_7724667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724667).length < 2 ^ (prefixWord ++ tailWord_7724667).sum := by decide
  have hdescent : baseEnd_7724667 < baseStart_7724667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724677 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 2, 3, 3]
def baseStart_7724677 : Nat := 118140960795 + 7724677 * 2 ^ 59
def prefixEnd_7724677 : Nat := 4983230072969 + 3 ^ 40 * 7724677 * 2
def baseEnd_7724677 : Nat := 3966472201730978899412363

theorem tailTrace_7724677 : CollatzResearch.WordTrace tailWord_7724677 prefixEnd_7724677 3966472201730978899412363 := by
  unfold tailWord_7724677
  simp only [CollatzResearch.WordTrace]
  refine ⟨281742116235821973644276285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187828077490547982429517523 281742116235821973644276285)
  ·
    refine ⟨105653293588433240116603607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281742116235821973644276285 105653293588433240116603607)
    ·
      refine ⟨158479940382649860174905411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105653293588433240116603607 158479940382649860174905411)
      ·
        refine ⟨237719910573974790262358117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158479940382649860174905411 237719910573974790262358117)
        ·
          refine ⟨44572483232620273174192147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237719910573974790262358117 44572483232620273174192147)
          ·
            refine ⟨66858724848930409761288221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44572483232620273174192147 66858724848930409761288221)
            ·
              refine ⟨25072021818348903660483083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66858724848930409761288221 25072021818348903660483083)
              ·
                refine ⟨37608032727523355490724625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25072021818348903660483083 37608032727523355490724625)
                ·
                  refine ⟨28206024545642516618043469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37608032727523355490724625 28206024545642516618043469)
                  ·
                    refine ⟨10577259204615943731766301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28206024545642516618043469 10577259204615943731766301)
                    ·
                      refine ⟨3966472201730978899412363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10577259204615943731766301 3966472201730978899412363)
                      ·
                        rfl

theorem cell23_7724677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_7724677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724677 prefixEnd_7724677 := by exact prefixLift 7724677
  have htrace : WordTrace (prefixWord ++ tailWord_7724677) baseStart_7724677 baseEnd_7724677 := by
    simpa [prefixWord, tailWord_7724677, baseEnd_7724677] using wordTrace_append hprefix tailTrace_7724677
  have hstable : (prefixWord ++ tailWord_7724677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724677).length < 2 ^ (prefixWord ++ tailWord_7724677).sum := by decide
  have hdescent : baseEnd_7724677 < baseStart_7724677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724720 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 5]
def baseStart_7724720 : Nat := 118140960795 + 7724720 * 2 ^ 59
def prefixEnd_7724720 : Nat := 4983230072969 + 3 ^ 40 * 7724720 * 2
def baseEnd_7724720 : Nat := 3966494281399122231174665

theorem tailTrace_7724720 : CollatzResearch.WordTrace tailWord_7724720 prefixEnd_7724720 3966494281399122231174665 := by
  unfold tailWord_7724720
  simp only [CollatzResearch.WordTrace]
  refine ⟨140871842287333095994045807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187829123049777461325394409 140871842287333095994045807)
  ·
    refine ⟨211307763430999643991068711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140871842287333095994045807 211307763430999643991068711)
    ·
      refine ⟨316961645146499465986603067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211307763430999643991068711 316961645146499465986603067)
      ·
        refine ⟨475442467719749198979904601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316961645146499465986603067 475442467719749198979904601)
        ·
          refine ⟨356581850789811899234928451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475442467719749198979904601 356581850789811899234928451)
          ·
            refine ⟨534872776184717848852392677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356581850789811899234928451 534872776184717848852392677)
            ·
              refine ⟨100288645534634596659823627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 534872776184717848852392677 100288645534634596659823627)
              ·
                refine ⟨150432968301951894989735441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100288645534634596659823627 150432968301951894989735441)
                ·
                  refine ⟨112824726226463921242301581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150432968301951894989735441 112824726226463921242301581)
                  ·
                    refine ⟨42309272334923970465863093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112824726226463921242301581 42309272334923970465863093)
                    ·
                      refine ⟨3966494281399122231174665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42309272334923970465863093 3966494281399122231174665)
                      ·
                        rfl

theorem cell23_7724720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_7724720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724720 prefixEnd_7724720 := by exact prefixLift 7724720
  have htrace : WordTrace (prefixWord ++ tailWord_7724720) baseStart_7724720 baseEnd_7724720 := by
    simpa [prefixWord, tailWord_7724720, baseEnd_7724720] using wordTrace_append hprefix tailTrace_7724720
  have hstable : (prefixWord ++ tailWord_7724720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724720).length < 2 ^ (prefixWord ++ tailWord_7724720).sum := by decide
  have hdescent : baseEnd_7724720 < baseStart_7724720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724754 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_7724754 : Nat := 118140960795 + 7724754 * 2 ^ 59
def prefixEnd_7724754 : Nat := 4983230072969 + 3 ^ 40 * 7724754 * 2
def baseEnd_7724754 : Nat := 3966511739741375098149509

theorem tailTrace_7724754 : CollatzResearch.WordTrace tailWord_7724754 prefixEnd_7724754 3966511739741375098149509 := by
  unfold tailWord_7724754
  simp only [CollatzResearch.WordTrace]
  refine ⟨70436231164135753948707329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187829949771028677196552877 70436231164135753948707329)
  ·
    refine ⟨52827173373101815461530497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70436231164135753948707329 52827173373101815461530497)
    ·
      refine ⟨39620380029826361596147873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52827173373101815461530497 39620380029826361596147873)
      ·
        refine ⟨29715285022369771197110905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39620380029826361596147873 29715285022369771197110905)
        ·
          refine ⟨22286463766777328397833179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29715285022369771197110905 22286463766777328397833179)
          ·
            refine ⟨33429695650165992596749769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22286463766777328397833179 33429695650165992596749769)
            ·
              refine ⟨25072271737624494447562327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33429695650165992596749769 25072271737624494447562327)
              ·
                refine ⟨37608407606436741671343491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25072271737624494447562327 37608407606436741671343491)
                ·
                  refine ⟨56412611409655112507015237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37608407606436741671343491 56412611409655112507015237)
                  ·
                    refine ⟨10577364639310333595065357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56412611409655112507015237 10577364639310333595065357)
                    ·
                      refine ⟨3966511739741375098149509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10577364639310333595065357 3966511739741375098149509)
                      ·
                        rfl

theorem cell23_7724754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_7724754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724754 prefixEnd_7724754 := by exact prefixLift 7724754
  have htrace : WordTrace (prefixWord ++ tailWord_7724754) baseStart_7724754 baseEnd_7724754 := by
    simpa [prefixWord, tailWord_7724754, baseEnd_7724754] using wordTrace_append hprefix tailTrace_7724754
  have hstable : (prefixWord ++ tailWord_7724754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724754).length < 2 ^ (prefixWord ++ tailWord_7724754).sum := by decide
  have hdescent : baseEnd_7724754 < baseStart_7724754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724761 : List Nat := [1, 2, 1, 2, 3, 3, 3, 3, 1, 4]
def baseStart_7724761 : Nat := 118140960795 + 7724761 * 2 ^ 59
def prefixEnd_7724761 : Nat := 4983230072969 + 3 ^ 40 * 7724761 * 2
def baseEnd_7724761 : Nat := 1322171778035318856920659

theorem tailTrace_7724761 : CollatzResearch.WordTrace tailWord_7724761 prefixEnd_7724761 1322171778035318856920659 := by
  unfold tailWord_7724761
  simp only [CollatzResearch.WordTrace]
  refine ⟨281745179967517655990334137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187830119978345103993556091 281745179967517655990334137)
  ·
    refine ⟨211308884975638241992750603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281745179967517655990334137 211308884975638241992750603)
    ·
      refine ⟨316963327463457362989125905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211308884975638241992750603 316963327463457362989125905)
      ·
        refine ⟨237722495597593022241844429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316963327463457362989125905 237722495597593022241844429)
        ·
          refine ⟨89145935849097383340691661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237722495597593022241844429 89145935849097383340691661)
          ·
            refine ⟨33429725943411518752759373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89145935849097383340691661 33429725943411518752759373)
            ·
              refine ⟨12536147228779319532284765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33429725943411518752759373 12536147228779319532284765)
              ·
                refine ⟨4701055210792244824606787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12536147228779319532284765 4701055210792244824606787)
                ·
                  refine ⟨7051582816188367236910181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4701055210792244824606787 7051582816188367236910181)
                  ·
                    refine ⟨1322171778035318856920659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7051582816188367236910181 1322171778035318856920659)
                    ·
                      rfl

theorem cell23_7724761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 1, 4].length) (baseStart_7724761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724761 prefixEnd_7724761 := by exact prefixLift 7724761
  have htrace : WordTrace (prefixWord ++ tailWord_7724761) baseStart_7724761 baseEnd_7724761 := by
    simpa [prefixWord, tailWord_7724761, baseEnd_7724761] using wordTrace_append hprefix tailTrace_7724761
  have hstable : (prefixWord ++ tailWord_7724761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724761).length < 2 ^ (prefixWord ++ tailWord_7724761).sum := by decide
  have hdescent : baseEnd_7724761 < baseStart_7724761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724771 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 3]
def baseStart_7724771 : Nat := 118140960795 + 7724771 * 2 ^ 59
def prefixEnd_7724771 : Nat := 4983230072969 + 3 ^ 40 * 7724771 * 2
def baseEnd_7724771 : Nat := 3966520468912501531636931

theorem tailTrace_7724771 : CollatzResearch.WordTrace tailWord_7724771 prefixEnd_7724771 3966520468912501531636931 := by
  unfold tailWord_7724771
  simp only [CollatzResearch.WordTrace]
  refine ⟨281745544697481427698198167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187830363131654285132132111 281745544697481427698198167)
  ·
    refine ⟨422618317046222141547297251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281745544697481427698198167 422618317046222141547297251)
    ·
      refine ⟨633927475569333212320945877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422618317046222141547297251 633927475569333212320945877)
      ·
        refine ⟨14857675208656247163772169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 633927475569333212320945877 14857675208656247163772169)
        ·
          refine ⟨11143256406492185372829127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14857675208656247163772169 11143256406492185372829127)
          ·
            refine ⟨16714884609738278059243691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11143256406492185372829127 16714884609738278059243691)
            ·
              refine ⟨25072326914607417088865537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16714884609738278059243691 25072326914607417088865537)
              ·
                refine ⟨18804245185955562816649153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25072326914607417088865537 18804245185955562816649153)
                ·
                  refine ⟨14103183889466672112486865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18804245185955562816649153 14103183889466672112486865)
                  ·
                    refine ⟨10577387917100004084365149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14103183889466672112486865 10577387917100004084365149)
                    ·
                      refine ⟨3966520468912501531636931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10577387917100004084365149 3966520468912501531636931)
                      ·
                        rfl

theorem cell23_7724771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_7724771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724771 prefixEnd_7724771 := by exact prefixLift 7724771
  have htrace : WordTrace (prefixWord ++ tailWord_7724771) baseStart_7724771 baseEnd_7724771 := by
    simpa [prefixWord, tailWord_7724771, baseEnd_7724771] using wordTrace_append hprefix tailTrace_7724771
  have hstable : (prefixWord ++ tailWord_7724771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724771).length < 2 ^ (prefixWord ++ tailWord_7724771).sum := by decide
  have hdescent : baseEnd_7724771 < baseStart_7724771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724784 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 3, 1, 3]
def baseStart_7724784 : Nat := 118140960795 + 7724784 * 2 ^ 59
def prefixEnd_7724784 : Nat := 4983230072969 + 3 ^ 40 * 7724784 * 2
def baseEnd_7724784 : Nat := 3966527144161009980774371

theorem tailTrace_7724784 : CollatzResearch.WordTrace tailWord_7724784 prefixEnd_7724784 3966527144161009980774371 := by
  unfold tailWord_7724784
  simp only [CollatzResearch.WordTrace]
  refine ⟨140873009423217165459210703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187830679230956220612280937 140873009423217165459210703)
  ·
    refine ⟨211309514134825748188816055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140873009423217165459210703 211309514134825748188816055)
    ·
      refine ⟨316964271202238622283224083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211309514134825748188816055 316964271202238622283224083)
      ·
        refine ⟨475446406803357933424836125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316964271202238622283224083 475446406803357933424836125)
        ·
          refine ⟨178292402551259225034313547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475446406803357933424836125 178292402551259225034313547)
          ·
            refine ⟨267438603826888837551470321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178292402551259225034313547 267438603826888837551470321)
            ·
              refine ⟨200578952870166628163602741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267438603826888837551470321 200578952870166628163602741)
              ·
                refine ⟨18804276831578121390337757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200578952870166628163602741 18804276831578121390337757)
                ·
                  refine ⟨7051603811841795521376659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18804276831578121390337757 7051603811841795521376659)
                  ·
                    refine ⟨10577405717762693282064989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7051603811841795521376659 10577405717762693282064989)
                    ·
                      refine ⟨3966527144161009980774371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10577405717762693282064989 3966527144161009980774371)
                      ·
                        rfl

theorem cell23_7724784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 3, 1, 3].length) (baseStart_7724784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724784 prefixEnd_7724784 := by exact prefixLift 7724784
  have htrace : WordTrace (prefixWord ++ tailWord_7724784) baseStart_7724784 baseEnd_7724784 := by
    simpa [prefixWord, tailWord_7724784, baseEnd_7724784] using wordTrace_append hprefix tailTrace_7724784
  have hstable : (prefixWord ++ tailWord_7724784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724784).length < 2 ^ (prefixWord ++ tailWord_7724784).sum := by decide
  have hdescent : baseEnd_7724784 < baseStart_7724784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724794 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2]
def baseStart_7724794 : Nat := 118140960795 + 7724794 * 2 ^ 59
def prefixEnd_7724794 : Nat := 4983230072969 + 3 ^ 40 * 7724794 * 2
def baseEnd_7724794 : Nat := 3966532278967554941649325

theorem tailTrace_7724794 : CollatzResearch.WordTrace tailWord_7724794 prefixEnd_7724794 3966532278967554941649325 := by
  unfold tailWord_7724794
  simp only [CollatzResearch.WordTrace]
  refine ⟨70436595894099525656571359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187830922384265401750856957 70436595894099525656571359)
  ·
    refine ⟨105654893841149288484857039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70436595894099525656571359 105654893841149288484857039)
    ·
      refine ⟨158482340761723932727285559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105654893841149288484857039 158482340761723932727285559)
      ·
        refine ⟨237723511142585899090928339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158482340761723932727285559 237723511142585899090928339)
        ·
          refine ⟨356585266713878848636392509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237723511142585899090928339 356585266713878848636392509)
          ·
            refine ⟨133719475017704568238647191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356585266713878848636392509 133719475017704568238647191)
            ·
              refine ⟨200579212526556852357970787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133719475017704568238647191 200579212526556852357970787)
              ·
                refine ⟨300868818789835278536956181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200579212526556852357970787 300868818789835278536956181)
                ·
                  refine ⟨14103225880773528681419821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 300868818789835278536956181 14103225880773528681419821)
                  ·
                    refine ⟨5288709705290073255532433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14103225880773528681419821 5288709705290073255532433)
                    ·
                      refine ⟨3966532278967554941649325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288709705290073255532433 3966532278967554941649325)
                      ·
                        rfl

theorem cell23_7724794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2].length) (baseStart_7724794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724794 prefixEnd_7724794 := by exact prefixLift 7724794
  have htrace : WordTrace (prefixWord ++ tailWord_7724794) baseStart_7724794 baseEnd_7724794 := by
    simpa [prefixWord, tailWord_7724794, baseEnd_7724794] using wordTrace_append hprefix tailTrace_7724794
  have hstable : (prefixWord ++ tailWord_7724794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724794).length < 2 ^ (prefixWord ++ tailWord_7724794).sum := by decide
  have hdescent : baseEnd_7724794 < baseStart_7724794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724804 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_7724804 : Nat := 118140960795 + 7724804 * 2 ^ 59
def prefixEnd_7724804 : Nat := 4983230072969 + 3 ^ 40 * 7724804 * 2
def baseEnd_7724804 : Nat := 1322179137924699967508093

theorem tailTrace_7724804 : CollatzResearch.WordTrace tailWord_7724804 prefixEnd_7724804 1322179137924699967508093 := by
  unfold tailWord_7724804
  simp only [CollatzResearch.WordTrace]
  refine ⟨140873374153180937167074733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187831165537574582889432977 140873374153180937167074733)
  ·
    refine ⟨52827515307442851437653025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140873374153180937167074733 52827515307442851437653025)
    ·
      refine ⟨39620636480582138578239769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52827515307442851437653025 39620636480582138578239769)
      ·
        refine ⟨29715477360436603933679827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39620636480582138578239769 29715477360436603933679827)
        ·
          refine ⟨44573216040654905900519741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29715477360436603933679827 44573216040654905900519741)
          ·
            refine ⟨16714956015245589712694903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44573216040654905900519741 16714956015245589712694903)
            ·
              refine ⟨25072434022868384569042355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16714956015245589712694903 25072434022868384569042355)
              ·
                refine ⟨37608651034302576853563533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25072434022868384569042355 37608651034302576853563533)
                ·
                  refine ⟨14103244137863466320086325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37608651034302576853563533 14103244137863466320086325)
                  ·
                    refine ⟨1322179137924699967508093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14103244137863466320086325 1322179137924699967508093)
                    ·
                      rfl

theorem cell23_7724804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_7724804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724804 prefixEnd_7724804 := by exact prefixLift 7724804
  have htrace : WordTrace (prefixWord ++ tailWord_7724804) baseStart_7724804 baseEnd_7724804 := by
    simpa [prefixWord, tailWord_7724804, baseEnd_7724804] using wordTrace_append hprefix tailTrace_7724804
  have hstable : (prefixWord ++ tailWord_7724804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724804).length < 2 ^ (prefixWord ++ tailWord_7724804).sum := by decide
  have hdescent : baseEnd_7724804 < baseStart_7724804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724821 : List Nat := [1, 3, 2, 1, 2, 4, 3, 1, 1, 5]
def baseStart_7724821 : Nat := 118140960795 + 7724821 * 2 ^ 59
def prefixEnd_7724821 : Nat := 4983230072969 + 3 ^ 40 * 7724821 * 2
def baseEnd_7724821 : Nat := 1322182047648408778670567

theorem tailTrace_7724821 : CollatzResearch.WordTrace tailWord_7724821 prefixEnd_7724821 1322182047648408778670567 := by
  unfold tailWord_7724821
  simp only [CollatzResearch.WordTrace]
  refine ⟨281747368347300286237518317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187831578898200190825012211 281747368347300286237518317)
  ·
    refine ⟨105655263130237607339069369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281747368347300286237518317 105655263130237607339069369)
    ·
      refine ⟨79241447347678205504302027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105655263130237607339069369 79241447347678205504302027)
      ·
        refine ⟨118862171021517308256453041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79241447347678205504302027 118862171021517308256453041)
        ·
          refine ⟨89146628266137981192339781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118862171021517308256453041 89146628266137981192339781)
          ·
            refine ⟨16714992799900871473563709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89146628266137981192339781 16714992799900871473563709)
            ·
              refine ⟨6268122299962826802586391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16714992799900871473563709 6268122299962826802586391)
              ·
                refine ⟨9402183449944240203879587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268122299962826802586391 9402183449944240203879587)
                ·
                  refine ⟨14103275174916360305819381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9402183449944240203879587 14103275174916360305819381)
                  ·
                    refine ⟨1322182047648408778670567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14103275174916360305819381 1322182047648408778670567)
                    ·
                      rfl

theorem cell23_7724821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_7724821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724821 prefixEnd_7724821 := by exact prefixLift 7724821
  have htrace : WordTrace (prefixWord ++ tailWord_7724821) baseStart_7724821 baseEnd_7724821 := by
    simpa [prefixWord, tailWord_7724821, baseEnd_7724821] using wordTrace_append hprefix tailTrace_7724821
  have hstable : (prefixWord ++ tailWord_7724821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724821).length < 2 ^ (prefixWord ++ tailWord_7724821).sum := by decide
  have hdescent : baseEnd_7724821 < baseStart_7724821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724824 : List Nat := [2, 1, 2, 3, 1, 1, 2, 5, 1, 1, 4]
def baseStart_7724824 : Nat := 118140960795 + 7724824 * 2 ^ 59
def prefixEnd_7724824 : Nat := 4983230072969 + 3 ^ 40 * 7724824 * 2
def baseEnd_7724824 : Nat := 3966547683387189824274187

theorem tailTrace_7724824 : CollatzResearch.WordTrace tailWord_7724824 prefixEnd_7724824 3966547683387189824274187 := by
  unfold tailWord_7724824
  simp only [CollatzResearch.WordTrace]
  refine ⟨140873738883144708874938763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187831651844192945166585017 140873738883144708874938763)
  ·
    refine ⟨211310608324717063312408145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140873738883144708874938763 211310608324717063312408145)
    ·
      refine ⟨158482956243537797484306109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211310608324717063312408145 158482956243537797484306109)
      ·
        refine ⟨59431108591326674056614791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158482956243537797484306109 59431108591326674056614791)
        ·
          refine ⟨89146662886990011084922187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59431108591326674056614791 89146662886990011084922187)
          ·
            refine ⟨133719994330485016627383281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89146662886990011084922187 133719994330485016627383281)
            ·
              refine ⟨100289995747863762470537461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133719994330485016627383281 100289995747863762470537461)
              ·
                refine ⟨9402187101362227731612887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100289995747863762470537461 9402187101362227731612887)
                ·
                  refine ⟨14103280652043341597419331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9402187101362227731612887 14103280652043341597419331)
                  ·
                    refine ⟨21154920978065012396128997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14103280652043341597419331 21154920978065012396128997)
                    ·
                      refine ⟨3966547683387189824274187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21154920978065012396128997 3966547683387189824274187)
                      ·
                        rfl

theorem cell23_7724824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_7724824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724824 prefixEnd_7724824 := by exact prefixLift 7724824
  have htrace : WordTrace (prefixWord ++ tailWord_7724824) baseStart_7724824 baseEnd_7724824 := by
    simpa [prefixWord, tailWord_7724824, baseEnd_7724824] using wordTrace_append hprefix tailTrace_7724824
  have hstable : (prefixWord ++ tailWord_7724824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724824).length < 2 ^ (prefixWord ++ tailWord_7724824).sum := by decide
  have hdescent : baseEnd_7724824 < baseStart_7724824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724844 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 3]
def baseStart_7724844 : Nat := 118140960795 + 7724844 * 2 ^ 59
def prefixEnd_7724844 : Nat := 4983230072969 + 3 ^ 40 * 7724844 * 2
def baseEnd_7724844 : Nat := 3966557953000279746024095

theorem tailTrace_7724844 : CollatzResearch.WordTrace tailWord_7724844 prefixEnd_7724844 3966557953000279746024095 := by
  unfold tailWord_7724844
  simp only [CollatzResearch.WordTrace]
  refine ⟨140874103613108480582802793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187832138150811307443737057 140874103613108480582802793)
  ·
    refine ⟨105655577709831360437102095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140874103613108480582802793 105655577709831360437102095)
    ·
      refine ⟨158483366564747040655653143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105655577709831360437102095 158483366564747040655653143)
      ·
        refine ⟨237725049847120560983479715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158483366564747040655653143 237725049847120560983479715)
        ·
          refine ⟨356587574770680841475219573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237725049847120560983479715 356587574770680841475219573)
          ·
            refine ⟨33430085134751328888301835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 356587574770680841475219573 33430085134751328888301835)
            ·
              refine ⟨50145127702126993332452753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33430085134751328888301835 50145127702126993332452753)
              ·
                refine ⟨37608845776595244999339565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50145127702126993332452753 37608845776595244999339565)
                ·
                  refine ⟨14103317166223216874752337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37608845776595244999339565 14103317166223216874752337)
                  ·
                    refine ⟨10577487874667412656064253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14103317166223216874752337 10577487874667412656064253)
                    ·
                      refine ⟨3966557953000279746024095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10577487874667412656064253 3966557953000279746024095)
                      ·
                        rfl

theorem cell23_7724844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_7724844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724844 prefixEnd_7724844 := by exact prefixLift 7724844
  have htrace : WordTrace (prefixWord ++ tailWord_7724844) baseStart_7724844 baseEnd_7724844 := by
    simpa [prefixWord, tailWord_7724844, baseEnd_7724844] using wordTrace_append hprefix tailTrace_7724844
  have hstable : (prefixWord ++ tailWord_7724844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724844).length < 2 ^ (prefixWord ++ tailWord_7724844).sum := by decide
  have hdescent : baseEnd_7724844 < baseStart_7724844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724858 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2]
def baseStart_7724858 : Nat := 118140960795 + 7724858 * 2 ^ 59
def prefixEnd_7724858 : Nat := 4983230072969 + 3 ^ 40 * 7724858 * 2
def baseEnd_7724858 : Nat := 3966565141729442691249031

theorem tailTrace_7724858 : CollatzResearch.WordTrace tailWord_7724858 prefixEnd_7724858 3966565141729442691249031 := by
  unfold tailWord_7724858
  simp only [CollatzResearch.WordTrace]
  refine ⟨70437179462041560389153807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187832478565444161037743485 70437179462041560389153807)
  ·
    refine ⟨105655769193062340583730711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70437179462041560389153807 105655769193062340583730711)
    ·
      refine ⟨158483653789593510875596067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105655769193062340583730711 158483653789593510875596067)
      ·
        refine ⟨237725480684390266313394101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158483653789593510875596067 237725480684390266313394101)
        ·
          refine ⟨22286763814161587466880697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237725480684390266313394101 22286763814161587466880697)
          ·
            refine ⟨16715072860621190600160523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22286763814161587466880697 16715072860621190600160523)
            ·
              refine ⟨25072609290931785900240785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16715072860621190600160523 25072609290931785900240785)
              ·
                refine ⟨18804456968198839425180589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25072609290931785900240785 18804456968198839425180589)
                ·
                  refine ⟨7051671363074564784442721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18804456968198839425180589 7051671363074564784442721)
                  ·
                    refine ⟨5288753522305923588332041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7051671363074564784442721 5288753522305923588332041)
                    ·
                      refine ⟨3966565141729442691249031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288753522305923588332041 3966565141729442691249031)
                      ·
                        rfl

theorem cell23_7724858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2].length) (baseStart_7724858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724858 prefixEnd_7724858 := by exact prefixLift 7724858
  have htrace : WordTrace (prefixWord ++ tailWord_7724858) baseStart_7724858 baseEnd_7724858 := by
    simpa [prefixWord, tailWord_7724858, baseEnd_7724858] using wordTrace_append hprefix tailTrace_7724858
  have hstable : (prefixWord ++ tailWord_7724858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724858).length < 2 ^ (prefixWord ++ tailWord_7724858).sum := by decide
  have hdescent : baseEnd_7724858 < baseStart_7724858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724861 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_7724861 : Nat := 118140960795 + 7724861 * 2 ^ 59
def prefixEnd_7724861 : Nat := 4983230072969 + 3 ^ 40 * 7724861 * 2
def baseEnd_7724861 : Nat := 3966566682171406179511517

theorem tailTrace_7724861 : CollatzResearch.WordTrace tailWord_7724861 prefixEnd_7724861 3966566682171406179511517 := by
  unfold tailWord_7724861
  simp only [CollatzResearch.WordTrace]
  refine ⟨281748827267155373068974437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187832551511436915379316291 281748827267155373068974437)
  ·
    refine ⟨52827905112591632450432707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281748827267155373068974437 52827905112591632450432707)
    ·
      refine ⟨79241857668887448675649061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52827905112591632450432707 79241857668887448675649061)
      ·
        refine ⟨14857848312916396626684199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79241857668887448675649061 14857848312916396626684199)
        ·
          refine ⟨22286772469374594940026299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14857848312916396626684199 22286772469374594940026299)
          ·
            refine ⟨33430158704061892410039449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22286772469374594940026299 33430158704061892410039449)
            ·
              refine ⟨25072619028046419307529587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33430158704061892410039449 25072619028046419307529587)
              ·
                refine ⟨37608928542069628961294381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25072619028046419307529587 37608928542069628961294381)
                ·
                  refine ⟨14103348203276110860485393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37608928542069628961294381 14103348203276110860485393)
                  ·
                    refine ⟨10577511152457083145364045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14103348203276110860485393 10577511152457083145364045)
                    ·
                      refine ⟨3966566682171406179511517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10577511152457083145364045 3966566682171406179511517)
                      ·
                        rfl

theorem cell23_7724861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_7724861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724861 prefixEnd_7724861 := by exact prefixLift 7724861
  have htrace : WordTrace (prefixWord ++ tailWord_7724861) baseStart_7724861 baseEnd_7724861 := by
    simpa [prefixWord, tailWord_7724861, baseEnd_7724861] using wordTrace_append hprefix tailTrace_7724861
  have hstable : (prefixWord ++ tailWord_7724861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724861).length < 2 ^ (prefixWord ++ tailWord_7724861).sum := by decide
  have hdescent : baseEnd_7724861 < baseStart_7724861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7724874 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_7724874 : Nat := 118140960795 + 7724874 * 2 ^ 59
def prefixEnd_7724874 : Nat := 4983230072969 + 3 ^ 40 * 7724874 * 2
def baseEnd_7724874 : Nat := 3966573357419914628648957

theorem tailTrace_7724874 : CollatzResearch.WordTrace tailWord_7724874 prefixEnd_7724874 3966573357419914628648957 := by
  unfold tailWord_7724874
  simp only [CollatzResearch.WordTrace]
  refine ⟨70437325354027069072299419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187832867610738850859465117 70437325354027069072299419)
  ·
    refine ⟨105655988031040603608449129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70437325354027069072299419 105655988031040603608449129)
    ·
      refine ⟨79241991023280452706336847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105655988031040603608449129 79241991023280452706336847)
      ·
        refine ⟨118862986534920679059505271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79241991023280452706336847 118862986534920679059505271)
        ·
          refine ⟨178294479802381018589257907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118862986534920679059505271 178294479802381018589257907)
          ·
            refine ⟨267441719703571527883886861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178294479802381018589257907 267441719703571527883886861)
            ·
              refine ⟨100290644888839322956457573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267441719703571527883886861 100290644888839322956457573)
              ·
                refine ⟨18804495916657373054335795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100290644888839322956457573 18804495916657373054335795)
                ·
                  refine ⟨28206743874986059581503693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18804495916657373054335795 28206743874986059581503693)
                  ·
                    refine ⟨10577528953119772343063885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28206743874986059581503693 10577528953119772343063885)
                    ·
                      refine ⟨3966573357419914628648957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10577528953119772343063885 3966573357419914628648957)
                      ·
                        rfl

theorem cell23_7724874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_7724874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7724874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7724874 prefixEnd_7724874 := by exact prefixLift 7724874
  have htrace : WordTrace (prefixWord ++ tailWord_7724874) baseStart_7724874 baseEnd_7724874 := by
    simpa [prefixWord, tailWord_7724874, baseEnd_7724874] using wordTrace_append hprefix tailTrace_7724874
  have hstable : (prefixWord ++ tailWord_7724874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7724874).length < 2 ^ (prefixWord ++ tailWord_7724874).sum := by decide
  have hdescent : baseEnd_7724874 < baseStart_7724874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7724874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725038 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_7725038 : Nat := 118140960795 + 7725038 * 2 ^ 59
def prefixEnd_7725038 : Nat := 4983230072969 + 3 ^ 40 * 7725038 * 2
def baseEnd_7725038 : Nat := 3966657568247251986998203

theorem tailTrace_7725038 : CollatzResearch.WordTrace tailWord_7725038 prefixEnd_7725038 3966657568247251986998203 := by
  unfold tailWord_7725038
  simp only [CollatzResearch.WordTrace]
  refine ⟨35219410373439266537270971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187836855325009421532111845 35219410373439266537270971)
  ·
    refine ⟨52829115560158899805906457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35219410373439266537270971 52829115560158899805906457)
    ·
      refine ⟨39621836670119174854429843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52829115560158899805906457 39621836670119174854429843)
      ·
        refine ⟨59432755005178762281644765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39621836670119174854429843 59432755005178762281644765)
        ·
          refine ⟨22287283126942035855616787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59432755005178762281644765 22287283126942035855616787)
          ·
            refine ⟨33430924690413053783425181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22287283126942035855616787 33430924690413053783425181)
            ·
              refine ⟨12536596758904895168784443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33430924690413053783425181 12536596758904895168784443)
              ·
                refine ⟨18804895138357342753176665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12536596758904895168784443 18804895138357342753176665)
                ·
                  refine ⟨14103671353768007064882499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18804895138357342753176665 14103671353768007064882499)
                  ·
                    refine ⟨21155507030652010597323749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14103671353768007064882499 21155507030652010597323749)
                    ·
                      refine ⟨3966657568247251986998203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21155507030652010597323749 3966657568247251986998203)
                      ·
                        rfl

theorem cell23_7725038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_7725038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725038 prefixEnd_7725038 := by exact prefixLift 7725038
  have htrace : WordTrace (prefixWord ++ tailWord_7725038) baseStart_7725038 baseEnd_7725038 := by
    simpa [prefixWord, tailWord_7725038, baseEnd_7725038] using wordTrace_append hprefix tailTrace_7725038
  have hstable : (prefixWord ++ tailWord_7725038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725038).length < 2 ^ (prefixWord ++ tailWord_7725038).sum := by decide
  have hdescent : baseEnd_7725038 < baseStart_7725038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725048 : List Nat := [2, 1, 2, 1, 1, 3, 3, 5, 1, 4]
def baseStart_7725048 : Nat := 118140960795 + 7725048 * 2 ^ 59
def prefixEnd_7725048 : Nat := 4983230072969 + 3 ^ 40 * 7725048 * 2
def baseEnd_7725048 : Nat := 1322220901017932315957719

theorem tailTrace_7725048 : CollatzResearch.WordTrace tailWord_7725048 prefixEnd_7725048 1322220901017932315957719 := by
  unfold tailWord_7725048
  simp only [CollatzResearch.WordTrace]
  refine ⟨140877823858738952003015899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187837098478318602670687865 140877823858738952003015899)
  ·
    refine ⟨211316735788108428004523849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140877823858738952003015899 211316735788108428004523849)
    ·
      refine ⟨158487551841081321003392887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211316735788108428004523849 158487551841081321003392887)
      ·
        refine ⟨237731327761621981505089331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158487551841081321003392887 237731327761621981505089331)
        ·
          refine ⟨356596991642432972257633997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237731327761621981505089331 356596991642432972257633997)
          ·
            refine ⟨133723871865912364596612749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356596991642432972257633997 133723871865912364596612749)
            ·
              refine ⟨50146451949717136723729781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133723871865912364596612749 50146451949717136723729781)
              ·
                refine ⟨4701229870285981567849667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50146451949717136723729781 4701229870285981567849667)
                ·
                  refine ⟨7051844805428972351774501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4701229870285981567849667 7051844805428972351774501)
                  ·
                    refine ⟨1322220901017932315957719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7051844805428972351774501 1322220901017932315957719)
                    ·
                      rfl

theorem cell23_7725048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_7725048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725048 prefixEnd_7725048 := by exact prefixLift 7725048
  have htrace : WordTrace (prefixWord ++ tailWord_7725048) baseStart_7725048 baseEnd_7725048 := by
    simpa [prefixWord, tailWord_7725048, baseEnd_7725048] using wordTrace_append hprefix tailTrace_7725048
  have hstable : (prefixWord ++ tailWord_7725048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725048).length < 2 ^ (prefixWord ++ tailWord_7725048).sum := by decide
  have hdescent : baseEnd_7725048 < baseStart_7725048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725061 : List Nat := [1, 3, 1, 1, 2, 4, 3, 2, 6]
def baseStart_7725061 : Nat := 118140960795 + 7725061 * 2 ^ 59
def prefixEnd_7725061 : Nat := 4983230072969 + 3 ^ 40 * 7725061 * 2
def baseEnd_7725061 : Nat := 440741042033589488556733

theorem tailTrace_7725061 : CollatzResearch.WordTrace tailWord_7725061 prefixEnd_7725061 440741042033589488556733 := by
  unfold tailWord_7725061
  simp only [CollatzResearch.WordTrace]
  refine ⟨281756121866430807226255037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187837414577620538150836691 281756121866430807226255037)
  ·
    refine ⟨105658545699911552709845639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281756121866430807226255037 105658545699911552709845639)
    ·
      refine ⟨158487818549867329064768459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105658545699911552709845639 158487818549867329064768459)
      ·
        refine ⟨237731727824800993597152689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158487818549867329064768459 237731727824800993597152689)
        ·
          refine ⟨178298795868600745197864517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237731727824800993597152689 178298795868600745197864517)
          ·
            refine ⟨33431024225362639724599597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178298795868600745197864517 33431024225362639724599597)
            ·
              refine ⟨12536634084510989896724849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33431024225362639724599597 12536634084510989896724849)
              ·
                refine ⟨9402475563383242422543637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12536634084510989896724849 9402475563383242422543637)
                ·
                  refine ⟨440741042033589488556733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9402475563383242422543637 440741042033589488556733)
                  ·
                    rfl

theorem cell23_7725061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 6].length) (baseStart_7725061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725061 prefixEnd_7725061 := by exact prefixLift 7725061
  have htrace : WordTrace (prefixWord ++ tailWord_7725061) baseStart_7725061 baseEnd_7725061 := by
    simpa [prefixWord, tailWord_7725061, baseEnd_7725061] using wordTrace_append hprefix tailTrace_7725061
  have hstable : (prefixWord ++ tailWord_7725061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725061).length < 2 ^ (prefixWord ++ tailWord_7725061).sum := by decide
  have hdescent : baseEnd_7725061 < baseStart_7725061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725064 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_7725064 : Nat := 118140960795 + 7725064 * 2 ^ 59
def prefixEnd_7725064 : Nat := 4983230072969 + 3 ^ 40 * 7725064 * 2
def baseEnd_7725064 : Nat := 3966670918744268885273083

theorem tailTrace_7725064 : CollatzResearch.WordTrace tailWord_7725064 prefixEnd_7725064 3966670918744268885273083 := by
  unfold tailWord_7725064
  simp only [CollatzResearch.WordTrace]
  refine ⟨140878115642709969369307123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187837487523613292492409497 140878115642709969369307123)
  ·
    refine ⟨211317173464064954053960685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140878115642709969369307123 211317173464064954053960685)
    ·
      refine ⟨79243940049024357770235257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211317173464064954053960685 79243940049024357770235257)
      ·
        refine ⟨59432955036768268327676443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79243940049024357770235257 59432955036768268327676443)
        ·
          refine ⟨89149432555152402491514665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59432955036768268327676443 89149432555152402491514665)
          ·
            refine ⟨66862074416364301868635999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89149432555152402491514665 66862074416364301868635999)
            ·
              refine ⟨100293111624546452802953999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66862074416364301868635999 100293111624546452802953999)
              ·
                refine ⟨150439667436819679204430999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100293111624546452802953999 150439667436819679204430999)
                ·
                  refine ⟨225659501155229518806646499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150439667436819679204430999 225659501155229518806646499)
                  ·
                    refine ⟨338489251732844278209969749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 225659501155229518806646499 338489251732844278209969749)
                    ·
                      refine ⟨3966670918744268885273083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 338489251732844278209969749 3966670918744268885273083)
                      ·
                        rfl

theorem cell23_7725064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_7725064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725064 prefixEnd_7725064 := by exact prefixLift 7725064
  have htrace : WordTrace (prefixWord ++ tailWord_7725064) baseStart_7725064 baseEnd_7725064 := by
    simpa [prefixWord, tailWord_7725064, baseEnd_7725064] using wordTrace_append hprefix tailTrace_7725064
  have hstable : (prefixWord ++ tailWord_7725064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725064).length < 2 ^ (prefixWord ++ tailWord_7725064).sum := by decide
  have hdescent : baseEnd_7725064 < baseStart_7725064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725131 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 3]
def baseStart_7725131 : Nat := 118140960795 + 7725131 * 2 ^ 59
def prefixEnd_7725131 : Nat := 4983230072969 + 3 ^ 40 * 7725131 * 2
def baseEnd_7725131 : Nat := 3966705321948120123135275

theorem tailTrace_7725131 : CollatzResearch.WordTrace tailWord_7725131 prefixEnd_7725131 3966705321948120123135275 := by
  unfold tailWord_7725131
  simp only [CollatzResearch.WordTrace]
  refine ⟨281758674976177209181303247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187839116650784806120868831 281758674976177209181303247)
  ·
    refine ⟨422638012464265813771954871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281758674976177209181303247 422638012464265813771954871)
    ·
      refine ⟨633957018696398720657932307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422638012464265813771954871 633957018696398720657932307)
      ·
        refine ⟨950935528044598080986898461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633957018696398720657932307 950935528044598080986898461)
        ·
          refine ⟨356600823016724280370086923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 950935528044598080986898461 356600823016724280370086923)
          ·
            refine ⟨534901234525086420555130385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356600823016724280370086923 534901234525086420555130385)
            ·
              refine ⟨401175925893814815416347789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534901234525086420555130385 401175925893814815416347789)
              ·
                refine ⟨150440972210180555781130421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401175925893814815416347789 150440972210180555781130421)
                ·
                  refine ⟨14103841144704427104480977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150440972210180555781130421 14103841144704427104480977)
                  ·
                    refine ⟨10577880858528320328360733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14103841144704427104480977 10577880858528320328360733)
                    ·
                      refine ⟨3966705321948120123135275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10577880858528320328360733 3966705321948120123135275)
                      ·
                        rfl

theorem cell23_7725131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 3].length) (baseStart_7725131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725131 prefixEnd_7725131 := by exact prefixLift 7725131
  have htrace : WordTrace (prefixWord ++ tailWord_7725131) baseStart_7725131 baseEnd_7725131 := by
    simpa [prefixWord, tailWord_7725131, baseEnd_7725131] using wordTrace_append hprefix tailTrace_7725131
  have hstable : (prefixWord ++ tailWord_7725131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725131).length < 2 ^ (prefixWord ++ tailWord_7725131).sum := by decide
  have hdescent : baseEnd_7725131 < baseStart_7725131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725141 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_7725141 : Nat := 118140960795 + 7725141 * 2 ^ 59
def prefixEnd_7725141 : Nat := 4983230072969 + 3 ^ 40 * 7725141 * 2
def baseEnd_7725141 : Nat := 3966710456754665084010229

theorem tailTrace_7725141 : CollatzResearch.WordTrace tailWord_7725141 prefixEnd_7725141 3966710456754665084010229 := by
  unfold tailWord_7725141
  simp only [CollatzResearch.WordTrace]
  refine ⟨281759039706140980889167277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187839359804093987259444851 281759039706140980889167277)
  ·
    refine ⟨105659639889802867833437729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281759039706140980889167277 105659639889802867833437729)
    ·
      refine ⟨79244729917352150875078297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105659639889802867833437729 79244729917352150875078297)
      ·
        refine ⟨59433547438014113156308723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79244729917352150875078297 59433547438014113156308723)
        ·
          refine ⟨89150321157021169734463085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59433547438014113156308723 89150321157021169734463085)
          ·
            refine ⟨33431370433882938650423657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89150321157021169734463085 33431370433882938650423657)
            ·
              refine ⟨25073527825412203987817743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33431370433882938650423657 25073527825412203987817743)
              ·
                refine ⟨37610291738118305981726615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25073527825412203987817743 37610291738118305981726615)
                ·
                  refine ⟨56415437607177458972589923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37610291738118305981726615 56415437607177458972589923)
                  ·
                    refine ⟨84623156410766188458884885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56415437607177458972589923 84623156410766188458884885)
                    ·
                      refine ⟨3966710456754665084010229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84623156410766188458884885 3966710456754665084010229)
                      ·
                        rfl

theorem cell23_7725141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_7725141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725141 prefixEnd_7725141 := by exact prefixLift 7725141
  have htrace : WordTrace (prefixWord ++ tailWord_7725141) baseStart_7725141 baseEnd_7725141 := by
    simpa [prefixWord, tailWord_7725141, baseEnd_7725141] using wordTrace_append hprefix tailTrace_7725141
  have hstable : (prefixWord ++ tailWord_7725141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725141).length < 2 ^ (prefixWord ++ tailWord_7725141).sum := by decide
  have hdescent : baseEnd_7725141 < baseStart_7725141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725142 : List Nat := [5, 2, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_7725142 : Nat := 118140960795 + 7725142 * 2 ^ 59
def prefixEnd_7725142 : Nat := 4983230072969 + 3 ^ 40 * 7725142 * 2
def baseEnd_7725142 : Nat := 1322236990078439860032575

theorem tailTrace_7725142 : CollatzResearch.WordTrace tailWord_7725142 prefixEnd_7725142 1322236990078439860032575 := by
  unfold tailWord_7725142
  simp only [CollatzResearch.WordTrace]
  refine ⟨17609942261196084878747105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187839384119424905373302453 17609942261196084878747105)
  ·
    refine ⟨13207456695897063659060329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17609942261196084878747105 13207456695897063659060329)
    ·
      refine ⟨9905592521922797744295247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13207456695897063659060329 9905592521922797744295247)
      ·
        refine ⟨14858388782884196616442871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9905592521922797744295247 14858388782884196616442871)
        ·
          refine ⟨22287583174326294924664307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14858388782884196616442871 22287583174326294924664307)
          ·
            refine ⟨33431374761489442386996461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22287583174326294924664307 33431374761489442386996461)
            ·
              refine ⟨12536765535558540895123673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33431374761489442386996461 12536765535558540895123673)
              ·
                refine ⟨9402574151668905671342755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12536765535558540895123673 9402574151668905671342755)
                ·
                  refine ⟨14103861227503358507014133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9402574151668905671342755 14103861227503358507014133)
                  ·
                    refine ⟨1322236990078439860032575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14103861227503358507014133 1322236990078439860032575)
                    ·
                      rfl

theorem cell23_7725142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_7725142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725142 prefixEnd_7725142 := by exact prefixLift 7725142
  have htrace : WordTrace (prefixWord ++ tailWord_7725142) baseStart_7725142 baseEnd_7725142 := by
    simpa [prefixWord, tailWord_7725142, baseEnd_7725142] using wordTrace_append hprefix tailTrace_7725142
  have hstable : (prefixWord ++ tailWord_7725142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725142).length < 2 ^ (prefixWord ++ tailWord_7725142).sum := by decide
  have hdescent : baseEnd_7725142 < baseStart_7725142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725162 : List Nat := [3, 1, 3, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_7725162 : Nat := 118140960795 + 7725162 * 2 ^ 59
def prefixEnd_7725162 : Nat := 4983230072969 + 3 ^ 40 * 7725162 * 2
def baseEnd_7725162 : Nat := 3966721239848409501847633

theorem tailTrace_7725162 : CollatzResearch.WordTrace tailWord_7725162 prefixEnd_7725162 3966721239848409501847633 := by
  unfold tailWord_7725162
  simp only [CollatzResearch.WordTrace]
  refine ⟨70439951409766225368920435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187839870426043267650454493 70439951409766225368920435)
  ·
    refine ⟨105659927114649338053380653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70439951409766225368920435 105659927114649338053380653)
    ·
      refine ⟨39622472667993501770017745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105659927114649338053380653 39622472667993501770017745)
      ·
        refine ⟨29716854500995126327513309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39622472667993501770017745 29716854500995126327513309)
        ·
          refine ⟨11143820437873172372817491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29716854500995126327513309 11143820437873172372817491)
          ·
            refine ⟨16715730656809758559226237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11143820437873172372817491 16715730656809758559226237)
            ·
              refine ⟨6268398996303659459709839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16715730656809758559226237 6268398996303659459709839)
              ·
                refine ⟨9402598494455489189564759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268398996303659459709839 9402598494455489189564759)
                ·
                  refine ⟨14103897741683233784347139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9402598494455489189564759 14103897741683233784347139)
                  ·
                    refine ⟨21155846612524850676520709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14103897741683233784347139 21155846612524850676520709)
                    ·
                      refine ⟨3966721239848409501847633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21155846612524850676520709 3966721239848409501847633)
                      ·
                        rfl

theorem cell23_7725162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_7725162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725162 prefixEnd_7725162 := by exact prefixLift 7725162
  have htrace : WordTrace (prefixWord ++ tailWord_7725162) baseStart_7725162 baseEnd_7725162 := by
    simpa [prefixWord, tailWord_7725162, baseEnd_7725162] using wordTrace_append hprefix tailTrace_7725162
  have hstable : (prefixWord ++ tailWord_7725162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725162).length < 2 ^ (prefixWord ++ tailWord_7725162).sum := by decide
  have hdescent : baseEnd_7725162 < baseStart_7725162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725181 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_7725181 : Nat := 118140960795 + 7725181 * 2 ^ 59
def prefixEnd_7725181 : Nat := 4983230072969 + 3 ^ 40 * 7725181 * 2
def baseEnd_7725181 : Nat := 1322243665326948309170015

theorem tailTrace_7725181 : CollatzResearch.WordTrace tailWord_7725181 prefixEnd_7725181 1322243665326948309170015 := by
  unfold tailWord_7725181
  simp only [CollatzResearch.WordTrace]
  refine ⟨281760498625996067720623397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187840332417330711813748931 281760498625996067720623397)
  ·
    refine ⟨52830093492374262697616887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281760498625996067720623397 52830093492374262697616887)
    ·
      refine ⟨79245140238561394046425331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52830093492374262697616887 79245140238561394046425331)
      ·
        refine ⟨118867710357842091069637997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79245140238561394046425331 118867710357842091069637997)
        ·
          refine ⟨44575391384190784151114249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118867710357842091069637997 44575391384190784151114249)
          ·
            refine ⟨33431543538143088113335687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44575391384190784151114249 33431543538143088113335687)
            ·
              refine ⟨50147315307214632170003531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33431543538143088113335687 50147315307214632170003531)
              ·
                refine ⟨75220972960821948255005297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50147315307214632170003531 75220972960821948255005297)
                ·
                  refine ⟨56415729720616461191253973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75220972960821948255005297 56415729720616461191253973)
                  ·
                    refine ⟨1322243665326948309170015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56415729720616461191253973 1322243665326948309170015)
                    ·
                      rfl

theorem cell23_7725181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_7725181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725181 prefixEnd_7725181 := by exact prefixLift 7725181
  have htrace : WordTrace (prefixWord ++ tailWord_7725181) baseStart_7725181 baseEnd_7725181 := by
    simpa [prefixWord, tailWord_7725181, baseEnd_7725181] using wordTrace_append hprefix tailTrace_7725181
  have hstable : (prefixWord ++ tailWord_7725181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725181).length < 2 ^ (prefixWord ++ tailWord_7725181).sum := by decide
  have hdescent : baseEnd_7725181 < baseStart_7725181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725185 : List Nat := [1, 2, 4, 2, 4, 1, 1, 8]
def baseStart_7725185 : Nat := 118140960795 + 7725185 * 2 ^ 59
def prefixEnd_7725185 : Nat := 4983230072969 + 3 ^ 40 * 7725185 * 2
def baseEnd_7725185 : Nat := 146916038885313441180001

theorem tailTrace_7725185 : CollatzResearch.WordTrace tailWord_7725185 prefixEnd_7725185 146916038885313441180001 := by
  unfold tailWord_7725185
  simp only [CollatzResearch.WordTrace]
  refine ⟨281760644517981576403769009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187840429678654384269179339 281760644517981576403769009)
  ·
    refine ⟨211320483388486182302826757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281760644517981576403769009 211320483388486182302826757)
    ·
      refine ⟨39622590635341159181780017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211320483388486182302826757 39622590635341159181780017)
      ·
        refine ⟨29716942976505869386335013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39622590635341159181780017 29716942976505869386335013)
        ·
          refine ⟨5571926808094850509937815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29716942976505869386335013 5571926808094850509937815)
          ·
            refine ⟨8357890212142275764906723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5571926808094850509937815 8357890212142275764906723)
            ·
              refine ⟨12536835318213413647360085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8357890212142275764906723 12536835318213413647360085)
              ·
                refine ⟨146916038885313441180001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12536835318213413647360085 146916038885313441180001)
                ·
                  rfl

theorem cell23_7725185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 8].length) (baseStart_7725185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725185 prefixEnd_7725185 := by exact prefixLift 7725185
  have htrace : WordTrace (prefixWord ++ tailWord_7725185) baseStart_7725185 baseEnd_7725185 := by
    simpa [prefixWord, tailWord_7725185, baseEnd_7725185] using wordTrace_append hprefix tailTrace_7725185
  have hstable : (prefixWord ++ tailWord_7725185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725185).length < 2 ^ (prefixWord ++ tailWord_7725185).sum := by decide
  have hdescent : baseEnd_7725185 < baseStart_7725185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725205 : List Nat := [1, 3, 2, 1, 1, 1, 4, 4, 1, 3, 2]
def baseStart_7725205 : Nat := 118140960795 + 7725205 * 2 ^ 59
def prefixEnd_7725205 : Nat := 4983230072969 + 3 ^ 40 * 7725205 * 2
def baseEnd_7725205 : Nat := 3966743319516552833609935

theorem tailTrace_7725205 : CollatzResearch.WordTrace tailWord_7725205 prefixEnd_7725205 3966743319516552833609935 := by
  unfold tailWord_7725205
  simp only [CollatzResearch.WordTrace]
  refine ⟨281761373977909119819497069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187840915985272746546331379 281761373977909119819497069)
  ·
    refine ⟨105660515241715919932311401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281761373977909119819497069 105660515241715919932311401)
    ·
      refine ⟨79245386431286939949233551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105660515241715919932311401 79245386431286939949233551)
      ·
        refine ⟨118868079646930409923850327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79245386431286939949233551 118868079646930409923850327)
        ·
          refine ⟨178302119470395614885775491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118868079646930409923850327 178302119470395614885775491)
          ·
            refine ⟨267453179205593422328663237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178302119470395614885775491 267453179205593422328663237)
            ·
              refine ⟨50147471101048766686624357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267453179205593422328663237 50147471101048766686624357)
              ·
                refine ⟨9402650831446643753742067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50147471101048766686624357 9402650831446643753742067)
                ·
                  refine ⟨14103976247169965630613101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9402650831446643753742067 14103976247169965630613101)
                  ·
                    refine ⟨5288991092688737111479913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14103976247169965630613101 5288991092688737111479913)
                    ·
                      refine ⟨3966743319516552833609935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5288991092688737111479913 3966743319516552833609935)
                      ·
                        rfl

theorem cell23_7725205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_7725205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725205 prefixEnd_7725205 := by exact prefixLift 7725205
  have htrace : WordTrace (prefixWord ++ tailWord_7725205) baseStart_7725205 baseEnd_7725205 := by
    simpa [prefixWord, tailWord_7725205, baseEnd_7725205] using wordTrace_append hprefix tailTrace_7725205
  have hstable : (prefixWord ++ tailWord_7725205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725205).length < 2 ^ (prefixWord ++ tailWord_7725205).sum := by decide
  have hdescent : baseEnd_7725205 < baseStart_7725205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725221 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_7725221 : Nat := 118140960795 + 7725221 * 2 ^ 59
def prefixEnd_7725221 : Nat := 4983230072969 + 3 ^ 40 * 7725221 * 2
def baseEnd_7725221 : Nat := 3966751535207024771009861

theorem tailTrace_7725221 : CollatzResearch.WordTrace tailWord_7725221 prefixEnd_7725221 3966751535207024771009861 := by
  unfold tailWord_7725221
  simp only [CollatzResearch.WordTrace]
  refine ⟨281761957545851154552079517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187841305030567436368053011 281761957545851154552079517)
  ·
    refine ⟨105660734079694182957029819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281761957545851154552079517 105660734079694182957029819)
    ·
      refine ⟨158491101119541274435544729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105660734079694182957029819 158491101119541274435544729)
      ·
        refine ⟨118868325839655955826658547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158491101119541274435544729 118868325839655955826658547)
        ·
          refine ⟨178302488759483933739987821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118868325839655955826658547 178302488759483933739987821)
          ·
            refine ⟨66863433284806475152495433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178302488759483933739987821 66863433284806475152495433)
            ·
              refine ⟨50147574963604856364371575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66863433284806475152495433 50147574963604856364371575)
              ·
                refine ⟨75221362445407284546557363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50147574963604856364371575 75221362445407284546557363)
                ·
                  refine ⟨112832043668110926819836045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75221362445407284546557363 112832043668110926819836045)
                  ·
                    refine ⟨42312016375541597557438517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112832043668110926819836045 42312016375541597557438517)
                    ·
                      refine ⟨3966751535207024771009861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42312016375541597557438517 3966751535207024771009861)
                      ·
                        rfl

theorem cell23_7725221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_7725221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725221 prefixEnd_7725221 := by exact prefixLift 7725221
  have htrace : WordTrace (prefixWord ++ tailWord_7725221) baseStart_7725221 baseEnd_7725221 := by
    simpa [prefixWord, tailWord_7725221, baseEnd_7725221] using wordTrace_append hprefix tailTrace_7725221
  have hstable : (prefixWord ++ tailWord_7725221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725221).length < 2 ^ (prefixWord ++ tailWord_7725221).sum := by decide
  have hdescent : baseEnd_7725221 < baseStart_7725221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725229 : List Nat := [1, 5, 2, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_7725229 : Nat := 118140960795 + 7725229 * 2 ^ 59
def prefixEnd_7725229 : Nat := 4983230072969 + 3 ^ 40 * 7725229 * 2
def baseEnd_7725229 : Nat := 3966755643052260739709825

theorem tailTrace_7725229 : CollatzResearch.WordTrace tailWord_7725229 prefixEnd_7725229 3966755643052260739709825 := by
  unfold tailWord_7725229
  simp only [CollatzResearch.WordTrace]
  refine ⟨281762249329822171918370741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187841499553214781278913827 281762249329822171918370741)
  ·
    refine ⟨26415210874670828617347257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281762249329822171918370741 26415210874670828617347257)
    ·
      refine ⟨19811408156003121463010443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26415210874670828617347257 19811408156003121463010443)
      ·
        refine ⟨29717112234004682194515665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19811408156003121463010443 29717112234004682194515665)
        ·
          refine ⟨22287834175503511645886749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29717112234004682194515665 22287834175503511645886749)
          ·
            refine ⟨8357937815813816867207531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22287834175503511645886749 8357937815813816867207531)
            ·
              refine ⟨12536906723720725300811297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8357937815813816867207531 12536906723720725300811297)
              ·
                refine ⟨9402680042790543975608473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12536906723720725300811297 9402680042790543975608473)
                ·
                  refine ⟨7052010032092907981706355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9402680042790543975608473 7052010032092907981706355)
                  ·
                    refine ⟨10578015048139361972559533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7052010032092907981706355 10578015048139361972559533)
                    ·
                      refine ⟨3966755643052260739709825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10578015048139361972559533 3966755643052260739709825)
                      ·
                        rfl

theorem cell23_7725229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_7725229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725229 prefixEnd_7725229 := by exact prefixLift 7725229
  have htrace : WordTrace (prefixWord ++ tailWord_7725229) baseStart_7725229 baseEnd_7725229 := by
    simpa [prefixWord, tailWord_7725229, baseEnd_7725229] using wordTrace_append hprefix tailTrace_7725229
  have hstable : (prefixWord ++ tailWord_7725229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725229).length < 2 ^ (prefixWord ++ tailWord_7725229).sum := by decide
  have hdescent : baseEnd_7725229 < baseStart_7725229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725248 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 4]
def baseStart_7725248 : Nat := 118140960795 + 7725248 * 2 ^ 59
def prefixEnd_7725248 : Nat := 4983230072969 + 3 ^ 40 * 7725248 * 2
def baseEnd_7725248 : Nat := 3966765399184696165372237

theorem tailTrace_7725248 : CollatzResearch.WordTrace tailWord_7725248 prefixEnd_7725248 3966765399184696165372237 := by
  unfold tailWord_7725248
  simp only [CollatzResearch.WordTrace]
  refine ⟨140881471158376669081656199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187841961544502225442208265 140881471158376669081656199)
  ·
    refine ⟨211322206737565003622484299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140881471158376669081656199 211322206737565003622484299)
    ·
      refine ⟨316983310106347505433726449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211322206737565003622484299 316983310106347505433726449)
      ·
        refine ⟨237737482579760629075294837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316983310106347505433726449 237737482579760629075294837)
        ·
          refine ⟨22287888991852558975808891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237737482579760629075294837 22287888991852558975808891)
          ·
            refine ⟨33431833487778838463713337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22287888991852558975808891 33431833487778838463713337)
            ·
              refine ⟨25073875115834128847785003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33431833487778838463713337 25073875115834128847785003)
              ·
                refine ⟨37610812673751193271677505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25073875115834128847785003 37610812673751193271677505)
                ·
                  refine ⟨28208109505313394953758129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37610812673751193271677505 28208109505313394953758129)
                  ·
                    refine ⟨21156082128985046215318597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28208109505313394953758129 21156082128985046215318597)
                    ·
                      refine ⟨3966765399184696165372237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21156082128985046215318597 3966765399184696165372237)
                      ·
                        rfl

theorem cell23_7725248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_7725248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725248 prefixEnd_7725248 := by exact prefixLift 7725248
  have htrace : WordTrace (prefixWord ++ tailWord_7725248) baseStart_7725248 baseEnd_7725248 := by
    simpa [prefixWord, tailWord_7725248, baseEnd_7725248] using wordTrace_append hprefix tailTrace_7725248
  have hstable : (prefixWord ++ tailWord_7725248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725248).length < 2 ^ (prefixWord ++ tailWord_7725248).sum := by decide
  have hdescent : baseEnd_7725248 < baseStart_7725248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725252 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_7725252 : Nat := 118140960795 + 7725252 * 2 ^ 59
def prefixEnd_7725252 : Nat := 4983230072969 + 3 ^ 40 * 7725252 * 2
def baseEnd_7725252 : Nat := 3966767453107314149722219

theorem tailTrace_7725252 : CollatzResearch.WordTrace tailWord_7725252 prefixEnd_7725252 3966767453107314149722219 := by
  unfold tailWord_7725252
  simp only [CollatzResearch.WordTrace]
  refine ⟨140881544104369423423229005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187842058805825897897638673 140881544104369423423229005)
  ·
    refine ⟨52830579039138533783710877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140881544104369423423229005 52830579039138533783710877)
    ·
      refine ⟨19811467139676950168891579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52830579039138533783710877 19811467139676950168891579)
      ·
        refine ⟨29717200709515425253337369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19811467139676950168891579 29717200709515425253337369)
        ·
          refine ⟨22287900532136568940003027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29717200709515425253337369 22287900532136568940003027)
          ·
            refine ⟨33431850798204853410004541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22287900532136568940003027 33431850798204853410004541)
            ·
              refine ⟨12536944049326820028751703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33431850798204853410004541 12536944049326820028751703)
              ·
                refine ⟨18805416073990230043127555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12536944049326820028751703 18805416073990230043127555)
                ·
                  refine ⟨28208124110985345064691333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18805416073990230043127555 28208124110985345064691333)
                  ·
                    refine ⟨5289023270809752199629625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28208124110985345064691333 5289023270809752199629625)
                    ·
                      refine ⟨3966767453107314149722219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5289023270809752199629625 3966767453107314149722219)
                      ·
                        rfl

theorem cell23_7725252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_7725252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725252 prefixEnd_7725252 := by exact prefixLift 7725252
  have htrace : WordTrace (prefixWord ++ tailWord_7725252) baseStart_7725252 baseEnd_7725252 := by
    simpa [prefixWord, tailWord_7725252, baseEnd_7725252] using wordTrace_append hprefix tailTrace_7725252
  have hstable : (prefixWord ++ tailWord_7725252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725252).length < 2 ^ (prefixWord ++ tailWord_7725252).sum := by decide
  have hdescent : baseEnd_7725252 < baseStart_7725252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725288 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 4, 5]
def baseStart_7725288 : Nat := 118140960795 + 7725288 * 2 ^ 59
def prefixEnd_7725288 : Nat := 4983230072969 + 3 ^ 40 * 7725288 * 2
def baseEnd_7725288 : Nat := 1322261979470292002957351

theorem tailTrace_7725288 : CollatzResearch.WordTrace tailWord_7725288 prefixEnd_7725288 1322261979470292002957351 := by
  unfold tailWord_7725288
  simp only [CollatzResearch.WordTrace]
  refine ⟨140882200618304212497384259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187842934157738949996512345 140882200618304212497384259)
  ·
    refine ⟨211323300927456318746076389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140882200618304212497384259 211323300927456318746076389)
    ·
      refine ⟨39623118923898059764889323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211323300927456318746076389 39623118923898059764889323)
      ·
        refine ⟨59434678385847089647333985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39623118923898059764889323 59434678385847089647333985)
        ·
          refine ⟨44576008789385317235500489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59434678385847089647333985 44576008789385317235500489)
          ·
            refine ⟨33432006592038987926625367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44576008789385317235500489 33432006592038987926625367)
            ·
              refine ⟨50148009888058481889938051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33432006592038987926625367 50148009888058481889938051)
              ·
                refine ⟨75222014832087722834907077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50148009888058481889938051 75222014832087722834907077)
                ·
                  refine ⟨14104127781016448031545077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75222014832087722834907077 14104127781016448031545077)
                  ·
                    refine ⟨1322261979470292002957351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14104127781016448031545077 1322261979470292002957351)
                    ·
                      rfl

theorem cell23_7725288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_7725288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725288 prefixEnd_7725288 := by exact prefixLift 7725288
  have htrace : WordTrace (prefixWord ++ tailWord_7725288) baseStart_7725288 baseEnd_7725288 := by
    simpa [prefixWord, tailWord_7725288, baseEnd_7725288] using wordTrace_append hprefix tailTrace_7725288
  have hstable : (prefixWord ++ tailWord_7725288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725288).length < 2 ^ (prefixWord ++ tailWord_7725288).sum := by decide
  have hdescent : baseEnd_7725288 < baseStart_7725288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725298 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_7725298 : Nat := 118140960795 + 7725298 * 2 ^ 59
def prefixEnd_7725298 : Nat := 4983230072969 + 3 ^ 40 * 7725298 * 2
def baseEnd_7725298 : Nat := 3966791073217420969747007

theorem tailTrace_7725298 : CollatzResearch.WordTrace tailWord_7725298 prefixEnd_7725298 3966791073217420969747007 := by
  unfold tailWord_7725298
  simp only [CollatzResearch.WordTrace]
  refine ⟨70441191491643049175658137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187843177311048131135088365 70441191491643049175658137)
  ·
    refine ⟨52830893618732286881743603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70441191491643049175658137 52830893618732286881743603)
    ·
      refine ⟨79246340428098430322615405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52830893618732286881743603 79246340428098430322615405)
      ·
        refine ⟨29717377660536911370980777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79246340428098430322615405 29717377660536911370980777)
        ·
          refine ⟨22288033245402683528235583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29717377660536911370980777 22288033245402683528235583)
          ·
            refine ⟨33432049868104025292353375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22288033245402683528235583 33432049868104025292353375)
            ·
              refine ⟨50148074802156037938530063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33432049868104025292353375 50148074802156037938530063)
              ·
                refine ⟨75222112203234056907795095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50148074802156037938530063 75222112203234056907795095)
                ·
                  refine ⟨112833168304851085361692643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75222112203234056907795095 112833168304851085361692643)
                  ·
                    refine ⟨169249752457276628042538965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112833168304851085361692643 169249752457276628042538965)
                    ·
                      refine ⟨3966791073217420969747007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169249752457276628042538965 3966791073217420969747007)
                      ·
                        rfl

theorem cell23_7725298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_7725298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725298 prefixEnd_7725298 := by exact prefixLift 7725298
  have htrace : WordTrace (prefixWord ++ tailWord_7725298) baseStart_7725298 baseEnd_7725298 := by
    simpa [prefixWord, tailWord_7725298, baseEnd_7725298] using wordTrace_append hprefix tailTrace_7725298
  have hstable : (prefixWord ++ tailWord_7725298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725298).length < 2 ^ (prefixWord ++ tailWord_7725298).sum := by decide
  have hdescent : baseEnd_7725298 < baseStart_7725298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725331 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 10]
def baseStart_7725331 : Nat := 118140960795 + 7725331 * 2 ^ 59
def prefixEnd_7725331 : Nat := 4983230072969 + 3 ^ 40 * 7725331 * 2
def baseEnd_7725331 : Nat := 440756446453224371181595

theorem tailTrace_7725331 : CollatzResearch.WordTrace tailWord_7725331 prefixEnd_7725331 440756446453224371181595 := by
  unfold tailWord_7725331
  simp only [CollatzResearch.WordTrace]
  refine ⟨281765969575452643338583847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187843979716968428892389231 281765969575452643338583847)
  ·
    refine ⟨422648954363178965007875771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281765969575452643338583847 422648954363178965007875771)
    ·
      refine ⟨633973431544768447511813657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422648954363178965007875771 633973431544768447511813657)
      ·
        refine ⟨475480073658576335633860243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633973431544768447511813657 475480073658576335633860243)
        ·
          refine ⟨713220110487864503450790365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475480073658576335633860243 713220110487864503450790365)
          ·
            refine ⟨267457541432949188794046387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 713220110487864503450790365 267457541432949188794046387)
            ·
              refine ⟨401186312149423783191069581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267457541432949188794046387 401186312149423783191069581)
              ·
                refine ⟨150444867056033918696651093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401186312149423783191069581 150444867056033918696651093)
                ·
                  refine ⟨440756446453224371181595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 150444867056033918696651093 440756446453224371181595)
                  ·
                    rfl

theorem cell23_7725331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 10].length) (baseStart_7725331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725331 prefixEnd_7725331 := by exact prefixLift 7725331
  have htrace : WordTrace (prefixWord ++ tailWord_7725331) baseStart_7725331 baseEnd_7725331 := by
    simpa [prefixWord, tailWord_7725331, baseEnd_7725331] using wordTrace_append hprefix tailTrace_7725331
  have hstable : (prefixWord ++ tailWord_7725331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725331).length < 2 ^ (prefixWord ++ tailWord_7725331).sum := by decide
  have hdescent : baseEnd_7725331 < baseStart_7725331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725345 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_7725345 : Nat := 118140960795 + 7725345 * 2 ^ 59
def prefixEnd_7725345 : Nat := 4983230072969 + 3 ^ 40 * 7725345 * 2
def baseEnd_7725345 : Nat := 3966815206808182285859291

theorem tailTrace_7725345 : CollatzResearch.WordTrace tailWord_7725345 prefixEnd_7725345 3966815206808182285859291 := by
  unfold tailWord_7725345
  simp only [CollatzResearch.WordTrace]
  refine ⟨281766480197401923729593489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187844320131601282486395659 281766480197401923729593489)
  ·
    refine ⟨211324860148051442797195117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281766480197401923729593489 211324860148051442797195117)
    ·
      refine ⟨79246822555519291048948169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211324860148051442797195117 79246822555519291048948169)
      ·
        refine ⟨59435116916639468286711127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79246822555519291048948169 59435116916639468286711127)
        ·
          refine ⟨89152675374959202430066691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59435116916639468286711127 89152675374959202430066691)
          ·
            refine ⟨133729013062438803645100037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89152675374959202430066691 133729013062438803645100037)
            ·
              refine ⟨25074189949207275683456257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133729013062438803645100037 25074189949207275683456257)
              ·
                refine ⟨18805642461905456762592193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25074189949207275683456257 18805642461905456762592193)
                ·
                  refine ⟨14104231846429092571944145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18805642461905456762592193 14104231846429092571944145)
                  ·
                    refine ⟨10578173884821819428958109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14104231846429092571944145 10578173884821819428958109)
                    ·
                      refine ⟨3966815206808182285859291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10578173884821819428958109 3966815206808182285859291)
                      ·
                        rfl

theorem cell23_7725345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_7725345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725345 prefixEnd_7725345 := by exact prefixLift 7725345
  have htrace : WordTrace (prefixWord ++ tailWord_7725345) baseStart_7725345 baseEnd_7725345 := by
    simpa [prefixWord, tailWord_7725345, baseEnd_7725345] using wordTrace_append hprefix tailTrace_7725345
  have hstable : (prefixWord ++ tailWord_7725345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725345).length < 2 ^ (prefixWord ++ tailWord_7725345).sum := by decide
  have hdescent : baseEnd_7725345 < baseStart_7725345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725443 : List Nat := [1, 1, 1, 3, 7, 1, 1, 3, 1, 1, 3]
def baseStart_7725443 : Nat := 118140960795 + 7725443 * 2 ^ 59
def prefixEnd_7725443 : Nat := 4983230072969 + 3 ^ 40 * 7725443 * 2
def baseEnd_7725443 : Nat := 3966865527912322902433841

theorem tailTrace_7725443 : CollatzResearch.WordTrace tailWord_7725443 prefixEnd_7725443 3966865527912322902433841 := by
  unfold tailWord_7725443
  simp only [CollatzResearch.WordTrace]
  refine ⟨281770054551046886466660983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187846703034031257644440655 281770054551046886466660983)
  ·
    refine ⟨422655081826570329699991475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281770054551046886466660983 422655081826570329699991475)
    ·
      refine ⟨633982622739855494549987213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422655081826570329699991475 633982622739855494549987213)
      ·
        refine ⟨237743483527445810456245205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 633982622739855494549987213 237743483527445810456245205)
        ·
          refine ⟨5572112895174511182568247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 237743483527445810456245205 5572112895174511182568247)
          ·
            refine ⟨8358169342761766773852371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5572112895174511182568247 8358169342761766773852371)
            ·
              refine ⟨12537254014142650160778557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8358169342761766773852371 12537254014142650160778557)
              ·
                refine ⟨4701470255303493810291959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12537254014142650160778557 4701470255303493810291959)
                ·
                  refine ⟨7052205382955240715437939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4701470255303493810291959 7052205382955240715437939)
                  ·
                    refine ⟨10578308074432861073156909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7052205382955240715437939 10578308074432861073156909)
                    ·
                      refine ⟨3966865527912322902433841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10578308074432861073156909 3966865527912322902433841)
                      ·
                        rfl

theorem cell23_7725443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 1, 1, 3].length) (baseStart_7725443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725443 prefixEnd_7725443 := by exact prefixLift 7725443
  have htrace : WordTrace (prefixWord ++ tailWord_7725443) baseStart_7725443 baseEnd_7725443 := by
    simpa [prefixWord, tailWord_7725443, baseEnd_7725443] using wordTrace_append hprefix tailTrace_7725443
  have hstable : (prefixWord ++ tailWord_7725443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725443).length < 2 ^ (prefixWord ++ tailWord_7725443).sum := by decide
  have hdescent : baseEnd_7725443 < baseStart_7725443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725452 : List Nat := [2, 2, 1, 2, 1, 4, 2, 3, 1, 2, 3]
def baseStart_7725452 : Nat := 118140960795 + 7725452 * 2 ^ 59
def prefixEnd_7725452 : Nat := 4983230072969 + 3 ^ 40 * 7725452 * 2
def baseEnd_7725452 : Nat := 3966870149238213367221299

theorem tailTrace_7725452 : CollatzResearch.WordTrace tailWord_7725452 prefixEnd_7725452 3966870149238213367221299 := by
  unfold tailWord_7725452
  simp only [CollatzResearch.WordTrace]
  refine ⟨140885191404007140501869305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187846921872009520669159073 140885191404007140501869305)
  ·
    refine ⟨105663893553005355376401979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140885191404007140501869305 105663893553005355376401979)
    ·
      refine ⟨158495840329508033064602969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105663893553005355376401979 158495840329508033064602969)
      ·
        refine ⟨118871880247131024798452227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158495840329508033064602969 118871880247131024798452227)
        ·
          refine ⟨178307820370696537197678341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118871880247131024798452227 178307820370696537197678341)
          ·
            refine ⟨33432716319505600724564689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178307820370696537197678341 33432716319505600724564689)
            ·
              refine ⟨25074537239629200543423517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33432716319505600724564689 25074537239629200543423517)
              ·
                refine ⟨9402951464860950203783819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25074537239629200543423517 9402951464860950203783819)
                ·
                  refine ⟨14104427197291425305675729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9402951464860950203783819 14104427197291425305675729)
                  ·
                    refine ⟨10578320397968568979256797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14104427197291425305675729 10578320397968568979256797)
                    ·
                      refine ⟨3966870149238213367221299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10578320397968568979256797 3966870149238213367221299)
                      ·
                        rfl

theorem cell23_7725452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_7725452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725452 prefixEnd_7725452 := by exact prefixLift 7725452
  have htrace : WordTrace (prefixWord ++ tailWord_7725452) baseStart_7725452 baseEnd_7725452 := by
    simpa [prefixWord, tailWord_7725452, baseEnd_7725452] using wordTrace_append hprefix tailTrace_7725452
  have hstable : (prefixWord ++ tailWord_7725452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725452).length < 2 ^ (prefixWord ++ tailWord_7725452).sum := by decide
  have hdescent : baseEnd_7725452 < baseStart_7725452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725466 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2]
def baseStart_7725466 : Nat := 118140960795 + 7725466 * 2 ^ 59
def prefixEnd_7725466 : Nat := 4983230072969 + 3 ^ 40 * 7725466 * 2
def baseEnd_7725466 : Nat := 3966877337967376312446235

theorem tailTrace_7725466 : CollatzResearch.WordTrace tailWord_7725466 prefixEnd_7725466 3966877337967376312446235 := by
  unfold tailWord_7725466
  simp only [CollatzResearch.WordTrace]
  refine ⟨70442723357490890348687063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187847262286642374263165501 70442723357490890348687063)
  ·
    refine ⟨105664085036236335523030595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70442723357490890348687063 105664085036236335523030595)
    ·
      refine ⟨158496127554354503284545893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105664085036236335523030595 158496127554354503284545893)
      ·
        refine ⟨29718023916441469365852355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158496127554354503284545893 29718023916441469365852355)
        ·
          refine ⟨44577035874662204048778533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29718023916441469365852355 44577035874662204048778533)
          ·
            refine ⟨8358194226499163259145975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44577035874662204048778533 8358194226499163259145975)
            ·
              refine ⟨12537291339748744888718963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8358194226499163259145975 12537291339748744888718963)
              ·
                refine ⟨18805937009623117333078445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12537291339748744888718963 18805937009623117333078445)
                ·
                  refine ⟨7052226378608668999904417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18805937009623117333078445 7052226378608668999904417)
                  ·
                    refine ⟨5289169783956501749928313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7052226378608668999904417 5289169783956501749928313)
                    ·
                      refine ⟨3966877337967376312446235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5289169783956501749928313 3966877337967376312446235)
                      ·
                        rfl

theorem cell23_7725466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_7725466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725466 prefixEnd_7725466 := by exact prefixLift 7725466
  have htrace : WordTrace (prefixWord ++ tailWord_7725466) baseStart_7725466 baseEnd_7725466 := by
    simpa [prefixWord, tailWord_7725466, baseEnd_7725466] using wordTrace_append hprefix tailTrace_7725466
  have hstable : (prefixWord ++ tailWord_7725466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725466).length < 2 ^ (prefixWord ++ tailWord_7725466).sum := by decide
  have hdescent : baseEnd_7725466 < baseStart_7725466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725516 : List Nat := [2, 2, 1, 4, 3, 1, 2, 2, 2, 1, 3]
def baseStart_7725516 : Nat := 118140960795 + 7725516 * 2 ^ 59
def prefixEnd_7725516 : Nat := 4983230072969 + 3 ^ 40 * 7725516 * 2
def baseEnd_7725516 : Nat := 3966903012000101116821005

theorem tailTrace_7725516 : CollatzResearch.WordTrace tailWord_7725516 prefixEnd_7725516 3966903012000101116821005 := by
  unfold tailWord_7725516
  simp only [CollatzResearch.WordTrace]
  refine ⟨140886358539891209967034201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187848478053188279956045601 140886358539891209967034201)
  ·
    refine ⟨105664768904918407475275651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140886358539891209967034201 105664768904918407475275651)
    ·
      refine ⟨158497153357377611212913477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105664768904918407475275651 158497153357377611212913477)
      ·
        refine ⟨29718216254508302102421277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158497153357377611212913477 29718216254508302102421277)
        ·
          refine ⟨11144331095440613288407979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29718216254508302102421277 11144331095440613288407979)
          ·
            refine ⟨16716496643160919932611969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11144331095440613288407979 16716496643160919932611969)
            ·
              refine ⟨12537372482370689949458977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16716496643160919932611969 12537372482370689949458977)
              ·
                refine ⟨9403029361778017462094233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12537372482370689949458977 9403029361778017462094233)
                ·
                  refine ⟨7052272021333513096570675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9403029361778017462094233 7052272021333513096570675)
                  ·
                    refine ⟨10578408032000269644856013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7052272021333513096570675 10578408032000269644856013)
                    ·
                      refine ⟨3966903012000101116821005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10578408032000269644856013 3966903012000101116821005)
                      ·
                        rfl

theorem cell23_7725516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_7725516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725516 prefixEnd_7725516 := by exact prefixLift 7725516
  have htrace : WordTrace (prefixWord ++ tailWord_7725516) baseStart_7725516 baseEnd_7725516 := by
    simpa [prefixWord, tailWord_7725516, baseEnd_7725516] using wordTrace_append hprefix tailTrace_7725516
  have hstable : (prefixWord ++ tailWord_7725516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725516).length < 2 ^ (prefixWord ++ tailWord_7725516).sum := by decide
  have hdescent : baseEnd_7725516 < baseStart_7725516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725535 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 4]
def baseStart_7725535 : Nat := 118140960795 + 7725535 * 2 ^ 59
def prefixEnd_7725535 : Nat := 4983230072969 + 3 ^ 40 * 7725535 * 2
def baseEnd_7725535 : Nat := 3966912768132536542483417

theorem tailTrace_7725535 : CollatzResearch.WordTrace tailWord_7725535 prefixEnd_7725535 3966912768132536542483417 := by
  unfold tailWord_7725535
  simp only [CollatzResearch.WordTrace]
  refine ⟨281773410066713586179010059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187848940044475724119340039 281773410066713586179010059)
  ·
    refine ⟨422660115100070379268515089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281773410066713586179010059 422660115100070379268515089)
    ·
      refine ⟨316995086325052784451386317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422660115100070379268515089 316995086325052784451386317)
      ·
        refine ⟨118873157371894794169269869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316995086325052784451386317 118873157371894794169269869)
        ·
          refine ⟨44577434014460547813476201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118873157371894794169269869 44577434014460547813476201)
          ·
            refine ⟨33433075510845410860107151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44577434014460547813476201 33433075510845410860107151)
            ·
              refine ⟨50149613266268116290160727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33433075510845410860107151 50149613266268116290160727)
              ·
                refine ⟨75224419899402174435241091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50149613266268116290160727 75224419899402174435241091)
                ·
                  refine ⟨112836629849103261652861637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75224419899402174435241091 112836629849103261652861637)
                  ·
                    refine ⟨21156868096706861559911557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112836629849103261652861637 21156868096706861559911557)
                    ·
                      refine ⟨3966912768132536542483417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21156868096706861559911557 3966912768132536542483417)
                      ·
                        rfl

theorem cell23_7725535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_7725535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725535 prefixEnd_7725535 := by exact prefixLift 7725535
  have htrace : WordTrace (prefixWord ++ tailWord_7725535) baseStart_7725535 baseEnd_7725535 := by
    simpa [prefixWord, tailWord_7725535, baseEnd_7725535] using wordTrace_append hprefix tailTrace_7725535
  have hstable : (prefixWord ++ tailWord_7725535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725535).length < 2 ^ (prefixWord ++ tailWord_7725535).sum := by decide
  have hdescent : baseEnd_7725535 < baseStart_7725535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725555 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 3]
def baseStart_7725555 : Nat := 118140960795 + 7725555 * 2 ^ 59
def prefixEnd_7725555 : Nat := 4983230072969 + 3 ^ 40 * 7725555 * 2
def baseEnd_7725555 : Nat := 3966923037745626464233325

theorem tailTrace_7725555 : CollatzResearch.WordTrace tailWord_7725555 prefixEnd_7725555 3966923037745626464233325 := by
  unfold tailWord_7725555
  simp only [CollatzResearch.WordTrace]
  refine ⟨281774139526641129594738119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187849426351094086396492079 281774139526641129594738119)
  ·
    refine ⟨422661209289961694392107179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281774139526641129594738119 422661209289961694392107179)
    ·
      refine ⟨633991813934942541588160769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422661209289961694392107179 633991813934942541588160769)
      ·
        refine ⟨475493860451206906191120577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633991813934942541588160769 475493860451206906191120577)
        ·
          refine ⟨356620395338405179643340433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475493860451206906191120577 356620395338405179643340433)
          ·
            refine ⟨267465296503803884732505325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356620395338405179643340433 267465296503803884732505325)
            ·
              refine ⟨100299486188926456774689497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267465296503803884732505325 100299486188926456774689497)
              ·
                refine ⟨75224614641694842581017123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100299486188926456774689497 75224614641694842581017123)
                ·
                  refine ⟨112836921962542263871525685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75224614641694842581017123 112836921962542263871525685)
                  ·
                    refine ⟨10578461433988337237955533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112836921962542263871525685 10578461433988337237955533)
                    ·
                      refine ⟨3966923037745626464233325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10578461433988337237955533 3966923037745626464233325)
                      ·
                        rfl

theorem cell23_7725555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 3].length) (baseStart_7725555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725555 prefixEnd_7725555 := by exact prefixLift 7725555
  have htrace : WordTrace (prefixWord ++ tailWord_7725555) baseStart_7725555 baseEnd_7725555 := by
    simpa [prefixWord, tailWord_7725555, baseEnd_7725555] using wordTrace_append hprefix tailTrace_7725555
  have hstable : (prefixWord ++ tailWord_7725555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725555).length < 2 ^ (prefixWord ++ tailWord_7725555).sum := by decide
  have hdescent : baseEnd_7725555 < baseStart_7725555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725612 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 1, 6, 2]
def baseStart_7725612 : Nat := 118140960795 + 7725612 * 2 ^ 59
def prefixEnd_7725612 : Nat := 4983230072969 + 3 ^ 40 * 7725612 * 2
def baseEnd_7725612 : Nat := 3966952306142932741220563

theorem tailTrace_7725612 : CollatzResearch.WordTrace tailWord_7725612 prefixEnd_7725612 3966952306142932741220563 := by
  unfold tailWord_7725612
  simp only [CollatzResearch.WordTrace]
  refine ⟨140888109243717314164781545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187850812324956418886375393 140888109243717314164781545)
  ·
    refine ⟨105666081932787985623586159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140888109243717314164781545 105666081932787985623586159)
    ·
      refine ⟨158499122899181978435379239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105666081932787985623586159 158499122899181978435379239)
      ·
        refine ⟨237748684348772967653068859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158499122899181978435379239 237748684348772967653068859)
        ·
          refine ⟨356623026523159451479603289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237748684348772967653068859 356623026523159451479603289)
          ·
            refine ⟨267467269892369588609702467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356623026523159451479603289 267467269892369588609702467)
            ·
              refine ⟨401200904838554382914553701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267467269892369588609702467 401200904838554382914553701)
              ·
                refine ⟨75225169657228946796478819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401200904838554382914553701 75225169657228946796478819)
                ·
                  refine ⟨112837754485843420194718229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75225169657228946796478819 112837754485843420194718229)
                  ·
                    refine ⟨5289269741523910321627417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112837754485843420194718229 5289269741523910321627417)
                    ·
                      refine ⟨3966952306142932741220563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5289269741523910321627417 3966952306142932741220563)
                      ·
                        rfl

theorem cell23_7725612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 6, 2].length) (baseStart_7725612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725612 prefixEnd_7725612 := by exact prefixLift 7725612
  have htrace : WordTrace (prefixWord ++ tailWord_7725612) baseStart_7725612 baseEnd_7725612 := by
    simpa [prefixWord, tailWord_7725612, baseEnd_7725612] using wordTrace_append hprefix tailTrace_7725612
  have hstable : (prefixWord ++ tailWord_7725612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725612).length < 2 ^ (prefixWord ++ tailWord_7725612).sum := by decide
  have hdescent : baseEnd_7725612 < baseStart_7725612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725629 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_7725629 : Nat := 118140960795 + 7725629 * 2 ^ 59
def prefixEnd_7725629 : Nat := 4983230072969 + 3 ^ 40 * 7725629 * 2
def baseEnd_7725629 : Nat := 3966961035314059174707985

theorem tailTrace_7725629 : CollatzResearch.WordTrace tailWord_7725629 prefixEnd_7725629 3966961035314059174707985 := by
  unfold tailWord_7725629
  simp only [CollatzResearch.WordTrace]
  refine ⟨281776838528373040232931941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187851225685582026821954627 281776838528373040232931941)
  ·
    refine ⟨52833157224069945043674739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281776838528373040232931941 52833157224069945043674739)
    ·
      refine ⟨79249735836104917565512109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52833157224069945043674739 79249735836104917565512109)
      ·
        refine ⟨29718650938539344087067041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79249735836104917565512109 29718650938539344087067041)
        ·
          refine ⟨22288988203904508065300281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29718650938539344087067041 22288988203904508065300281)
          ·
            refine ⟨16716741152928381048975211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22288988203904508065300281 16716741152928381048975211)
            ·
              refine ⟨25075111729392571573462817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16716741152928381048975211 25075111729392571573462817)
              ·
                refine ⟨18806333797044428680097113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25075111729392571573462817 18806333797044428680097113)
                ·
                  refine ⟨14104750347783321510072835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18806333797044428680097113 14104750347783321510072835)
                  ·
                    refine ⟨21157125521674982265109253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14104750347783321510072835 21157125521674982265109253)
                    ·
                      refine ⟨3966961035314059174707985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21157125521674982265109253 3966961035314059174707985)
                      ·
                        rfl

theorem cell23_7725629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_7725629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725629 prefixEnd_7725629 := by exact prefixLift 7725629
  have htrace : WordTrace (prefixWord ++ tailWord_7725629) baseStart_7725629 baseEnd_7725629 := by
    simpa [prefixWord, tailWord_7725629, baseEnd_7725629] using wordTrace_append hprefix tailTrace_7725629
  have hstable : (prefixWord ++ tailWord_7725629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725629).length < 2 ^ (prefixWord ++ tailWord_7725629).sum := by decide
  have hdescent : baseEnd_7725629 < baseStart_7725629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725632 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 3]
def baseStart_7725632 : Nat := 118140960795 + 7725632 * 2 ^ 59
def prefixEnd_7725632 : Nat := 4983230072969 + 3 ^ 40 * 7725632 * 2
def baseEnd_7725632 : Nat := 3966962575756022662970471

theorem tailTrace_7725632 : CollatzResearch.WordTrace tailWord_7725632 prefixEnd_7725632 3966962575756022662970471 := by
  unfold tailWord_7725632
  simp only [CollatzResearch.WordTrace]
  refine ⟨140888473973681085872645575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187851298631574781163527433 140888473973681085872645575)
  ·
    refine ⟨211332710960521628808968363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140888473973681085872645575 211332710960521628808968363)
    ·
      refine ⟨316999066440782443213452545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211332710960521628808968363 316999066440782443213452545)
      ·
        refine ⟨237749299830586832410089409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316999066440782443213452545 237749299830586832410089409)
        ·
          refine ⟨178311974872940124307567057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237749299830586832410089409 178311974872940124307567057)
          ·
            refine ⟨133733981154705093230675293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178311974872940124307567057 133733981154705093230675293)
            ·
              refine ⟨50150242933014409961503235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133733981154705093230675293 50150242933014409961503235)
              ·
                refine ⟨75225364399521614942254853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50150242933014409961503235 75225364399521614942254853)
                ·
                  refine ⟨14104755824910302801672785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75225364399521614942254853 14104755824910302801672785)
                  ·
                    refine ⟨10578566868682727101254589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14104755824910302801672785 10578566868682727101254589)
                    ·
                      refine ⟨3966962575756022662970471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10578566868682727101254589 3966962575756022662970471)
                      ·
                        rfl

theorem cell23_7725632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_7725632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725632 prefixEnd_7725632 := by exact prefixLift 7725632
  have htrace : WordTrace (prefixWord ++ tailWord_7725632) baseStart_7725632 baseEnd_7725632 := by
    simpa [prefixWord, tailWord_7725632, baseEnd_7725632] using wordTrace_append hprefix tailTrace_7725632
  have hstable : (prefixWord ++ tailWord_7725632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725632).length < 2 ^ (prefixWord ++ tailWord_7725632).sum := by decide
  have hdescent : baseEnd_7725632 < baseStart_7725632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725639 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 3, 4]
def baseStart_7725639 : Nat := 118140960795 + 7725639 * 2 ^ 59
def prefixEnd_7725639 : Nat := 4983230072969 + 3 ^ 40 * 7725639 * 2
def baseEnd_7725639 : Nat := 1322322056706868045194313

theorem tailTrace_7725639 : CollatzResearch.WordTrace tailWord_7725639 prefixEnd_7725639 1322322056706868045194313 := by
  unfold tailWord_7725639
  simp only [CollatzResearch.WordTrace]
  refine ⟨281777203258336811940795971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187851468838891207960530647 281777203258336811940795971)
  ·
    refine ⟨422665804887505217911193957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281777203258336811940795971 422665804887505217911193957)
    ·
      refine ⟨79249838416407228358348867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 422665804887505217911193957 79249838416407228358348867)
      ·
        refine ⟨118874757624610842537523301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79249838416407228358348867 118874757624610842537523301)
        ·
          refine ⟨22289017054614532975785619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118874757624610842537523301 22289017054614532975785619)
          ·
            refine ⟨33433525581921799463678429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22289017054614532975785619 33433525581921799463678429)
            ·
              refine ⟨12537572093220674798879411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33433525581921799463678429 12537572093220674798879411)
              ·
                refine ⟨18806358139831012198319117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12537572093220674798879411 18806358139831012198319117)
                ·
                  refine ⟨7052384302436629574369669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18806358139831012198319117 7052384302436629574369669)
                  ·
                    refine ⟨1322322056706868045194313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7052384302436629574369669 1322322056706868045194313)
                    ·
                      rfl

theorem cell23_7725639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_7725639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725639 prefixEnd_7725639 := by exact prefixLift 7725639
  have htrace : WordTrace (prefixWord ++ tailWord_7725639) baseStart_7725639 baseEnd_7725639 := by
    simpa [prefixWord, tailWord_7725639, baseEnd_7725639] using wordTrace_append hprefix tailTrace_7725639
  have hstable : (prefixWord ++ tailWord_7725639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725639).length < 2 ^ (prefixWord ++ tailWord_7725639).sum := by decide
  have hdescent : baseEnd_7725639 < baseStart_7725639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725675 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 5]
def baseStart_7725675 : Nat := 118140960795 + 7725675 * 2 ^ 59
def prefixEnd_7725675 : Nat := 4983230072969 + 3 ^ 40 * 7725675 * 2
def baseEnd_7725675 : Nat := 3966984655424165994732773

theorem tailTrace_7725675 : CollatzResearch.WordTrace tailWord_7725675 prefixEnd_7725675 3966984655424165994732773 := by
  unfold tailWord_7725675
  simp only [CollatzResearch.WordTrace]
  refine ⟨281778516286206390089106479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187852344190804260059404319 281778516286206390089106479)
  ·
    refine ⟨422667774429309585133659719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281778516286206390089106479 422667774429309585133659719)
    ·
      refine ⟨634001661643964377700489579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422667774429309585133659719 634001661643964377700489579)
      ·
        refine ⟨951002492465946566550734369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634001661643964377700489579 951002492465946566550734369)
        ·
          refine ⟨713251869349459924913050777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951002492465946566550734369 713251869349459924913050777)
          ·
            refine ⟨534938902012094943684788083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713251869349459924913050777 534938902012094943684788083)
            ·
              refine ⟨802408353018142415527182125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534938902012094943684788083 802408353018142415527182125)
              ·
                refine ⟨300903132381803405822693297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 802408353018142415527182125 300903132381803405822693297)
                ·
                  refine ⟨225677349286352554367019973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300903132381803405822693297 225677349286352554367019973)
                  ·
                    refine ⟨42314502991191103943816245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 225677349286352554367019973 42314502991191103943816245)
                    ·
                      refine ⟨3966984655424165994732773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42314502991191103943816245 3966984655424165994732773)
                      ·
                        rfl

theorem cell23_7725675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 5].length) (baseStart_7725675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725675 prefixEnd_7725675 := by exact prefixLift 7725675
  have htrace : WordTrace (prefixWord ++ tailWord_7725675) baseStart_7725675 baseEnd_7725675 := by
    simpa [prefixWord, tailWord_7725675, baseEnd_7725675] using wordTrace_append hprefix tailTrace_7725675
  have hstable : (prefixWord ++ tailWord_7725675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725675).length < 2 ^ (prefixWord ++ tailWord_7725675).sum := by decide
  have hdescent : baseEnd_7725675 < baseStart_7725675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725686 : List Nat := [5, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_7725686 : Nat := 118140960795 + 7725686 * 2 ^ 59
def prefixEnd_7725686 : Nat := 4983230072969 + 3 ^ 40 * 7725686 * 2
def baseEnd_7725686 : Nat := 440776700412373939077247

theorem tailTrace_7725686 : CollatzResearch.WordTrace tailWord_7725686 prefixEnd_7725686 440776700412373939077247 := by
  unfold tailWord_7725686
  simp only [CollatzResearch.WordTrace]
  refine ⟨17611182343072908685484807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187852611659444359311837941 17611182343072908685484807)
  ·
    refine ⟨26416773514609363028227211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17611182343072908685484807 26416773514609363028227211)
    ·
      refine ⟨39625160271914044542340817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26416773514609363028227211 39625160271914044542340817)
      ·
        refine ⟨29718870203935533406755613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39625160271914044542340817 29718870203935533406755613)
        ·
          refine ⟨11144576326475825027533355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29718870203935533406755613 11144576326475825027533355)
          ·
            refine ⟨16716864489713737541300033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11144576326475825027533355 16716864489713737541300033)
            ·
              refine ⟨12537648367285303155975025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16716864489713737541300033 12537648367285303155975025)
              ·
                refine ⟨9403236275463977366981269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12537648367285303155975025 9403236275463977366981269)
                ·
                  refine ⟨440776700412373939077247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9403236275463977366981269 440776700412373939077247)
                  ·
                    rfl

theorem cell23_7725686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_7725686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725686 prefixEnd_7725686 := by exact prefixLift 7725686
  have htrace : WordTrace (prefixWord ++ tailWord_7725686) baseStart_7725686 baseEnd_7725686 := by
    simpa [prefixWord, tailWord_7725686, baseEnd_7725686] using wordTrace_append hprefix tailTrace_7725686
  have hstable : (prefixWord ++ tailWord_7725686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725686).length < 2 ^ (prefixWord ++ tailWord_7725686).sum := by decide
  have hdescent : baseEnd_7725686 < baseStart_7725686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725712 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 8, 4]
def baseStart_7725712 : Nat := 118140960795 + 7725712 * 2 ^ 59
def prefixEnd_7725712 : Nat := 4983230072969 + 3 ^ 40 * 7725712 * 2
def baseEnd_7725712 : Nat := 1322334551402794116656701

theorem tailTrace_7725712 : CollatzResearch.WordTrace tailWord_7725712 prefixEnd_7725712 1322334551402794116656701 := by
  unfold tailWord_7725712
  simp only [CollatzResearch.WordTrace]
  refine ⟨140889932893536172704101695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187853243858048230272135593 140889932893536172704101695)
  ·
    refine ⟨211334899340304259056152543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140889932893536172704101695 211334899340304259056152543)
    ·
      refine ⟨317002349010456388584228815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211334899340304259056152543 317002349010456388584228815)
      ·
        refine ⟨475503523515684582876343223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317002349010456388584228815 475503523515684582876343223)
        ·
          refine ⟨713255285273526874314514835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475503523515684582876343223 713255285273526874314514835)
          ·
            refine ⟨1069882927910290311471772253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713255285273526874314514835 1069882927910290311471772253)
            ·
              refine ⟨401206097966358866801914595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1069882927910290311471772253 401206097966358866801914595)
              ·
                refine ⟨601809146949538300202871893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401206097966358866801914595 601809146949538300202871893)
                ·
                  refine ⟨7052450940814901955502405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 601809146949538300202871893 7052450940814901955502405)
                  ·
                    refine ⟨1322334551402794116656701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7052450940814901955502405 1322334551402794116656701)
                    ·
                      rfl

theorem cell23_7725712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 8, 4].length) (baseStart_7725712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725712 prefixEnd_7725712 := by exact prefixLift 7725712
  have htrace : WordTrace (prefixWord ++ tailWord_7725712) baseStart_7725712 baseEnd_7725712 := by
    simpa [prefixWord, tailWord_7725712, baseEnd_7725712] using wordTrace_append hprefix tailTrace_7725712
  have hstable : (prefixWord ++ tailWord_7725712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725712).length < 2 ^ (prefixWord ++ tailWord_7725712).sum := by decide
  have hdescent : baseEnd_7725712 < baseStart_7725712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725719 : List Nat := [1, 1, 3, 3, 2, 1, 2, 4, 1, 1, 4]
def baseStart_7725719 : Nat := 118140960795 + 7725719 * 2 ^ 59
def prefixEnd_7725719 : Nat := 4983230072969 + 3 ^ 40 * 7725719 * 2
def baseEnd_7725719 : Nat := 3967007248572963822582571

theorem tailTrace_7725719 : CollatzResearch.WordTrace tailWord_7725719 prefixEnd_7725719 3967007248572963822582571 := by
  unfold tailWord_7725719
  simp only [CollatzResearch.WordTrace]
  refine ⟨281780121098046985603708211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187853414065364657069138807 281780121098046985603708211)
  ·
    refine ⟨422670181647070478405562317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281780121098046985603708211 422670181647070478405562317)
    ·
      refine ⟨158501318117651429402085869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422670181647070478405562317 158501318117651429402085869)
      ·
        refine ⟨59437994294119286025782201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158501318117651429402085869 59437994294119286025782201)
        ·
          refine ⟨44578495720589464519336651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59437994294119286025782201 44578495720589464519336651)
          ·
            refine ⟨66867743580884196779004977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44578495720589464519336651 66867743580884196779004977)
            ·
              refine ⟨50150807685663147584253733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66867743580884196779004977 50150807685663147584253733)
              ·
                refine ⟨9403276441061840172047575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50150807685663147584253733 9403276441061840172047575)
                ·
                  refine ⟨14104914661592760258071363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9403276441061840172047575 14104914661592760258071363)
                  ·
                    refine ⟨21157371992389140387107045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14104914661592760258071363 21157371992389140387107045)
                    ·
                      refine ⟨3967007248572963822582571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21157371992389140387107045 3967007248572963822582571)
                      ·
                        rfl

theorem cell23_7725719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_7725719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725719 prefixEnd_7725719 := by exact prefixLift 7725719
  have htrace : WordTrace (prefixWord ++ tailWord_7725719) baseStart_7725719 baseEnd_7725719 := by
    simpa [prefixWord, tailWord_7725719, baseEnd_7725719] using wordTrace_append hprefix tailTrace_7725719
  have hstable : (prefixWord ++ tailWord_7725719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725719).length < 2 ^ (prefixWord ++ tailWord_7725719).sum := by decide
  have hdescent : baseEnd_7725719 < baseStart_7725719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725752 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 2, 7, 3]
def baseStart_7725752 : Nat := 118140960795 + 7725752 * 2 ^ 59
def prefixEnd_7725752 : Nat := 4983230072969 + 3 ^ 40 * 7725752 * 2
def baseEnd_7725752 : Nat := 3967024193434562193469919

theorem tailTrace_7725752 : CollatzResearch.WordTrace tailWord_7725752 prefixEnd_7725752 3967024193434562193469919 := by
  unfold tailWord_7725752
  simp only [CollatzResearch.WordTrace]
  refine ⟨140890662353463716119829755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187854216471284954826439673 140890662353463716119829755)
  ·
    refine ⟨211335993530195574179744633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140890662353463716119829755 211335993530195574179744633)
    ·
      refine ⟨158501995147646680634808475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211335993530195574179744633 158501995147646680634808475)
      ·
        refine ⟨237752992721470020952212713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158501995147646680634808475 237752992721470020952212713)
        ·
          refine ⟨178314744541102515714159535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237752992721470020952212713 178314744541102515714159535)
          ·
            refine ⟨267472116811653773571239303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178314744541102515714159535 267472116811653773571239303)
            ·
              refine ⟨401208175217480660356858955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267472116811653773571239303 401208175217480660356858955)
              ·
                refine ⟨601812262826220990535288433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401208175217480660356858955 601812262826220990535288433)
                ·
                  refine ⟨451359197119665742901466325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601812262826220990535288433 451359197119665742901466325)
                  ·
                    refine ⟨10578731182492165849253117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 451359197119665742901466325 10578731182492165849253117)
                    ·
                      refine ⟨3967024193434562193469919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10578731182492165849253117 3967024193434562193469919)
                      ·
                        rfl

theorem cell23_7725752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_7725752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725752 prefixEnd_7725752 := by exact prefixLift 7725752
  have htrace : WordTrace (prefixWord ++ tailWord_7725752) baseStart_7725752 baseEnd_7725752 := by
    simpa [prefixWord, tailWord_7725752, baseEnd_7725752] using wordTrace_append hprefix tailTrace_7725752
  have hstable : (prefixWord ++ tailWord_7725752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725752).length < 2 ^ (prefixWord ++ tailWord_7725752).sum := by decide
  have hdescent : baseEnd_7725752 < baseStart_7725752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725792 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 4]
def baseStart_7725792 : Nat := 118140960795 + 7725792 * 2 ^ 59
def prefixEnd_7725792 : Nat := 4983230072969 + 3 ^ 40 * 7725792 * 2
def baseEnd_7725792 : Nat := 3967044732660742036969735

theorem tailTrace_7725792 : CollatzResearch.WordTrace tailWord_7725792 prefixEnd_7725792 3967044732660742036969735 := by
  unfold tailWord_7725792
  simp only [CollatzResearch.WordTrace]
  refine ⟨140891391813391259535557815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187855189084521679380743753 140891391813391259535557815)
  ·
    refine ⟨211337087720086889303336723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140891391813391259535557815 211337087720086889303336723)
    ·
      refine ⟨317005631580130333955005085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211337087720086889303336723 317005631580130333955005085)
      ·
        refine ⟨118877111842548875233126907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317005631580130333955005085 118877111842548875233126907)
        ·
          refine ⟨178315667763823312849690361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118877111842548875233126907 178315667763823312849690361)
          ·
            refine ⟨133736750822867484637267771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178315667763823312849690361 133736750822867484637267771)
            ·
              refine ⟨200605126234301226955901657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133736750822867484637267771 200605126234301226955901657)
              ·
                refine ⟨150453844675725920216926243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200605126234301226955901657 150453844675725920216926243)
                ·
                  refine ⟨225680767013588880325389365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150453844675725920216926243 225680767013588880325389365)
                  ·
                    refine ⟨21157571907523957530505253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 225680767013588880325389365 21157571907523957530505253)
                    ·
                      refine ⟨3967044732660742036969735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21157571907523957530505253 3967044732660742036969735)
                      ·
                        rfl

theorem cell23_7725792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_7725792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725792 prefixEnd_7725792 := by exact prefixLift 7725792
  have htrace : WordTrace (prefixWord ++ tailWord_7725792) baseStart_7725792 baseEnd_7725792 := by
    simpa [prefixWord, tailWord_7725792, baseEnd_7725792] using wordTrace_append hprefix tailTrace_7725792
  have hstable : (prefixWord ++ tailWord_7725792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725792).length < 2 ^ (prefixWord ++ tailWord_7725792).sum := by decide
  have hdescent : baseEnd_7725792 < baseStart_7725792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725820 : List Nat := [2, 2, 2, 1, 3, 4, 2, 1, 2, 1, 3]
def baseStart_7725820 : Nat := 118140960795 + 7725820 * 2 ^ 59
def prefixEnd_7725820 : Nat := 4983230072969 + 3 ^ 40 * 7725820 * 2
def baseEnd_7725820 : Nat := 3967059110119067927419607

theorem tailTrace_7725820 : CollatzResearch.WordTrace tailWord_7725820 prefixEnd_7725820 3967059110119067927419607 := by
  unfold tailWord_7725820
  simp only [CollatzResearch.WordTrace]
  refine ⟨140891902435340539926567457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187855869913787386568756609 140891902435340539926567457)
  ·
    refine ⟨105668926826505404944925593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140891902435340539926567457 105668926826505404944925593)
    ·
      refine ⟨79251695119879053708694195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105668926826505404944925593 79251695119879053708694195)
      ·
        refine ⟨118877542679818580563041293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79251695119879053708694195 118877542679818580563041293)
        ·
          refine ⟨44579078504931967711140485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118877542679818580563041293 44579078504931967711140485)
          ·
            refine ⟨8358577219674743945838841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44579078504931967711140485 8358577219674743945838841)
            ·
              refine ⟨6268932914756057959379131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8358577219674743945838841 6268932914756057959379131)
              ·
                refine ⟨9403399372134086939068697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268932914756057959379131 9403399372134086939068697)
                ·
                  refine ⟨7052549529100565204301523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9403399372134086939068697 7052549529100565204301523)
                  ·
                    refine ⟨10578824293650847806452285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7052549529100565204301523 10578824293650847806452285)
                    ·
                      refine ⟨3967059110119067927419607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10578824293650847806452285 3967059110119067927419607)
                      ·
                        rfl

theorem cell23_7725820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_7725820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725820 prefixEnd_7725820 := by exact prefixLift 7725820
  have htrace : WordTrace (prefixWord ++ tailWord_7725820) baseStart_7725820 baseEnd_7725820 := by
    simpa [prefixWord, tailWord_7725820, baseEnd_7725820] using wordTrace_append hprefix tailTrace_7725820
  have hstable : (prefixWord ++ tailWord_7725820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725820).length < 2 ^ (prefixWord ++ tailWord_7725820).sum := by decide
  have hdescent : baseEnd_7725820 < baseStart_7725820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725859 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 3]
def baseStart_7725859 : Nat := 118140960795 + 7725859 * 2 ^ 59
def prefixEnd_7725859 : Nat := 4983230072969 + 3 ^ 40 * 7725859 * 2
def baseEnd_7725859 : Nat := 3967079135864593274831927

theorem tailTrace_7725859 : CollatzResearch.WordTrace tailWord_7725859 prefixEnd_7725859 3967079135864593274831927 := by
  unfold tailWord_7725859
  simp only [CollatzResearch.WordTrace]
  refine ⟨281785227317539789513804631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187856818211693193009203087 281785227317539789513804631)
  ·
    refine ⟨422677840976309684270706947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281785227317539789513804631 422677840976309684270706947)
    ·
      refine ⟨634016761464464526406060421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422677840976309684270706947 634016761464464526406060421)
      ·
        refine ⟨118878142774587098701136329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 634016761464464526406060421 118878142774587098701136329)
        ·
          refine ⟨89158607080940324025852247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118878142774587098701136329 89158607080940324025852247)
          ·
            refine ⟨133737910621410486038778371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89158607080940324025852247 133737910621410486038778371)
            ·
              refine ⟨200606865932115729058167557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133737910621410486038778371 200606865932115729058167557)
              ·
                refine ⟨37613787362271699198406417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200606865932115729058167557 37613787362271699198406417)
                ·
                  refine ⟨28210340521703774398804813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37613787362271699198406417 28210340521703774398804813)
                  ·
                    refine ⟨10578877695638915399551805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28210340521703774398804813 10578877695638915399551805)
                    ·
                      refine ⟨3967079135864593274831927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10578877695638915399551805 3967079135864593274831927)
                      ·
                        rfl

theorem cell23_7725859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_7725859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725859 prefixEnd_7725859 := by exact prefixLift 7725859
  have htrace : WordTrace (prefixWord ++ tailWord_7725859) baseStart_7725859 baseEnd_7725859 := by
    simpa [prefixWord, tailWord_7725859, baseEnd_7725859] using wordTrace_append hprefix tailTrace_7725859
  have hstable : (prefixWord ++ tailWord_7725859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725859).length < 2 ^ (prefixWord ++ tailWord_7725859).sum := by decide
  have hdescent : baseEnd_7725859 < baseStart_7725859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725939 : List Nat := [1, 1, 1, 2, 2, 1, 4, 5, 6]
def baseStart_7725939 : Nat := 118140960795 + 7725939 * 2 ^ 59
def prefixEnd_7725939 : Nat := 4983230072969 + 3 ^ 40 * 7725939 * 2
def baseEnd_7725939 : Nat := 440791134924105884647951

theorem tailTrace_7725939 : CollatzResearch.WordTrace tailWord_7725939 prefixEnd_7725939 440791134924105884647951 := by
  unfold tailWord_7725939
  simp only [CollatzResearch.WordTrace]
  refine ⟨281788145157249963176716871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187858763438166642117811247 281788145157249963176716871)
  ·
    refine ⟨422682217735874944765075307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281788145157249963176716871 422682217735874944765075307)
    ·
      refine ⟨634023326603812417147612961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422682217735874944765075307 634023326603812417147612961)
      ·
        refine ⟨475517494952859312860709721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634023326603812417147612961 475517494952859312860709721)
        ·
          refine ⟨356638121214644484645532291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475517494952859312860709721 356638121214644484645532291)
          ·
            refine ⟨534957181821966726968298437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356638121214644484645532291 534957181821966726968298437)
            ·
              refine ⟨100304471591618761306555957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 534957181821966726968298437 100304471591618761306555957)
              ·
                refine ⟨9403544211714258872489621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100304471591618761306555957 9403544211714258872489621)
                ·
                  refine ⟨440791134924105884647951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9403544211714258872489621 440791134924105884647951)
                  ·
                    rfl

theorem cell23_7725939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 6].length) (baseStart_7725939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725939 prefixEnd_7725939 := by exact prefixLift 7725939
  have htrace : WordTrace (prefixWord ++ tailWord_7725939) baseStart_7725939 baseEnd_7725939 := by
    simpa [prefixWord, tailWord_7725939, baseEnd_7725939] using wordTrace_append hprefix tailTrace_7725939
  have hstable : (prefixWord ++ tailWord_7725939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725939).length < 2 ^ (prefixWord ++ tailWord_7725939).sum := by decide
  have hdescent : baseEnd_7725939 < baseStart_7725939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725960 : List Nat := [2, 1, 3, 3, 2, 1, 3, 3, 1, 4]
def baseStart_7725960 : Nat := 118140960795 + 7725960 * 2 ^ 59
def prefixEnd_7725960 : Nat := 4983230072969 + 3 ^ 40 * 7725960 * 2
def baseEnd_7725960 : Nat := 1322376999136899126556321

theorem tailTrace_7725960 : CollatzResearch.WordTrace tailWord_7725960 prefixEnd_7725960 1322376999136899126556321 := by
  unfold tailWord_7725960
  simp only [CollatzResearch.WordTrace]
  refine ⟨140894455545086941881615667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187859274060115922508820889 140894455545086941881615667)
  ·
    refine ⟨211341683317630412822423501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140894455545086941881615667 211341683317630412822423501)
    ·
      refine ⟨79253131244111404808408813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211341683317630412822423501 79253131244111404808408813)
      ·
        refine ⟨29719924216541776803153305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79253131244111404808408813 29719924216541776803153305)
        ·
          refine ⟨22289943162406332602364979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29719924216541776803153305 22289943162406332602364979)
          ·
            refine ⟨33434914743609498903547469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22289943162406332602364979 33434914743609498903547469)
            ·
              refine ⟨12538093028853562088830301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33434914743609498903547469 12538093028853562088830301)
              ·
                refine ⟨4701784885820085783311363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12538093028853562088830301 4701784885820085783311363)
                ·
                  refine ⟨7052677328730128674967045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4701784885820085783311363 7052677328730128674967045)
                  ·
                    refine ⟨1322376999136899126556321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7052677328730128674967045 1322376999136899126556321)
                    ·
                      rfl

theorem cell23_7725960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_7725960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725960 prefixEnd_7725960 := by exact prefixLift 7725960
  have htrace : WordTrace (prefixWord ++ tailWord_7725960) baseStart_7725960 baseEnd_7725960 := by
    simpa [prefixWord, tailWord_7725960, baseEnd_7725960] using wordTrace_append hprefix tailTrace_7725960
  have hstable : (prefixWord ++ tailWord_7725960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725960).length < 2 ^ (prefixWord ++ tailWord_7725960).sum := by decide
  have hdescent : baseEnd_7725960 < baseStart_7725960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725969 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 5, 5]
def baseStart_7725969 : Nat := 118140960795 + 7725969 * 2 ^ 59
def prefixEnd_7725969 : Nat := 4983230072969 + 3 ^ 40 * 7725969 * 2
def baseEnd_7725969 : Nat := 1322378539578862614818807

theorem tailTrace_7725969 : CollatzResearch.WordTrace tailWord_7725969 prefixEnd_7725969 1322378539578862614818807 := by
  unfold tailWord_7725969
  simp only [CollatzResearch.WordTrace]
  refine ⟨281789239347141278300308961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187859492898094185533539307 281789239347141278300308961)
  ·
    refine ⟨211341929510355958725231721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281789239347141278300308961 211341929510355958725231721)
    ·
      refine ⟨158506447132766969043923791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211341929510355958725231721 158506447132766969043923791)
      ·
        refine ⟨237759670699150453565885687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158506447132766969043923791 237759670699150453565885687)
        ·
          refine ⟨356639506048725680348828531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237759670699150453565885687 356639506048725680348828531)
          ·
            refine ⟨534959259073088520523242797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356639506048725680348828531 534959259073088520523242797)
            ·
              refine ⟨200609722152408195196216049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 534959259073088520523242797 200609722152408195196216049)
              ·
                refine ⟨150457291614306146397162037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200609722152408195196216049 150457291614306146397162037)
                ·
                  refine ⟨14105371088841201224733941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150457291614306146397162037 14105371088841201224733941)
                  ·
                    refine ⟨1322378539578862614818807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14105371088841201224733941 1322378539578862614818807)
                    ·
                      rfl

theorem cell23_7725969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_7725969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725969 prefixEnd_7725969 := by exact prefixLift 7725969
  have htrace : WordTrace (prefixWord ++ tailWord_7725969) baseStart_7725969 baseEnd_7725969 := by
    simpa [prefixWord, tailWord_7725969, baseEnd_7725969] using wordTrace_append hprefix tailTrace_7725969
  have hstable : (prefixWord ++ tailWord_7725969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725969).length < 2 ^ (prefixWord ++ tailWord_7725969).sum := by decide
  have hdescent : baseEnd_7725969 < baseStart_7725969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725970 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_7725970 : Nat := 118140960795 + 7725970 * 2 ^ 59
def prefixEnd_7725970 : Nat := 4983230072969 + 3 ^ 40 * 7725970 * 2
def baseEnd_7725970 : Nat := 3967136132217242340543917

theorem tailTrace_7725970 : CollatzResearch.WordTrace tailWord_7725970 prefixEnd_7725970 3967136132217242340543917 := by
  unfold tailWord_7725970
  simp only [CollatzResearch.WordTrace]
  refine ⟨70447318955034413867773841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187859517213425103647396909 70447318955034413867773841)
  ·
    refine ⟨52835489216275810400830381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70447318955034413867773841 52835489216275810400830381)
    ·
      refine ⟨19813308456103428900311393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52835489216275810400830381 19813308456103428900311393)
      ·
        refine ⟨14859981342077571675233545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19813308456103428900311393 14859981342077571675233545)
        ·
          refine ⟨11144986006558178756425159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14859981342077571675233545 11144986006558178756425159)
          ·
            refine ⟨16717479009837268134637739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11144986006558178756425159 16717479009837268134637739)
            ·
              refine ⟨25076218514755902201956609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16717479009837268134637739 25076218514755902201956609)
              ·
                refine ⟨18807163886066926651467457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25076218514755902201956609 18807163886066926651467457)
                ·
                  refine ⟨14105372914550194988600593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18807163886066926651467457 14105372914550194988600593)
                  ·
                    refine ⟨10579029685912646241450445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14105372914550194988600593 10579029685912646241450445)
                    ·
                      refine ⟨3967136132217242340543917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10579029685912646241450445 3967136132217242340543917)
                      ·
                        rfl

theorem cell23_7725970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_7725970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725970 prefixEnd_7725970 := by exact prefixLift 7725970
  have htrace : WordTrace (prefixWord ++ tailWord_7725970) baseStart_7725970 baseEnd_7725970 := by
    simpa [prefixWord, tailWord_7725970, baseEnd_7725970] using wordTrace_append hprefix tailTrace_7725970
  have hstable : (prefixWord ++ tailWord_7725970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725970).length < 2 ^ (prefixWord ++ tailWord_7725970).sum := by decide
  have hdescent : baseEnd_7725970 < baseStart_7725970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7725989 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_7725989 : Nat := 118140960795 + 7725989 * 2 ^ 59
def prefixEnd_7725989 : Nat := 4983230072969 + 3 ^ 40 * 7725989 * 2
def baseEnd_7725989 : Nat := 3967145888349677766206329

theorem tailTrace_7725989 : CollatzResearch.WordTrace tailWord_7725989 prefixEnd_7725989 3967145888349677766206329 := by
  unfold tailWord_7725989
  simp only [CollatzResearch.WordTrace]
  refine ⟨281789968807068821716037021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187859979204712547810691347 281789968807068821716037021)
  ·
    refine ⟨105671238302650808143513883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281789968807068821716037021 105671238302650808143513883)
    ·
      refine ⟨158506857453976212215270825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105671238302650808143513883 158506857453976212215270825)
      ·
        refine ⟨118880143090482159161453119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158506857453976212215270825 118880143090482159161453119)
        ·
          refine ⟨178320214635723238742179679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118880143090482159161453119 178320214635723238742179679)
          ·
            refine ⟨267480321953584858113269519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178320214635723238742179679 267480321953584858113269519)
            ·
              refine ⟨401220482930377287169904279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267480321953584858113269519 401220482930377287169904279)
              ·
                refine ⟨601830724395565930754856419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401220482930377287169904279 601830724395565930754856419)
                ·
                  refine ⟨902746086593348896132284629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601830724395565930754856419 902746086593348896132284629)
                  ·
                    refine ⟨21158111404531614753100421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 902746086593348896132284629 21158111404531614753100421)
                    ·
                      refine ⟨3967145888349677766206329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21158111404531614753100421 3967145888349677766206329)
                      ·
                        rfl

theorem cell23_7725989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_7725989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7725989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7725989 prefixEnd_7725989 := by exact prefixLift 7725989
  have htrace : WordTrace (prefixWord ++ tailWord_7725989) baseStart_7725989 baseEnd_7725989 := by
    simpa [prefixWord, tailWord_7725989, baseEnd_7725989] using wordTrace_append hprefix tailTrace_7725989
  have hstable : (prefixWord ++ tailWord_7725989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7725989).length < 2 ^ (prefixWord ++ tailWord_7725989).sum := by decide
  have hdescent : baseEnd_7725989 < baseStart_7725989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7725989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726016 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 1, 6]
def baseStart_7726016 : Nat := 118140960795 + 7726016 * 2 ^ 59
def prefixEnd_7726016 : Nat := 4983230072969 + 3 ^ 40 * 7726016 * 2
def baseEnd_7726016 : Nat := 1322386584109116386856235

theorem tailTrace_7726016 : CollatzResearch.WordTrace tailWord_7726016 prefixEnd_7726016 1322386584109116386856235 := by
  unfold tailWord_7726016
  simp only [CollatzResearch.WordTrace]
  refine ⟨140895476788985502663634951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187860635718647336884846601 140895476788985502663634951)
  ·
    refine ⟨211343215183478253995452427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140895476788985502663634951 211343215183478253995452427)
    ·
      refine ⟨317014822775217380993178641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211343215183478253995452427 317014822775217380993178641)
      ·
        refine ⟨237761117081413035744883981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317014822775217380993178641 237761117081413035744883981)
        ·
          refine ⟨89160418905529888404331493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237761117081413035744883981 89160418905529888404331493)
          ·
            refine ⟨16717578544786854075812155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89160418905529888404331493 16717578544786854075812155)
            ·
              refine ⟨25076367817180281113718233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16717578544786854075812155 25076367817180281113718233)
              ·
                refine ⟨18807275862885210835288675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25076367817180281113718233 18807275862885210835288675)
                ·
                  refine ⟨28210913794327816252933013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18807275862885210835288675 28210913794327816252933013)
                  ·
                    refine ⟨1322386584109116386856235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28210913794327816252933013 1322386584109116386856235)
                    ·
                      rfl

theorem cell23_7726016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 1, 6].length) (baseStart_7726016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726016 prefixEnd_7726016 := by exact prefixLift 7726016
  have htrace : WordTrace (prefixWord ++ tailWord_7726016) baseStart_7726016 baseEnd_7726016 := by
    simpa [prefixWord, tailWord_7726016, baseEnd_7726016] using wordTrace_append hprefix tailTrace_7726016
  have hstable : (prefixWord ++ tailWord_7726016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726016).length < 2 ^ (prefixWord ++ tailWord_7726016).sum := by decide
  have hdescent : baseEnd_7726016 < baseStart_7726016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726033 : List Nat := [1, 2, 2, 1, 2, 1, 6, 2, 2, 4]
def baseStart_7726033 : Nat := 118140960795 + 7726033 * 2 ^ 59
def prefixEnd_7726033 : Nat := 4983230072969 + 3 ^ 40 * 7726033 * 2
def baseEnd_7726033 : Nat := 1322389493832825198018709

theorem tailTrace_7726033 : CollatzResearch.WordTrace tailWord_7726033 prefixEnd_7726033 1322389493832825198018709 := by
  unfold tailWord_7726033
  simp only [CollatzResearch.WordTrace]
  refine ⟨281791573618909417230638753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187861049079272944820425835 281791573618909417230638753)
  ·
    refine ⟨211343680214182062922979065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281791573618909417230638753 211343680214182062922979065)
    ·
      refine ⟨158507760160636547192234299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211343680214182062922979065 158507760160636547192234299)
      ·
        refine ⟨237761640240954820788351449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158507760160636547192234299 237761640240954820788351449)
        ·
          refine ⟨178321230180716115591263587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237761640240954820788351449 178321230180716115591263587)
          ·
            refine ⟨267481845271074173386895381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178321230180716115591263587 267481845271074173386895381)
            ·
              refine ⟨12538211497081601877510721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 267481845271074173386895381 12538211497081601877510721)
              ·
                refine ⟨9403658622811201408133041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12538211497081601877510721 9403658622811201408133041)
                ·
                  refine ⟨7052743967108401056099781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9403658622811201408133041 7052743967108401056099781)
                  ·
                    refine ⟨1322389493832825198018709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7052743967108401056099781 1322389493832825198018709)
                    ·
                      rfl

theorem cell23_7726033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_7726033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726033 prefixEnd_7726033 := by exact prefixLift 7726033
  have htrace : WordTrace (prefixWord ++ tailWord_7726033) baseStart_7726033 baseEnd_7726033 := by
    simpa [prefixWord, tailWord_7726033, baseEnd_7726033] using wordTrace_append hprefix tailTrace_7726033
  have hstable : (prefixWord ++ tailWord_7726033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726033).length < 2 ^ (prefixWord ++ tailWord_7726033).sum := by decide
  have hdescent : baseEnd_7726033 < baseStart_7726033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726034 : List Nat := [3, 2, 2, 3, 1, 1, 4, 2, 1, 1, 3]
def baseStart_7726034 : Nat := 118140960795 + 7726034 * 2 ^ 59
def prefixEnd_7726034 : Nat := 4983230072969 + 3 ^ 40 * 7726034 * 2
def baseEnd_7726034 : Nat := 3967168994979130090143623

theorem tailTrace_7726034 : CollatzResearch.WordTrace tailWord_7726034 prefixEnd_7726034 3967168994979130090143623 := by
  unfold tailWord_7726034
  simp only [CollatzResearch.WordTrace]
  refine ⟨70447902522976448600356289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187861073394603862934283437 70447902522976448600356289)
  ·
    refine ⟨52835926892232336450267217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70447902522976448600356289 52835926892232336450267217)
    ·
      refine ⟨39626945169174252337700413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52835926892232336450267217 39626945169174252337700413)
      ·
        refine ⟨14860104438440344626637655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39626945169174252337700413 14860104438440344626637655)
        ·
          refine ⟨22290156657660516939956483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14860104438440344626637655 22290156657660516939956483)
          ·
            refine ⟨33435234986490775409934725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22290156657660516939956483 33435234986490775409934725)
            ·
              refine ⟨6269106559967020389362761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33435234986490775409934725 6269106559967020389362761)
              ·
                refine ⟨4701829919975265292022071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6269106559967020389362761 4701829919975265292022071)
                ·
                  refine ⟨7052744879962897938033107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4701829919975265292022071 7052744879962897938033107)
                  ·
                    refine ⟨10579117319944346907049661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7052744879962897938033107 10579117319944346907049661)
                    ·
                      refine ⟨3967168994979130090143623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10579117319944346907049661 3967168994979130090143623)
                      ·
                        rfl

theorem cell23_7726034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_7726034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726034 prefixEnd_7726034 := by exact prefixLift 7726034
  have htrace : WordTrace (prefixWord ++ tailWord_7726034) baseStart_7726034 baseEnd_7726034 := by
    simpa [prefixWord, tailWord_7726034, baseEnd_7726034] using wordTrace_append hprefix tailTrace_7726034
  have hstable : (prefixWord ++ tailWord_7726034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726034).length < 2 ^ (prefixWord ++ tailWord_7726034).sum := by decide
  have hdescent : baseEnd_7726034 < baseStart_7726034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726039 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_7726039 : Nat := 118140960795 + 7726039 * 2 ^ 59
def prefixEnd_7726039 : Nat := 4983230072969 + 3 ^ 40 * 7726039 * 2
def baseEnd_7726039 : Nat := 3967171562382402570581099

theorem tailTrace_7726039 : CollatzResearch.WordTrace tailWord_7726039 prefixEnd_7726039 3967171562382402570581099 := by
  unfold tailWord_7726039
  simp only [CollatzResearch.WordTrace]
  refine ⟨281791792456887680255357171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187861194971258453503571447 281791792456887680255357171)
  ·
    refine ⟨422687688685331520383035757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281791792456887680255357171 422687688685331520383035757)
    ·
      refine ⟨158507883256999320143638409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422687688685331520383035757 158507883256999320143638409)
      ·
        refine ⟨118880912442749490107728807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158507883256999320143638409 118880912442749490107728807)
        ·
          refine ⟨178321368664124235161593211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118880912442749490107728807 178321368664124235161593211)
          ·
            refine ⟨267482052996186352742389817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178321368664124235161593211 267482052996186352742389817)
            ·
              refine ⟨200611539747139764556792363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267482052996186352742389817 200611539747139764556792363)
              ·
                refine ⟨300917309620709646835188545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200611539747139764556792363 300917309620709646835188545)
                ·
                  refine ⟨225687982215532235126391409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300917309620709646835188545 225687982215532235126391409)
                  ·
                    refine ⟨169265986661649176344793557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 225687982215532235126391409 169265986661649176344793557)
                    ·
                      refine ⟨3967171562382402570581099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169265986661649176344793557 3967171562382402570581099)
                      ·
                        rfl

theorem cell23_7726039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_7726039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726039 prefixEnd_7726039 := by exact prefixLift 7726039
  have htrace : WordTrace (prefixWord ++ tailWord_7726039) baseStart_7726039 baseEnd_7726039 := by
    simpa [prefixWord, tailWord_7726039, baseEnd_7726039] using wordTrace_append hprefix tailTrace_7726039
  have hstable : (prefixWord ++ tailWord_7726039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726039).length < 2 ^ (prefixWord ++ tailWord_7726039).sum := by decide
  have hdescent : baseEnd_7726039 < baseStart_7726039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726050 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_7726050 : Nat := 118140960795 + 7726050 * 2 ^ 59
def prefixEnd_7726050 : Nat := 4983230072969 + 3 ^ 40 * 7726050 * 2
def baseEnd_7726050 : Nat := 1322392403556534009181183

theorem tailTrace_7726050 : CollatzResearch.WordTrace tailWord_7726050 prefixEnd_7726050 1322392403556534009181183 := by
  unfold tailWord_7726050
  simp only [CollatzResearch.WordTrace]
  refine ⟨70448048414961957283501901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187861462439898552756005069 70448048414961957283501901)
  ·
    refine ⟨26418018155610733981313213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70448048414961957283501901 26418018155610733981313213)
    ·
      refine ⟨9906756808354025242992455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26418018155610733981313213 9906756808354025242992455)
      ·
        refine ⟨14860135212531037864488683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9906756808354025242992455 14860135212531037864488683)
        ·
          refine ⟨22290202818796556796733025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14860135212531037864488683 22290202818796556796733025)
          ·
            refine ⟨16717652114097417597549769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22290202818796556796733025 16717652114097417597549769)
            ·
              refine ⟨12538239085573063198162327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16717652114097417597549769 12538239085573063198162327)
              ·
                refine ⟨18807358628359594797243491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12538239085573063198162327 18807358628359594797243491)
                ·
                  refine ⟨28211037942539392195865237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18807358628359594797243491 28211037942539392195865237)
                  ·
                    refine ⟨1322392403556534009181183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28211037942539392195865237 1322392403556534009181183)
                    ·
                      rfl

theorem cell23_7726050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_7726050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726050 prefixEnd_7726050 := by exact prefixLift 7726050
  have htrace : WordTrace (prefixWord ++ tailWord_7726050) baseStart_7726050 baseEnd_7726050 := by
    simpa [prefixWord, tailWord_7726050, baseEnd_7726050] using wordTrace_append hprefix tailTrace_7726050
  have hstable : (prefixWord ++ tailWord_7726050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726050).length < 2 ^ (prefixWord ++ tailWord_7726050).sum := by decide
  have hdescent : baseEnd_7726050 < baseStart_7726050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726073 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 4, 1, 3]
def baseStart_7726073 : Nat := 118140960795 + 7726073 * 2 ^ 59
def prefixEnd_7726073 : Nat := 4983230072969 + 3 ^ 40 * 7726073 * 2
def baseEnd_7726073 : Nat := 3967189020724655437555943

theorem tailTrace_7726073 : CollatzResearch.WordTrace tailWord_7726073 prefixEnd_7726073 3967189020724655437555943 := by
  unfold tailWord_7726073
  simp only [CollatzResearch.WordTrace]
  refine ⟨281793032538764504062094873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187862021692509669374729915 281793032538764504062094873)
  ·
    refine ⟨211344774404073378046571155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281793032538764504062094873 211344774404073378046571155)
    ·
      refine ⟨317017161606110067069856733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211344774404073378046571155 317017161606110067069856733)
      ·
        refine ⟨118881435602291275151196275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317017161606110067069856733 118881435602291275151196275)
        ·
          refine ⟨178322153403436912726794413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118881435602291275151196275 178322153403436912726794413)
          ·
            refine ⟨66870807526288842272547905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178322153403436912726794413 66870807526288842272547905)
            ·
              refine ⟨50153105644716631704410929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66870807526288842272547905 50153105644716631704410929)
              ·
                refine ⟨37614829233537473778308197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50153105644716631704410929 37614829233537473778308197)
                ·
                  refine ⟨7052780481288276333432787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37614829233537473778308197 7052780481288276333432787)
                  ·
                    refine ⟨10579170721932414500149181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7052780481288276333432787 10579170721932414500149181)
                    ·
                      refine ⟨3967189020724655437555943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10579170721932414500149181 3967189020724655437555943)
                      ·
                        rfl

theorem cell23_7726073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_7726073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726073 prefixEnd_7726073 := by exact prefixLift 7726073
  have htrace : WordTrace (prefixWord ++ tailWord_7726073) baseStart_7726073 baseEnd_7726073 := by
    simpa [prefixWord, tailWord_7726073, baseEnd_7726073] using wordTrace_append hprefix tailTrace_7726073
  have hstable : (prefixWord ++ tailWord_7726073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726073).length < 2 ^ (prefixWord ++ tailWord_7726073).sum := by decide
  have hdescent : baseEnd_7726073 < baseStart_7726073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726090 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 4, 1, 3]
def baseStart_7726090 : Nat := 118140960795 + 7726090 * 2 ^ 59
def prefixEnd_7726090 : Nat := 4983230072969 + 3 ^ 40 * 7726090 * 2
def baseEnd_7726090 : Nat := 3967197749895781871043365

theorem tailTrace_7726090 : CollatzResearch.WordTrace tailWord_7726090 prefixEnd_7726090 3967197749895781871043365 := by
  unfold tailWord_7726090
  simp only [CollatzResearch.WordTrace]
  refine ⟨70448413144925728991365931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187862435053135277310309149 70448413144925728991365931)
  ·
    refine ⟨105672619717388593487048897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70448413144925728991365931 105672619717388593487048897)
    ·
      refine ⟨79254464788041445115286673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105672619717388593487048897 79254464788041445115286673)
      ·
        refine ⟨59440848591031083836465005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79254464788041445115286673 59440848591031083836465005)
        ·
          refine ⟨22290318221636656438674377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59440848591031083836465005 22290318221636656438674377)
          ·
            refine ⟨16717738666227492329005783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22290318221636656438674377 16717738666227492329005783)
            ·
              refine ⟨25076607999341238493508675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16717738666227492329005783 25076607999341238493508675)
              ·
                refine ⟨37614911999011857740263013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25076607999341238493508675 37614911999011857740263013)
                ·
                  refine ⟨7052795999814723326299315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37614911999011857740263013 7052795999814723326299315)
                  ·
                    refine ⟨10579193999722084989448973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7052795999814723326299315 10579193999722084989448973)
                    ·
                      refine ⟨3967197749895781871043365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10579193999722084989448973 3967197749895781871043365)
                      ·
                        rfl

theorem cell23_7726090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_7726090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726090 prefixEnd_7726090 := by exact prefixLift 7726090
  have htrace : WordTrace (prefixWord ++ tailWord_7726090) baseStart_7726090 baseEnd_7726090 := by
    simpa [prefixWord, tailWord_7726090, baseEnd_7726090] using wordTrace_append hprefix tailTrace_7726090
  have hstable : (prefixWord ++ tailWord_7726090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726090).length < 2 ^ (prefixWord ++ tailWord_7726090).sum := by decide
  have hdescent : baseEnd_7726090 < baseStart_7726090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726106 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 2, 6]
def baseStart_7726106 : Nat := 118140960795 + 7726106 * 2 ^ 59
def prefixEnd_7726106 : Nat := 4983230072969 + 3 ^ 40 * 7726106 * 2
def baseEnd_7726106 : Nat := 1322401988528751269481097

theorem tailTrace_7726106 : CollatzResearch.WordTrace tailWord_7726106 prefixEnd_7726106 1322401988528751269481097 := by
  unfold tailWord_7726106
  simp only [CollatzResearch.WordTrace]
  refine ⟨70448559036911237674511543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187862824098429967132030781 70448559036911237674511543)
  ·
    refine ⟨105672838555366856511767315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70448559036911237674511543 105672838555366856511767315)
    ·
      refine ⟨158509257833050284767650973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105672838555366856511767315 158509257833050284767650973)
      ·
        refine ⟨59440971687393856787869115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158509257833050284767650973 59440971687393856787869115)
        ·
          refine ⟨89161457531090785181803673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59440971687393856787869115 89161457531090785181803673)
          ·
            refine ⟨66871093148318088886352755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89161457531090785181803673 66871093148318088886352755)
            ·
              refine ⟨100306639722477133329529133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66871093148318088886352755 100306639722477133329529133)
              ·
                refine ⟨37614989895928924998573425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100306639722477133329529133 37614989895928924998573425)
                ·
                  refine ⟨28211242421946693748930069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37614989895928924998573425 28211242421946693748930069)
                  ·
                    refine ⟨1322401988528751269481097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28211242421946693748930069 1322401988528751269481097)
                    ·
                      rfl

theorem cell23_7726106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_7726106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726106 prefixEnd_7726106 := by exact prefixLift 7726106
  have htrace : WordTrace (prefixWord ++ tailWord_7726106) baseStart_7726106 baseEnd_7726106 := by
    simpa [prefixWord, tailWord_7726106, baseEnd_7726106] using wordTrace_append hprefix tailTrace_7726106
  have hstable : (prefixWord ++ tailWord_7726106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726106).length < 2 ^ (prefixWord ++ tailWord_7726106).sum := by decide
  have hdescent : baseEnd_7726106 < baseStart_7726106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726130 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2]
def baseStart_7726130 : Nat := 118140960795 + 7726130 * 2 ^ 59
def prefixEnd_7726130 : Nat := 4983230072969 + 3 ^ 40 * 7726130 * 2
def baseEnd_7726130 : Nat := 3967218289121961714543181

theorem tailTrace_7726130 : CollatzResearch.WordTrace tailWord_7726130 prefixEnd_7726130 3967218289121961714543181 := by
  unfold tailWord_7726130
  simp only [CollatzResearch.WordTrace]
  refine ⟨70448777874889500699229961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187863407666372001864613229 70448777874889500699229961)
  ·
    refine ⟨52836583406167125524422471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70448777874889500699229961 52836583406167125524422471)
    ·
      refine ⟨79254875109250688286633707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52836583406167125524422471 79254875109250688286633707)
      ·
        refine ⟨118882312663876032429950561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79254875109250688286633707 118882312663876032429950561)
        ·
          refine ⟨89161734497907024322462921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118882312663876032429950561 89161734497907024322462921)
          ·
            refine ⟨66871300873430268241847191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89161734497907024322462921 66871300873430268241847191)
            ·
              refine ⟨100306951310145402362770787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66871300873430268241847191 100306951310145402362770787)
              ·
                refine ⟨150460426965218103544156181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100306951310145402362770787 150460426965218103544156181)
                ·
                  refine ⟨7052832513994598603632321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150460426965218103544156181 7052832513994598603632321)
                  ·
                    refine ⟨5289624385495948952724241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7052832513994598603632321 5289624385495948952724241)
                    ·
                      refine ⟨3967218289121961714543181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5289624385495948952724241 3967218289121961714543181)
                      ·
                        rfl

theorem cell23_7726130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_7726130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726130 prefixEnd_7726130 := by exact prefixLift 7726130
  have htrace : WordTrace (prefixWord ++ tailWord_7726130) baseStart_7726130 baseEnd_7726130 := by
    simpa [prefixWord, tailWord_7726130, baseEnd_7726130] using wordTrace_append hprefix tailTrace_7726130
  have hstable : (prefixWord ++ tailWord_7726130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726130).length < 2 ^ (prefixWord ++ tailWord_7726130).sum := by decide
  have hdescent : baseEnd_7726130 < baseStart_7726130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726164 : List Nat := [2, 4, 1, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_7726164 : Nat := 118140960795 + 7726164 * 2 ^ 59
def prefixEnd_7726164 : Nat := 4983230072969 + 3 ^ 40 * 7726164 * 2
def baseEnd_7726164 : Nat := 3967235747464214581518025

theorem tailTrace_7726164 : CollatzResearch.WordTrace tailWord_7726164 prefixEnd_7726164 3967235747464214581518025 := by
  unfold tailWord_7726164
  simp only [CollatzResearch.WordTrace]
  refine ⟨140898175790717413301828773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187864234387623217735771697 140898175790717413301828773)
  ·
    refine ⟨26418407960759514994092895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140898175790717413301828773 26418407960759514994092895)
    ·
      refine ⟨39627611941139272491139343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26418407960759514994092895 39627611941139272491139343)
      ·
        refine ⟨59441417911708908736709015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39627611941139272491139343 59441417911708908736709015)
        ·
          refine ⟨89162126867563363105063523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59441417911708908736709015 89162126867563363105063523)
          ·
            refine ⟨133743190301345044657595285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89162126867563363105063523 133743190301345044657595285)
            ·
              refine ⟨6269212045375548968324779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133743190301345044657595285 6269212045375548968324779)
              ·
                refine ⟨9403818068063323452487169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6269212045375548968324779 9403818068063323452487169)
                ·
                  refine ⟨7052863551047492589365377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9403818068063323452487169 7052863551047492589365377)
                  ·
                    refine ⟨5289647663285619442024033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7052863551047492589365377 5289647663285619442024033)
                    ·
                      refine ⟨3967235747464214581518025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5289647663285619442024033 3967235747464214581518025)
                      ·
                        rfl

theorem cell23_7726164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_7726164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726164 prefixEnd_7726164 := by exact prefixLift 7726164
  have htrace : WordTrace (prefixWord ++ tailWord_7726164) baseStart_7726164 baseEnd_7726164 := by
    simpa [prefixWord, tailWord_7726164, baseEnd_7726164] using wordTrace_append hprefix tailTrace_7726164
  have hstable : (prefixWord ++ tailWord_7726164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726164).length < 2 ^ (prefixWord ++ tailWord_7726164).sum := by decide
  have hdescent : baseEnd_7726164 < baseStart_7726164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726176 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 7]
def baseStart_7726176 : Nat := 118140960795 + 7726176 * 2 ^ 59
def prefixEnd_7726176 : Nat := 4983230072969 + 3 ^ 40 * 7726176 * 2
def baseEnd_7726176 : Nat := 3967241909232068534567969

theorem tailTrace_7726176 : CollatzResearch.WordTrace tailWord_7726176 prefixEnd_7726176 3967241909232068534567969 := by
  unfold tailWord_7726176
  simp only [CollatzResearch.WordTrace]
  refine ⟨140898394628695676326547191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187864526171594235102062921 140898394628695676326547191)
  ·
    refine ⟨211347591943043514489820787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140898394628695676326547191 211347591943043514489820787)
    ·
      refine ⟨317021387914565271734731181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211347591943043514489820787 317021387914565271734731181)
      ·
        refine ⟨118883020467961976900524193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317021387914565271734731181 118883020467961976900524193)
        ·
          refine ⟨89162265350971482675393145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118883020467961976900524193 89162265350971482675393145)
          ·
            refine ⟨66871699013228612006544859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89162265350971482675393145 66871699013228612006544859)
            ·
              refine ⟨100307548519842918009817289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66871699013228612006544859 100307548519842918009817289)
              ·
                refine ⟨75230661389882188507362967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100307548519842918009817289 75230661389882188507362967)
                ·
                  refine ⟨112845992084823282761044451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75230661389882188507362967 112845992084823282761044451)
                  ·
                    refine ⟨169268988127234924141566677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112845992084823282761044451 169268988127234924141566677)
                    ·
                      refine ⟨3967241909232068534567969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169268988127234924141566677 3967241909232068534567969)
                      ·
                        rfl

theorem cell23_7726176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_7726176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726176 prefixEnd_7726176 := by exact prefixLift 7726176
  have htrace : WordTrace (prefixWord ++ tailWord_7726176) baseStart_7726176 baseEnd_7726176 := by
    simpa [prefixWord, tailWord_7726176, baseEnd_7726176] using wordTrace_append hprefix tailTrace_7726176
  have hstable : (prefixWord ++ tailWord_7726176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726176).length < 2 ^ (prefixWord ++ tailWord_7726176).sum := by decide
  have hdescent : baseEnd_7726176 < baseStart_7726176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726183 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 2, 5]
def baseStart_7726183 : Nat := 118140960795 + 7726183 * 2 ^ 59
def prefixEnd_7726183 : Nat := 4983230072969 + 3 ^ 40 * 7726183 * 2
def baseEnd_7726183 : Nat := 1322415167865550002393479

theorem tailTrace_7726183 : CollatzResearch.WordTrace tailWord_7726183 prefixEnd_7726183 1322415167865550002393479 := by
  unfold tailWord_7726183
  simp only [CollatzResearch.WordTrace]
  refine ⟨281797044568365992848599203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187864696378910661899066135 281797044568365992848599203)
  ·
    refine ⟨422695566852548989272898805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281797044568365992848599203 422695566852548989272898805)
    ·
      refine ⟨39627709392426467744334263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 422695566852548989272898805 39627709392426467744334263)
      ·
        refine ⟨59441564088639701616501395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39627709392426467744334263 59441564088639701616501395)
        ·
          refine ⟨89162346132959552424752093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59441564088639701616501395 89162346132959552424752093)
          ·
            refine ⟨33435879799859832159282035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89162346132959552424752093 33435879799859832159282035)
            ·
              refine ⟨50153819699789748238923053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33435879799859832159282035 50153819699789748238923053)
              ·
                refine ⟨18807682387421155589596145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50153819699789748238923053 18807682387421155589596145)
                ·
                  refine ⟨14105761790565866692197109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18807682387421155589596145 14105761790565866692197109)
                  ·
                    refine ⟨1322415167865550002393479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14105761790565866692197109 1322415167865550002393479)
                    ·
                      rfl

theorem cell23_7726183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_7726183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726183 prefixEnd_7726183 := by exact prefixLift 7726183
  have htrace : WordTrace (prefixWord ++ tailWord_7726183) baseStart_7726183 baseEnd_7726183 := by
    simpa [prefixWord, tailWord_7726183, baseEnd_7726183] using wordTrace_append hprefix tailTrace_7726183
  have hstable : (prefixWord ++ tailWord_7726183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726183).length < 2 ^ (prefixWord ++ tailWord_7726183).sum := by decide
  have hdescent : baseEnd_7726183 < baseStart_7726183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726203 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 3, 6, 2]
def baseStart_7726203 : Nat := 118140960795 + 7726203 * 2 ^ 59
def prefixEnd_7726203 : Nat := 4983230072969 + 3 ^ 40 * 7726203 * 2
def baseEnd_7726203 : Nat := 3967255773209739928930345

theorem tailTrace_7726203 : CollatzResearch.WordTrace tailWord_7726203 prefixEnd_7726203 3967255773209739928930345 := by
  unfold tailWord_7726203
  simp only [CollatzResearch.WordTrace]
  refine ⟨281797774028293536264327263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187865182685529024176218175 281797774028293536264327263)
  ·
    refine ⟨422696661042440304396490895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281797774028293536264327263 422696661042440304396490895)
    ·
      refine ⟨634044991563660456594736343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422696661042440304396490895 634044991563660456594736343)
      ·
        refine ⟨951067487345490684892104515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634044991563660456594736343 951067487345490684892104515)
        ·
          refine ⟨1426601231018236027338156773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951067487345490684892104515 1426601231018236027338156773)
          ·
            refine ⟨267487730815919255125904395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1426601231018236027338156773 267487730815919255125904395)
            ·
              refine ⟨401231596223878882688856593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267487730815919255125904395 401231596223878882688856593)
              ·
                refine ⟨300923697167909162016642445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401231596223878882688856593 300923697167909162016642445)
                ·
                  refine ⟨112846386437965935756240917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300923697167909162016642445 112846386437965935756240917)
                  ·
                    refine ⟨5289674364279653238573793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112846386437965935756240917 5289674364279653238573793)
                    ·
                      refine ⟨3967255773209739928930345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5289674364279653238573793 3967255773209739928930345)
                      ·
                        rfl

theorem cell23_7726203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 6, 2].length) (baseStart_7726203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726203 prefixEnd_7726203 := by exact prefixLift 7726203
  have htrace : WordTrace (prefixWord ++ tailWord_7726203) baseStart_7726203 baseEnd_7726203 := by
    simpa [prefixWord, tailWord_7726203, baseEnd_7726203] using wordTrace_append hprefix tailTrace_7726203
  have hstable : (prefixWord ++ tailWord_7726203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726203).length < 2 ^ (prefixWord ++ tailWord_7726203).sum := by decide
  have hdescent : baseEnd_7726203 < baseStart_7726203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726250 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7726250 : Nat := 118140960795 + 7726250 * 2 ^ 59
def prefixEnd_7726250 : Nat := 4983230072969 + 3 ^ 40 * 7726250 * 2
def baseEnd_7726250 : Nat := 3967279906800501245042629

theorem tailTrace_7726250 : CollatzResearch.WordTrace tailWord_7726250 prefixEnd_7726250 3967279906800501245042629 := by
  unfold tailWord_7726250
  simp only [CollatzResearch.WordTrace]
  refine ⟨70449872064780815822822051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187866325506082175527525469 70449872064780815822822051)
  ·
    refine ⟨105674808097171223734233077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70449872064780815822822051 105674808097171223734233077)
    ·
      refine ⟨9907013259109802225084351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105674808097171223734233077 9907013259109802225084351)
      ·
        refine ⟨14860519888664703337626527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9907013259109802225084351 14860519888664703337626527)
        ·
          refine ⟨22290779832997055006439791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14860519888664703337626527 22290779832997055006439791)
          ·
            refine ⟨33436169749495582509659687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22290779832997055006439791 33436169749495582509659687)
            ·
              refine ⟨50154254624243373764489531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33436169749495582509659687 50154254624243373764489531)
              ·
                refine ⟨75231381936365060646734297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50154254624243373764489531 75231381936365060646734297)
                ·
                  refine ⟨56423536452273795485050723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75231381936365060646734297 56423536452273795485050723)
                  ·
                    refine ⟨84635304678410693227576085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56423536452273795485050723 84635304678410693227576085)
                    ·
                      refine ⟨3967279906800501245042629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84635304678410693227576085 3967279906800501245042629)
                      ·
                        rfl

theorem cell23_7726250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7726250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726250 prefixEnd_7726250 := by exact prefixLift 7726250
  have htrace : WordTrace (prefixWord ++ tailWord_7726250) baseStart_7726250 baseEnd_7726250 := by
    simpa [prefixWord, tailWord_7726250, baseEnd_7726250] using wordTrace_append hprefix tailTrace_7726250
  have hstable : (prefixWord ++ tailWord_7726250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726250).length < 2 ^ (prefixWord ++ tailWord_7726250).sum := by decide
  have hdescent : baseEnd_7726250 < baseStart_7726250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726280 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 1, 5, 2]
def baseStart_7726280 : Nat := 118140960795 + 7726280 * 2 ^ 59
def prefixEnd_7726280 : Nat := 4983230072969 + 3 ^ 40 * 7726280 * 2
def baseEnd_7726280 : Nat := 3967295311220136127667491

theorem tailTrace_7726280 : CollatzResearch.WordTrace tailWord_7726280 prefixEnd_7726280 3967295311220136127667491 := by
  unfold tailWord_7726280
  simp only [CollatzResearch.WordTrace]
  refine ⟨140900291224507289207440147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187867054966009718943253529 140900291224507289207440147)
  ·
    refine ⟨211350436836760933811160221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140900291224507289207440147 211350436836760933811160221)
    ·
      refine ⟨79256413813785350179185083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211350436836760933811160221 79256413813785350179185083)
      ·
        refine ⟨118884620720678025268777625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79256413813785350179185083 118884620720678025268777625)
        ·
          refine ⟨89163465540508518951583219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118884620720678025268777625 89163465540508518951583219)
          ·
            refine ⟨133745198310762778427374829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89163465540508518951583219 133745198310762778427374829)
            ·
              refine ⟨50154449366536041910265561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133745198310762778427374829 50154449366536041910265561)
              ·
                refine ⟨37615837024902031432699171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50154449366536041910265561 37615837024902031432699171)
                ·
                  refine ⟨56423755537353047149048757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37615837024902031432699171 56423755537353047149048757)
                  ·
                    refine ⟨5289727081626848170223321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56423755537353047149048757 5289727081626848170223321)
                    ·
                      refine ⟨3967295311220136127667491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5289727081626848170223321 3967295311220136127667491)
                      ·
                        rfl

theorem cell23_7726280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_7726280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726280 prefixEnd_7726280 := by exact prefixLift 7726280
  have htrace : WordTrace (prefixWord ++ tailWord_7726280) baseStart_7726280 baseEnd_7726280 := by
    simpa [prefixWord, tailWord_7726280, baseEnd_7726280] using wordTrace_append hprefix tailTrace_7726280
  have hstable : (prefixWord ++ tailWord_7726280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726280).length < 2 ^ (prefixWord ++ tailWord_7726280).sum := by decide
  have hdescent : baseEnd_7726280 < baseStart_7726280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726303 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 1, 6]
def baseStart_7726303 : Nat := 118140960795 + 7726303 * 2 ^ 59
def prefixEnd_7726303 : Nat := 4983230072969 + 3 ^ 40 * 7726303 * 2
def baseEnd_7726303 : Nat := 1322435707091729845893295

theorem tailTrace_7726303 : CollatzResearch.WordTrace tailWord_7726303 prefixEnd_7726303 1322435707091729845893295 := by
  unfold tailWord_7726303
  simp only [CollatzResearch.WordTrace]
  refine ⟨281801421327931253342967563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187867614218620835561978375 281801421327931253342967563)
  ·
    refine ⟨422702131991896880014451345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281801421327931253342967563 422702131991896880014451345)
    ·
      refine ⟨317026598993922660010838509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422702131991896880014451345 317026598993922660010838509)
      ·
        refine ⟨118884974622720997504064441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317026598993922660010838509 118884974622720997504064441)
        ·
          refine ⟨89163730967040748128048331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118884974622720997504064441 89163730967040748128048331)
          ·
            refine ⟨133745596450561122192072497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89163730967040748128048331 133745596450561122192072497)
            ·
              refine ⟨100309197337920841644054373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133745596450561122192072497 100309197337920841644054373)
              ·
                refine ⟨18807974500860157808260195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100309197337920841644054373 18807974500860157808260195)
                ·
                  refine ⟨28211961751290236712390293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18807974500860157808260195 28211961751290236712390293)
                  ·
                    refine ⟨1322435707091729845893295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28211961751290236712390293 1322435707091729845893295)
                    ·
                      rfl

theorem cell23_7726303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 6].length) (baseStart_7726303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726303 prefixEnd_7726303 := by exact prefixLift 7726303
  have htrace : WordTrace (prefixWord ++ tailWord_7726303) baseStart_7726303 baseEnd_7726303 := by
    simpa [prefixWord, tailWord_7726303, baseEnd_7726303] using wordTrace_append hprefix tailTrace_7726303
  have hstable : (prefixWord ++ tailWord_7726303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726303).length < 2 ^ (prefixWord ++ tailWord_7726303).sum := by decide
  have hdescent : baseEnd_7726303 < baseStart_7726303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726304 : List Nat := [2, 1, 1, 3, 1, 4, 3, 3, 1, 1, 3]
def baseStart_7726304 : Nat := 118140960795 + 7726304 * 2 ^ 59
def prefixEnd_7726304 : Nat := 4983230072969 + 3 ^ 40 * 7726304 * 2
def baseEnd_7726304 : Nat := 3967307634755844033767381

theorem tailTrace_7726304 : CollatzResearch.WordTrace tailWord_7726304 prefixEnd_7726304 3967307634755844033767381 := by
  unfold tailWord_7726304
  simp only [CollatzResearch.WordTrace]
  refine ⟨140900728900463815256876983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187867638533951753675835977 140900728900463815256876983)
  ·
    refine ⟨211351093350695722885315475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140900728900463815256876983 211351093350695722885315475)
    ·
      refine ⟨317026640026043584327973213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211351093350695722885315475 317026640026043584327973213)
      ·
        refine ⟨118884990009766344122989955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317026640026043584327973213 118884990009766344122989955)
        ·
          refine ⟨178327485014649516184484933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118884990009766344122989955 178327485014649516184484933)
          ·
            refine ⟨33436403440246784284590925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178327485014649516184484933 33436403440246784284590925)
            ·
              refine ⟨12538651290092544106721597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33436403440246784284590925 12538651290092544106721597)
              ·
                refine ⟨4701994233784704040020599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12538651290092544106721597 4701994233784704040020599)
                ·
                  refine ⟨7052991350677056060030899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4701994233784704040020599 7052991350677056060030899)
                  ·
                    refine ⟨10579487026015584090046349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7052991350677056060030899 10579487026015584090046349)
                    ·
                      refine ⟨3967307634755844033767381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10579487026015584090046349 3967307634755844033767381)
                      ·
                        rfl

theorem cell23_7726304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_7726304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726304 prefixEnd_7726304 := by exact prefixLift 7726304
  have htrace : WordTrace (prefixWord ++ tailWord_7726304) baseStart_7726304 baseEnd_7726304 := by
    simpa [prefixWord, tailWord_7726304, baseEnd_7726304] using wordTrace_append hprefix tailTrace_7726304
  have hstable : (prefixWord ++ tailWord_7726304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726304).length < 2 ^ (prefixWord ++ tailWord_7726304).sum := by decide
  have hdescent : baseEnd_7726304 < baseStart_7726304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726323 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 6]
def baseStart_7726323 : Nat := 118140960795 + 7726323 * 2 ^ 59
def prefixEnd_7726323 : Nat := 4983230072969 + 3 ^ 40 * 7726323 * 2
def baseEnd_7726323 : Nat := 3967317390888279459429793

theorem tailTrace_7726323 : CollatzResearch.WordTrace tailWord_7726323 prefixEnd_7726323 3967317390888279459429793 := by
  unfold tailWord_7726323
  simp only [CollatzResearch.WordTrace]
  refine ⟨281802150787858796758695623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187868100525239197839130415 281802150787858796758695623)
  ·
    refine ⟨422703226181788195138043435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281802150787858796758695623 422703226181788195138043435)
    ·
      refine ⟨634054839272682292707065153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422703226181788195138043435 634054839272682292707065153)
      ·
        refine ⟨475541129454511719530298865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634054839272682292707065153 475541129454511719530298865)
        ·
          refine ⟨356655847090883789647724149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475541129454511719530298865 356655847090883789647724149)
          ·
            refine ⟨33436485664770355279474139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 356655847090883789647724149 33436485664770355279474139)
            ·
              refine ⟨50154728497155532919211209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33436485664770355279474139 50154728497155532919211209)
              ·
                refine ⟨37616046372866649689408407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50154728497155532919211209 37616046372866649689408407)
                ·
                  refine ⟨56424069559299974534112611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37616046372866649689408407 56424069559299974534112611)
                  ·
                    refine ⟨84636104338949961801168917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56424069559299974534112611 84636104338949961801168917)
                    ·
                      refine ⟨3967317390888279459429793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84636104338949961801168917 3967317390888279459429793)
                      ·
                        rfl

theorem cell23_7726323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_7726323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726323 prefixEnd_7726323 := by exact prefixLift 7726323
  have htrace : WordTrace (prefixWord ++ tailWord_7726323) baseStart_7726323 baseEnd_7726323 := by
    simpa [prefixWord, tailWord_7726323, baseEnd_7726323] using wordTrace_append hprefix tailTrace_7726323
  have hstable : (prefixWord ++ tailWord_7726323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726323).length < 2 ^ (prefixWord ++ tailWord_7726323).sum := by decide
  have hdescent : baseEnd_7726323 < baseStart_7726323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726330 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3]
def baseStart_7726330 : Nat := 118140960795 + 7726330 * 2 ^ 59
def prefixEnd_7726330 : Nat := 4983230072969 + 3 ^ 40 * 7726330 * 2
def baseEnd_7726330 : Nat := 3967320985252860932042261

theorem tailTrace_7726330 : CollatzResearch.WordTrace tailWord_7726330 prefixEnd_7726330 3967320985252860932042261 := by
  unfold tailWord_7726330
  simp only [CollatzResearch.WordTrace]
  refine ⟨70450601524708359238550111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187868270732555624636133629 70450601524708359238550111)
  ·
    refine ⟨105675902287062538857825167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70450601524708359238550111 105675902287062538857825167)
    ·
      refine ⟨158513853430593808286737751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105675902287062538857825167 158513853430593808286737751)
      ·
        refine ⟨237770780145890712430106627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158513853430593808286737751 237770780145890712430106627)
        ·
          refine ⟨356656170218836068645159941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237770780145890712430106627 356656170218836068645159941)
          ·
            refine ⟨66873031916031762870967489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356656170218836068645159941 66873031916031762870967489)
            ·
              refine ⟨50154773937023822153225617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66873031916031762870967489 50154773937023822153225617)
              ·
                refine ⟨37616080452767866614919213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50154773937023822153225617 37616080452767866614919213)
                ·
                  refine ⟨14106030169787949980594705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37616080452767866614919213 14106030169787949980594705)
                  ·
                    refine ⟨10579522627340962485446029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14106030169787949980594705 10579522627340962485446029)
                    ·
                      refine ⟨3967320985252860932042261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10579522627340962485446029 3967320985252860932042261)
                      ·
                        rfl

theorem cell23_7726330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_7726330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726330 prefixEnd_7726330 := by exact prefixLift 7726330
  have htrace : WordTrace (prefixWord ++ tailWord_7726330) baseStart_7726330 baseEnd_7726330 := by
    simpa [prefixWord, tailWord_7726330, baseEnd_7726330] using wordTrace_append hprefix tailTrace_7726330
  have hstable : (prefixWord ++ tailWord_7726330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726330).length < 2 ^ (prefixWord ++ tailWord_7726330).sum := by decide
  have hdescent : baseEnd_7726330 < baseStart_7726330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726337 : List Nat := [1, 2, 4, 1, 1, 4, 1, 3, 2, 4]
def baseStart_7726337 : Nat := 118140960795 + 7726337 * 2 ^ 59
def prefixEnd_7726337 : Nat := 4983230072969 + 3 ^ 40 * 7726337 * 2
def baseEnd_7726337 : Nat := 1322441526539147468218243

theorem tailTrace_7726337 : CollatzResearch.WordTrace tailWord_7726337 prefixEnd_7726337 1322441526539147468218243 := by
  unfold tailWord_7726337
  simp only [CollatzResearch.WordTrace]
  refine ⟨281802661409808077149705265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187868440939872051433136843 281802661409808077149705265)
  ·
    refine ⟨211351996057356057862278949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281802661409808077149705265 211351996057356057862278949)
    ·
      refine ⟨39628499260754260849177303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211351996057356057862278949 39628499260754260849177303)
      ·
        refine ⟨59442748891131391273765955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39628499260754260849177303 59442748891131391273765955)
        ·
          refine ⟨89164123336697086910648933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59442748891131391273765955 89164123336697086910648933)
          ·
            refine ⟨16718273125630703795746675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89164123336697086910648933 16718273125630703795746675)
            ·
              refine ⟨25077409688446055693620013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16718273125630703795746675 25077409688446055693620013)
              ·
                refine ⟨9404028633167270885107505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25077409688446055693620013 9404028633167270885107505)
                ·
                  refine ⟨7053021474875453163830629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9404028633167270885107505 7053021474875453163830629)
                  ·
                    refine ⟨1322441526539147468218243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7053021474875453163830629 1322441526539147468218243)
                    ·
                      rfl

theorem cell23_7726337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_7726337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726337 prefixEnd_7726337 := by exact prefixLift 7726337
  have htrace : WordTrace (prefixWord ++ tailWord_7726337) baseStart_7726337 baseEnd_7726337 := by
    simpa [prefixWord, tailWord_7726337, baseEnd_7726337] using wordTrace_append hprefix tailTrace_7726337
  have hstable : (prefixWord ++ tailWord_7726337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726337).length < 2 ^ (prefixWord ++ tailWord_7726337).sum := by decide
  have hdescent : baseEnd_7726337 < baseStart_7726337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726340 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_7726340 : Nat := 118140960795 + 7726340 * 2 ^ 59
def prefixEnd_7726340 : Nat := 4983230072969 + 3 ^ 40 * 7726340 * 2
def baseEnd_7726340 : Nat := 3967326120059405892917215

theorem tailTrace_7726340 : CollatzResearch.WordTrace tailWord_7726340 prefixEnd_7726340 3967326120059405892917215 := by
  unfold tailWord_7726340
  simp only [CollatzResearch.WordTrace]
  refine ⟨140901385414398604331032237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187868513885864805774709649 140901385414398604331032237)
  ·
    refine ⟨52838019530399476624137089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140901385414398604331032237 52838019530399476624137089)
    ·
      refine ⟨39628514647799607468102817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52838019530399476624137089 39628514647799607468102817)
      ·
        refine ⟨29721385985849705601077113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39628514647799607468102817 29721385985849705601077113)
        ·
          refine ⟨22291039489387279200807835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29721385985849705601077113 22291039489387279200807835)
          ·
            refine ⟨33436559234080918801211753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22291039489387279200807835 33436559234080918801211753)
            ·
              refine ⟨25077419425560689100908815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33436559234080918801211753 25077419425560689100908815)
              ·
                refine ⟨37616129138341033651363223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25077419425560689100908815 37616129138341033651363223)
                ·
                  refine ⟨56424193707511550477044835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37616129138341033651363223 56424193707511550477044835)
                  ·
                    refine ⟨84636290561267325715567253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56424193707511550477044835 84636290561267325715567253)
                    ·
                      refine ⟨3967326120059405892917215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84636290561267325715567253 3967326120059405892917215)
                      ·
                        rfl

theorem cell23_7726340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_7726340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726340 prefixEnd_7726340 := by exact prefixLift 7726340
  have htrace : WordTrace (prefixWord ++ tailWord_7726340) baseStart_7726340 baseEnd_7726340 := by
    simpa [prefixWord, tailWord_7726340, baseEnd_7726340] using wordTrace_append hprefix tailTrace_7726340
  have hstable : (prefixWord ++ tailWord_7726340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726340).length < 2 ^ (prefixWord ++ tailWord_7726340).sum := by decide
  have hdescent : baseEnd_7726340 < baseStart_7726340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726344 : List Nat := [2, 1, 3, 2, 4, 2, 1, 2, 1, 1, 4]
def baseStart_7726344 : Nat := 118140960795 + 7726344 * 2 ^ 59
def prefixEnd_7726344 : Nat := 4983230072969 + 3 ^ 40 * 7726344 * 2
def baseEnd_7726344 : Nat := 3967328173982023877267197

theorem tailTrace_7726344 : CollatzResearch.WordTrace tailWord_7726344 prefixEnd_7726344 3967328173982023877267197 := by
  unfold tailWord_7726344
  simp only [CollatzResearch.WordTrace]
  refine ⟨140901458360391358672605043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187868611147188478230140057 140901458360391358672605043)
  ·
    refine ⟨211352187540587038008907565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140901458360391358672605043 211352187540587038008907565)
    ·
      refine ⟨79257070327720139253340337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211352187540587038008907565 79257070327720139253340337)
      ·
        refine ⟨59442802745790104440005253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79257070327720139253340337 59442802745790104440005253)
        ·
          refine ⟨11145525514835644582500985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59442802745790104440005253 11145525514835644582500985)
          ·
            refine ⟨8359144136126733436875739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11145525514835644582500985 8359144136126733436875739)
            ·
              refine ⟨12538716204190100155313609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8359144136126733436875739 12538716204190100155313609)
              ·
                refine ⟨9404037153142575116485207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12538716204190100155313609 9404037153142575116485207)
                ·
                  refine ⟨14106055729713862674727811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9404037153142575116485207 14106055729713862674727811)
                  ·
                    refine ⟨21159083594570794012091717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14106055729713862674727811 21159083594570794012091717)
                    ·
                      refine ⟨3967328173982023877267197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21159083594570794012091717 3967328173982023877267197)
                      ·
                        rfl

theorem cell23_7726344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_7726344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726344 prefixEnd_7726344 := by exact prefixLift 7726344
  have htrace : WordTrace (prefixWord ++ tailWord_7726344) baseStart_7726344 baseEnd_7726344 := by
    simpa [prefixWord, tailWord_7726344, baseEnd_7726344] using wordTrace_append hprefix tailTrace_7726344
  have hstable : (prefixWord ++ tailWord_7726344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726344).length < 2 ^ (prefixWord ++ tailWord_7726344).sum := by decide
  have hdescent : baseEnd_7726344 < baseStart_7726344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726347 : List Nat := [1, 1, 1, 1, 5, 3, 3, 2, 1, 2, 3]
def baseStart_7726347 : Nat := 118140960795 + 7726347 * 2 ^ 59
def prefixEnd_7726347 : Nat := 4983230072969 + 3 ^ 40 * 7726347 * 2
def baseEnd_7726347 : Nat := 3967329714423987365529683

theorem tailTrace_7726347 : CollatzResearch.WordTrace tailWord_7726347 prefixEnd_7726347 3967329714423987365529683 := by
  unfold tailWord_7726347
  simp only [CollatzResearch.WordTrace]
  refine ⟨281803026139771848857569295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187868684093181232571712863 281803026139771848857569295)
  ·
    refine ⟨422704539209657773286353943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281803026139771848857569295 422704539209657773286353943)
    ·
      refine ⟨634056808814486659929530915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422704539209657773286353943 634056808814486659929530915)
      ·
        refine ⟨951085213221729989894296373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634056808814486659929530915 951085213221729989894296373)
        ·
          refine ⟨89164238739537186552590285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 951085213221729989894296373 89164238739537186552590285)
          ·
            refine ⟨33436589527326444957221357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89164238739537186552590285 33436589527326444957221357)
            ·
              refine ⟨12538721072747416858958009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33436589527326444957221357 12538721072747416858958009)
              ·
                refine ⟨9404040804560562644218507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12538721072747416858958009 9404040804560562644218507)
                ·
                  refine ⟨14106061206840843966327761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9404040804560562644218507 14106061206840843966327761)
                  ·
                    refine ⟨10579545905130632974745821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14106061206840843966327761 10579545905130632974745821)
                    ·
                      refine ⟨3967329714423987365529683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10579545905130632974745821 3967329714423987365529683)
                      ·
                        rfl

theorem cell23_7726347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 2, 3].length) (baseStart_7726347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726347 prefixEnd_7726347 := by exact prefixLift 7726347
  have htrace : WordTrace (prefixWord ++ tailWord_7726347) baseStart_7726347 baseEnd_7726347 := by
    simpa [prefixWord, tailWord_7726347, baseEnd_7726347] using wordTrace_append hprefix tailTrace_7726347
  have hstable : (prefixWord ++ tailWord_7726347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726347).length < 2 ^ (prefixWord ++ tailWord_7726347).sum := by decide
  have hdescent : baseEnd_7726347 < baseStart_7726347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726354 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_7726354 : Nat := 118140960795 + 7726354 * 2 ^ 59
def prefixEnd_7726354 : Nat := 4983230072969 + 3 ^ 40 * 7726354 * 2
def baseEnd_7726354 : Nat := 1322444436262856279380717

theorem tailTrace_7726354 : CollatzResearch.WordTrace tailWord_7726354 prefixEnd_7726354 1322444436262856279380717 := by
  unfold tailWord_7726354
  simp only [CollatzResearch.WordTrace]
  refine ⟨70450820362686622263268529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187868854300497659368716077 70450820362686622263268529)
  ·
    refine ⟨52838115272014966697451397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70450820362686622263268529 52838115272014966697451397)
    ·
      refine ⟨9907146613502806255772137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52838115272014966697451397 9907146613502806255772137)
      ·
        refine ⟨7430359960127104691829103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9907146613502806255772137 7430359960127104691829103)
        ·
          refine ⟨11145539940190657037743655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7430359960127104691829103 11145539940190657037743655)
          ·
            refine ⟨16718309910285985556615483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11145539940190657037743655 16718309910285985556615483)
            ·
              refine ⟨25077464865428978334923225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16718309910285985556615483 25077464865428978334923225)
              ·
                refine ⟨18808098649071733751192419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25077464865428978334923225 18808098649071733751192419)
                ·
                  refine ⟨28212147973607600626788629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18808098649071733751192419 28212147973607600626788629)
                  ·
                    refine ⟨1322444436262856279380717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28212147973607600626788629 1322444436262856279380717)
                    ·
                      rfl

theorem cell23_7726354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_7726354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726354 prefixEnd_7726354 := by exact prefixLift 7726354
  have htrace : WordTrace (prefixWord ++ tailWord_7726354) baseStart_7726354 baseEnd_7726354 := by
    simpa [prefixWord, tailWord_7726354, baseEnd_7726354] using wordTrace_append hprefix tailTrace_7726354
  have hstable : (prefixWord ++ tailWord_7726354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726354).length < 2 ^ (prefixWord ++ tailWord_7726354).sum := by decide
  have hdescent : baseEnd_7726354 < baseStart_7726354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726360 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 3, 3, 3]
def baseStart_7726360 : Nat := 118140960795 + 7726360 * 2 ^ 59
def prefixEnd_7726360 : Nat := 4983230072969 + 3 ^ 40 * 7726360 * 2
def baseEnd_7726360 : Nat := 3967336389672495814667123

theorem tailTrace_7726360 : CollatzResearch.WordTrace tailWord_7726360 prefixEnd_7726360 3967336389672495814667123 := by
  unfold tailWord_7726360
  simp only [CollatzResearch.WordTrace]
  refine ⟨140901750144362376038896267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187869000192483168051861689 140901750144362376038896267)
  ·
    refine ⟨211352625216543564058344401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140901750144362376038896267 211352625216543564058344401)
    ·
      refine ⟨158514468912407673043758301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211352625216543564058344401 158514468912407673043758301)
      ·
        refine ⟨59442925842152877391409363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158514468912407673043758301 59442925842152877391409363)
        ·
          refine ⟨89164388763229316087114045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59442925842152877391409363 89164388763229316087114045)
          ·
            refine ⟨33436645786210993532667767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89164388763229316087114045 33436645786210993532667767)
            ·
              refine ⟨50154968679316490299001651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33436645786210993532667767 50154968679316490299001651)
              ·
                refine ⟨75232453018974735448502477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50154968679316490299001651 75232453018974735448502477)
                ·
                  refine ⟨28212169882115525793188429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75232453018974735448502477 28212169882115525793188429)
                  ·
                    refine ⟨10579563705793322172445661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28212169882115525793188429 10579563705793322172445661)
                    ·
                      refine ⟨3967336389672495814667123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10579563705793322172445661 3967336389672495814667123)
                      ·
                        rfl

theorem cell23_7726360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_7726360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726360 prefixEnd_7726360 := by exact prefixLift 7726360
  have htrace : WordTrace (prefixWord ++ tailWord_7726360) baseStart_7726360 baseEnd_7726360 := by
    simpa [prefixWord, tailWord_7726360, baseEnd_7726360] using wordTrace_append hprefix tailTrace_7726360
  have hstable : (prefixWord ++ tailWord_7726360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726360).length < 2 ^ (prefixWord ++ tailWord_7726360).sum := by decide
  have hdescent : baseEnd_7726360 < baseStart_7726360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726378 : List Nat := [3, 1, 4, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_7726378 : Nat := 118140960795 + 7726378 * 2 ^ 59
def prefixEnd_7726378 : Nat := 4983230072969 + 3 ^ 40 * 7726378 * 2
def baseEnd_7726378 : Nat := 3967345632324276744242041

theorem tailTrace_7726378 : CollatzResearch.WordTrace tailWord_7726378 prefixEnd_7726378 3967345632324276744242041 := by
  unfold tailWord_7726378
  simp only [CollatzResearch.WordTrace]
  refine ⟨70451039200664885287986947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187869437868439694101298525 70451039200664885287986947)
  ·
    refine ⟨105676558800997327931980421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70451039200664885287986947 105676558800997327931980421)
    ·
      refine ⟨19814354775186998987246329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105676558800997327931980421 19814354775186998987246329)
      ·
        refine ⟨14860766081390249240434747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19814354775186998987246329 14860766081390249240434747)
        ·
          refine ⟨22291149122085373860652121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14860766081390249240434747 22291149122085373860652121)
          ·
            refine ⟨16718361841564030395489091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22291149122085373860652121 16718361841564030395489091)
            ·
              refine ⟨25077542762346045593233637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16718361841564030395489091 25077542762346045593233637)
              ·
                refine ⟨4702039267939883548731307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25077542762346045593233637 4702039267939883548731307)
                ·
                  refine ⟨7053058901909825323096961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4702039267939883548731307 7053058901909825323096961)
                  ·
                    refine ⟨5289794176432368992322721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7053058901909825323096961 5289794176432368992322721)
                    ·
                      refine ⟨3967345632324276744242041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5289794176432368992322721 3967345632324276744242041)
                      ·
                        rfl

theorem cell23_7726378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_7726378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726378 prefixEnd_7726378 := by exact prefixLift 7726378
  have htrace : WordTrace (prefixWord ++ tailWord_7726378) baseStart_7726378 baseEnd_7726378 := by
    simpa [prefixWord, tailWord_7726378, baseEnd_7726378] using wordTrace_append hprefix tailTrace_7726378
  have hstable : (prefixWord ++ tailWord_7726378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726378).length < 2 ^ (prefixWord ++ tailWord_7726378).sum := by decide
  have hdescent : baseEnd_7726378 < baseStart_7726378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726387 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 3, 3, 2]
def baseStart_7726387 : Nat := 118140960795 + 7726387 * 2 ^ 59
def prefixEnd_7726387 : Nat := 4983230072969 + 3 ^ 40 * 7726387 * 2
def baseEnd_7726387 : Nat := 3967350253650167209029499

theorem tailTrace_7726387 : CollatzResearch.WordTrace tailWord_7726387 prefixEnd_7726387 3967350253650167209029499 := by
  unfold tailWord_7726387
  simp only [CollatzResearch.WordTrace]
  refine ⟨281804485059626935689025415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187869656706417957126016943 281804485059626935689025415)
  ·
    refine ⟨422706727589440403533538123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281804485059626935689025415 422706727589440403533538123)
    ·
      refine ⟨634060091384160605300307185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422706727589440403533538123 634060091384160605300307185)
      ·
        refine ⟨475545068538120453975230389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634060091384160605300307185 475545068538120453975230389)
        ·
          refine ⟨44582350175448792560177849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 475545068538120453975230389 44582350175448792560177849)
          ·
            refine ⟨33436762631586594420133387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44582350175448792560177849 33436762631586594420133387)
            ·
              refine ⟨50155143947379891630200081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33436762631586594420133387 50155143947379891630200081)
              ·
                refine ⟨37616357960534918722650061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50155143947379891630200081 37616357960534918722650061)
                ·
                  refine ⟨14106134235200594520993773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37616357960534918722650061 14106134235200594520993773)
                  ·
                    refine ⟨5289800338200222945372665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14106134235200594520993773 5289800338200222945372665)
                    ·
                      refine ⟨3967350253650167209029499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5289800338200222945372665 3967350253650167209029499)
                      ·
                        rfl

theorem cell23_7726387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 3, 2].length) (baseStart_7726387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726387 prefixEnd_7726387 := by exact prefixLift 7726387
  have htrace : WordTrace (prefixWord ++ tailWord_7726387) baseStart_7726387 baseEnd_7726387 := by
    simpa [prefixWord, tailWord_7726387, baseEnd_7726387] using wordTrace_append hprefix tailTrace_7726387
  have hstable : (prefixWord ++ tailWord_7726387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726387).length < 2 ^ (prefixWord ++ tailWord_7726387).sum := by decide
  have hdescent : baseEnd_7726387 < baseStart_7726387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726417 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 1, 4, 2]
def baseStart_7726417 : Nat := 118140960795 + 7726417 * 2 ^ 59
def prefixEnd_7726417 : Nat := 4983230072969 + 3 ^ 40 * 7726417 * 2
def baseEnd_7726417 : Nat := 3967365658069802091654361

theorem tailTrace_7726417 : CollatzResearch.WordTrace tailWord_7726417 prefixEnd_7726417 3967365658069802091654361 := by
  unfold tailWord_7726417
  simp only [CollatzResearch.WordTrace]
  refine ⟨281805579249518250812617505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187870386166345500541745003 281805579249518250812617505)
  ·
    refine ⟨211354184437138688109463129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281805579249518250812617505 211354184437138688109463129)
    ·
      refine ⟨158515638327854016082097347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211354184437138688109463129 158515638327854016082097347)
      ·
        refine ⟨237773457491781024123146021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158515638327854016082097347 237773457491781024123146021)
        ·
          refine ⟨44582523279708942023089879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237773457491781024123146021 44582523279708942023089879)
          ·
            refine ⟨66873784919563413034634819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44582523279708942023089879 66873784919563413034634819)
            ·
              refine ⟨100310677379345119551952229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66873784919563413034634819 100310677379345119551952229)
              ·
                refine ⟨18808252008627209915991043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100310677379345119551952229 18808252008627209915991043)
                ·
                  refine ⟨28212378012940814873986565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18808252008627209915991043 28212378012940814873986565)
                  ·
                    refine ⟨5289820877426402788872481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28212378012940814873986565 5289820877426402788872481)
                    ·
                      refine ⟨3967365658069802091654361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5289820877426402788872481 3967365658069802091654361)
                      ·
                        rfl

theorem cell23_7726417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 4, 2].length) (baseStart_7726417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726417 prefixEnd_7726417 := by exact prefixLift 7726417
  have htrace : WordTrace (prefixWord ++ tailWord_7726417) baseStart_7726417 baseEnd_7726417 := by
    simpa [prefixWord, tailWord_7726417, baseEnd_7726417] using wordTrace_append hprefix tailTrace_7726417
  have hstable : (prefixWord ++ tailWord_7726417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726417).length < 2 ^ (prefixWord ++ tailWord_7726417).sum := by decide
  have hdescent : baseEnd_7726417 < baseStart_7726417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726420 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_7726420 : Nat := 118140960795 + 7726420 * 2 ^ 59
def prefixEnd_7726420 : Nat := 4983230072969 + 3 ^ 40 * 7726420 * 2
def baseEnd_7726420 : Nat := 3967367198511765579916847

theorem tailTrace_7726420 : CollatzResearch.WordTrace tailWord_7726420 prefixEnd_7726420 3967367198511765579916847 := by
  unfold tailWord_7726420
  simp only [CollatzResearch.WordTrace]
  refine ⟨140902844334253691162488357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187870459112338254883317809 140902844334253691162488357)
  ·
    refine ⟨26419283312672567092966567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140902844334253691162488357 26419283312672567092966567)
    ·
      refine ⟨39628924969008850639449851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26419283312672567092966567 39628924969008850639449851)
      ·
        refine ⟨59443387453513275959174777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39628924969008850639449851 59443387453513275959174777)
        ·
          refine ⟨44582540590134956969381083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59443387453513275959174777 44582540590134956969381083)
          ·
            refine ⟨66873810885202435454071625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44582540590134956969381083 66873810885202435454071625)
            ·
              refine ⟨50155358163901826590553719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66873810885202435454071625 50155358163901826590553719)
              ·
                refine ⟨75233037245852739885830579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50155358163901826590553719 75233037245852739885830579)
                ·
                  refine ⟨112849555868779109828745869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75233037245852739885830579 112849555868779109828745869)
                  ·
                    refine ⟨42318583450792166185779701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112849555868779109828745869 42318583450792166185779701)
                    ·
                      refine ⟨3967367198511765579916847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42318583450792166185779701 3967367198511765579916847)
                      ·
                        rfl

theorem cell23_7726420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_7726420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726420 prefixEnd_7726420 := by exact prefixLift 7726420
  have htrace : WordTrace (prefixWord ++ tailWord_7726420) baseStart_7726420 baseEnd_7726420 := by
    simpa [prefixWord, tailWord_7726420, baseEnd_7726420] using wordTrace_append hprefix tailTrace_7726420
  have hstable : (prefixWord ++ tailWord_7726420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726420).length < 2 ^ (prefixWord ++ tailWord_7726420).sum := by decide
  have hdescent : baseEnd_7726420 < baseStart_7726420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726421 : List Nat := [1, 3, 2, 2, 3, 1, 4, 1, 1, 3, 2]
def baseStart_7726421 : Nat := 118140960795 + 7726421 * 2 ^ 59
def prefixEnd_7726421 : Nat := 4983230072969 + 3 ^ 40 * 7726421 * 2
def baseEnd_7726421 : Nat := 3967367711992420076004343

theorem tailTrace_7726421 : CollatzResearch.WordTrace tailWord_7726421 prefixEnd_7726421 3967367711992420076004343 := by
  unfold tailWord_7726421
  simp only [CollatzResearch.WordTrace]
  refine ⟨281805725141503759495763117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187870483427669172997175411 281805725141503759495763117)
  ·
    refine ⟨105677146928063909810911169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281805725141503759495763117 105677146928063909810911169)
    ·
      refine ⟨79257860196047932358183377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105677146928063909810911169 79257860196047932358183377)
      ·
        refine ⟨59443395147035949268637533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79257860196047932358183377 59443395147035949268637533)
        ·
          refine ⟨22291273180138480975739075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59443395147035949268637533 22291273180138480975739075)
          ·
            refine ⟨33436909770207721463608613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22291273180138480975739075 33436909770207721463608613)
            ·
              refine ⟨6269420581913947774426615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33436909770207721463608613 6269420581913947774426615)
              ·
                refine ⟨9404130872870921661639923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6269420581913947774426615 9404130872870921661639923)
                ·
                  refine ⟨14106196309306382492459885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9404130872870921661639923 14106196309306382492459885)
                  ·
                    refine ⟨5289823615989893434672457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14106196309306382492459885 5289823615989893434672457)
                    ·
                      refine ⟨3967367711992420076004343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5289823615989893434672457 3967367711992420076004343)
                      ·
                        rfl

theorem cell23_7726421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_7726421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726421 prefixEnd_7726421 := by exact prefixLift 7726421
  have htrace : WordTrace (prefixWord ++ tailWord_7726421) baseStart_7726421 baseEnd_7726421 := by
    simpa [prefixWord, tailWord_7726421, baseEnd_7726421] using wordTrace_append hprefix tailTrace_7726421
  have hstable : (prefixWord ++ tailWord_7726421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726421).length < 2 ^ (prefixWord ++ tailWord_7726421).sum := by decide
  have hdescent : baseEnd_7726421 < baseStart_7726421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726422 : List Nat := [5, 2, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_7726422 : Nat := 118140960795 + 7726422 * 2 ^ 59
def prefixEnd_7726422 : Nat := 4983230072969 + 3 ^ 40 * 7726422 * 2
def baseEnd_7726422 : Nat := 1322456075157691524030613

theorem tailTrace_7726422 : CollatzResearch.WordTrace tailWord_7726422 prefixEnd_7726422 1322456075157691524030613 := by
  unfold tailWord_7726422
  simp only [CollatzResearch.WordTrace]
  refine ⟨17612860100906258541659345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187870507743000091111033013 17612860100906258541659345)
  ·
    refine ⟨13209645075679693906244509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17612860100906258541659345 13209645075679693906244509)
    ·
      refine ⟨4953616903379885214841691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13209645075679693906244509 4953616903379885214841691)
      ·
        refine ⟨7430425355069827822262537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4953616903379885214841691 7430425355069827822262537)
        ·
          refine ⟨5572819016302370866696903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7430425355069827822262537 5572819016302370866696903)
          ·
            refine ⟨8359228524453556300045355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5572819016302370866696903 8359228524453556300045355)
            ·
              refine ⟨12538842786680334450068033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8359228524453556300045355 12538842786680334450068033)
              ·
                refine ⟨9404132090010250837551025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12538842786680334450068033 9404132090010250837551025)
                ·
                  refine ⟨7053099067507688128163269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9404132090010250837551025 7053099067507688128163269)
                  ·
                    refine ⟨1322456075157691524030613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7053099067507688128163269 1322456075157691524030613)
                    ·
                      rfl

theorem cell23_7726422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_7726422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726422 prefixEnd_7726422 := by exact prefixLift 7726422
  have htrace : WordTrace (prefixWord ++ tailWord_7726422) baseStart_7726422 baseEnd_7726422 := by
    simpa [prefixWord, tailWord_7726422, baseEnd_7726422] using wordTrace_append hprefix tailTrace_7726422
  have hstable : (prefixWord ++ tailWord_7726422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726422).length < 2 ^ (prefixWord ++ tailWord_7726422).sum := by decide
  have hdescent : baseEnd_7726422 < baseStart_7726422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726443 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 8]
def baseStart_7726443 : Nat := 118140960795 + 7726443 * 2 ^ 59
def prefixEnd_7726443 : Nat := 4983230072969 + 3 ^ 40 * 7726443 * 2
def baseEnd_7726443 : Nat := 3967379008566818989929241

theorem tailTrace_7726443 : CollatzResearch.WordTrace tailWord_7726443 prefixEnd_7726443 3967379008566818989929241 := by
  unfold tailWord_7726443
  simp only [CollatzResearch.WordTrace]
  refine ⟨281806527547424057253063983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187871018364949371502042655 281806527547424057253063983)
  ·
    refine ⟨422709791321136085879595975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281806527547424057253063983 422709791321136085879595975)
    ·
      refine ⟨634064686981704128819393963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422709791321136085879595975 634064686981704128819393963)
      ·
        refine ⟨951097030472556193229090945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634064686981704128819393963 951097030472556193229090945)
        ·
          refine ⟨713322772854417144921818209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951097030472556193229090945 713322772854417144921818209)
          ·
            refine ⟨534992079640812858691363657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713322772854417144921818209 534992079640812858691363657)
            ·
              refine ⟨401244059730609644018522743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534992079640812858691363657 401244059730609644018522743)
              ·
                refine ⟨601866089595914466027784115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401244059730609644018522743 601866089595914466027784115)
                ·
                  refine ⟨902799134393871699041676173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601866089595914466027784115 902799134393871699041676173)
                  ·
                    refine ⟨338549675397701887140628565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 902799134393871699041676173 338549675397701887140628565)
                    ·
                      refine ⟨3967379008566818989929241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 338549675397701887140628565 3967379008566818989929241)
                      ·
                        rfl

theorem cell23_7726443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_7726443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726443 prefixEnd_7726443 := by exact prefixLift 7726443
  have htrace : WordTrace (prefixWord ++ tailWord_7726443) baseStart_7726443 baseEnd_7726443 := by
    simpa [prefixWord, tailWord_7726443, baseEnd_7726443] using wordTrace_append hprefix tailTrace_7726443
  have hstable : (prefixWord ++ tailWord_7726443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726443).length < 2 ^ (prefixWord ++ tailWord_7726443).sum := by decide
  have hdescent : baseEnd_7726443 < baseStart_7726443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726520 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_7726520 : Nat := 118140960795 + 7726520 * 2 ^ 59
def prefixEnd_7726520 : Nat := 4983230072969 + 3 ^ 40 * 7726520 * 2
def baseEnd_7726520 : Nat := 3967418546577215188666387

theorem tailTrace_7726520 : CollatzResearch.WordTrace tailWord_7726520 prefixEnd_7726520 3967418546577215188666387 := by
  unfold tailWord_7726520
  simp only [CollatzResearch.WordTrace]
  refine ⟨140904667984072549701808507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187872890645430066269078009 140904667984072549701808507)
  ·
    refine ⟨211357001976108824552712761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140904667984072549701808507 211357001976108824552712761)
    ·
      refine ⟨158517751482081618414534571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211357001976108824552712761 158517751482081618414534571)
      ·
        refine ⟨237776627223122427621801857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158517751482081618414534571 237776627223122427621801857)
        ·
          refine ⟨178332470417341820716351393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237776627223122427621801857 178332470417341820716351393)
          ·
            refine ⟨133749352813006365537263545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178332470417341820716351393 133749352813006365537263545)
            ·
              refine ⟨100312014609754774152947659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133749352813006365537263545 100312014609754774152947659)
              ·
                refine ⟨150468021914632161229421489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100312014609754774152947659 150468021914632161229421489)
                ·
                  refine ⟨112851016435974120922066117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150468021914632161229421489 112851016435974120922066117)
                  ·
                    refine ⟨21159565581745147672887397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112851016435974120922066117 21159565581745147672887397)
                    ·
                      refine ⟨3967418546577215188666387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21159565581745147672887397 3967418546577215188666387)
                      ·
                        rfl

theorem cell23_7726520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_7726520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726520 prefixEnd_7726520 := by exact prefixLift 7726520
  have htrace : WordTrace (prefixWord ++ tailWord_7726520) baseStart_7726520 baseEnd_7726520 := by
    simpa [prefixWord, tailWord_7726520, baseEnd_7726520] using wordTrace_append hprefix tailTrace_7726520
  have hstable : (prefixWord ++ tailWord_7726520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726520).length < 2 ^ (prefixWord ++ tailWord_7726520).sum := by decide
  have hdescent : baseEnd_7726520 < baseStart_7726520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726577 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 3, 5]
def baseStart_7726577 : Nat := 118140960795 + 7726577 * 2 ^ 59
def prefixEnd_7726577 : Nat := 4983230072969 + 3 ^ 40 * 7726577 * 2
def baseEnd_7726577 : Nat := 1322482604991507155217875

theorem tailTrace_7726577 : CollatzResearch.WordTrace tailWord_7726577 prefixEnd_7726577 1322482604991507155217875 := by
  unfold tailWord_7726577
  simp only [CollatzResearch.WordTrace]
  refine ⟨281811414928938598138441985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187874276619292398758961323 281811414928938598138441985)
  ·
    refine ⟨211358561196703948603831489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281811414928938598138441985 211358561196703948603831489)
    ·
      refine ⟨158518920897527961452873617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211358561196703948603831489 158518920897527961452873617)
      ·
        refine ⟨118889190673145971089655213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158518920897527961452873617 118889190673145971089655213)
        ·
          refine ⟨44583446502429739158620705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118889190673145971089655213 44583446502429739158620705)
          ·
            refine ⟨33437584876822304368965529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44583446502429739158620705 33437584876822304368965529)
            ·
              refine ⟨25078188657616728276724147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33437584876822304368965529 25078188657616728276724147)
              ·
                refine ⟨37617282986425092415086221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25078188657616728276724147 37617282986425092415086221)
                ·
                  refine ⟨14106481119909409655657333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37617282986425092415086221 14106481119909409655657333)
                  ·
                    refine ⟨1322482604991507155217875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14106481119909409655657333 1322482604991507155217875)
                    ·
                      rfl

theorem cell23_7726577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_7726577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726577 prefixEnd_7726577 := by exact prefixLift 7726577
  have htrace : WordTrace (prefixWord ++ tailWord_7726577) baseStart_7726577 baseEnd_7726577 := by
    simpa [prefixWord, tailWord_7726577, baseEnd_7726577] using wordTrace_append hprefix tailTrace_7726577
  have hstable : (prefixWord ++ tailWord_7726577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726577).length < 2 ^ (prefixWord ++ tailWord_7726577).sum := by decide
  have hdescent : baseEnd_7726577 < baseStart_7726577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726584 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 1, 5, 2]
def baseStart_7726584 : Nat := 118140960795 + 7726584 * 2 ^ 59
def prefixEnd_7726584 : Nat := 4983230072969 + 3 ^ 40 * 7726584 * 2
def baseEnd_7726584 : Nat := 3967451409339102938266093

theorem tailTrace_7726584 : CollatzResearch.WordTrace tailWord_7726584 prefixEnd_7726584 3967451409339102938266093 := by
  unfold tailWord_7726584
  simp only [CollatzResearch.WordTrace]
  refine ⟨140905835119956619166973403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187874446826608825555964537 140905835119956619166973403)
  ·
    refine ⟨211358752679934928750460105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140905835119956619166973403 211358752679934928750460105)
    ·
      refine ⟨158519064509951196562845079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211358752679934928750460105 158519064509951196562845079)
      ·
        refine ⟨237778596764926794844267619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158519064509951196562845079 237778596764926794844267619)
        ·
          refine ⟨356667895147390192266401429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237778596764926794844267619 356667895147390192266401429)
          ·
            refine ⟨16718807585033915262487567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 356667895147390192266401429 16718807585033915262487567)
            ·
              refine ⟨25078211377550872893731351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16718807585033915262487567 25078211377550872893731351)
              ·
                refine ⟨37617317066326309340597027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25078211377550872893731351 37617317066326309340597027)
                ·
                  refine ⟨56425975599489464010895541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37617317066326309340597027 56425975599489464010895541)
                  ·
                    refine ⟨5289935212452137251021457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56425975599489464010895541 5289935212452137251021457)
                    ·
                      refine ⟨3967451409339102938266093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5289935212452137251021457 3967451409339102938266093)
                      ·
                        rfl

theorem cell23_7726584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 5, 2].length) (baseStart_7726584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726584 prefixEnd_7726584 := by exact prefixLift 7726584
  have htrace : WordTrace (prefixWord ++ tailWord_7726584) baseStart_7726584 baseEnd_7726584 := by
    simpa [prefixWord, tailWord_7726584, baseEnd_7726584] using wordTrace_append hprefix tailTrace_7726584
  have hstable : (prefixWord ++ tailWord_7726584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726584).length < 2 ^ (prefixWord ++ tailWord_7726584).sum := by decide
  have hdescent : baseEnd_7726584 < baseStart_7726584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726598 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_7726598 : Nat := 118140960795 + 7726598 * 2 ^ 59
def prefixEnd_7726598 : Nat := 4983230072969 + 3 ^ 40 * 7726598 * 2
def baseEnd_7726598 : Nat := 440828733118696209276781

theorem tailTrace_7726598 : CollatzResearch.WordTrace tailWord_7726598 prefixEnd_7726598 440828733118696209276781 := by
  unfold tailWord_7726598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8806630651933203710154889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187874787241241679149970965 8806630651933203710154889)
  ·
    refine ⟨6604972988949902782616167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8806630651933203710154889 6604972988949902782616167)
    ·
      refine ⟨9907459483424854173924251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6604972988949902782616167 9907459483424854173924251)
      ·
        refine ⟨14861189225137281260886377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9907459483424854173924251 14861189225137281260886377)
        ·
          refine ⟨11145891918852960945664783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14861189225137281260886377 11145891918852960945664783)
          ·
            refine ⟨16718837878279441418497175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11145891918852960945664783 16718837878279441418497175)
            ·
              refine ⟨25078256817419162127745763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16718837878279441418497175 25078256817419162127745763)
              ·
                refine ⟨37617385226128743191618645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25078256817419162127745763 37617385226128743191618645)
                ·
                  refine ⟨440828733118696209276781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37617385226128743191618645 440828733118696209276781)
                  ·
                    rfl

theorem cell23_7726598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_7726598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726598 prefixEnd_7726598 := by exact prefixLift 7726598
  have htrace : WordTrace (prefixWord ++ tailWord_7726598) baseStart_7726598 baseEnd_7726598 := by
    simpa [prefixWord, tailWord_7726598, baseEnd_7726598] using wordTrace_append hprefix tailTrace_7726598
  have hstable : (prefixWord ++ tailWord_7726598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726598).length < 2 ^ (prefixWord ++ tailWord_7726598).sum := by decide
  have hdescent : baseEnd_7726598 < baseStart_7726598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726624 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 1, 6]
def baseStart_7726624 : Nat := 118140960795 + 7726624 * 2 ^ 59
def prefixEnd_7726624 : Nat := 4983230072969 + 3 ^ 40 * 7726624 * 2
def baseEnd_7726624 : Nat := 1322490649521760927255303

theorem tailTrace_7726624 : CollatzResearch.WordTrace tailWord_7726624 prefixEnd_7726624 1322490649521760927255303 := by
  unfold tailWord_7726624
  simp only [CollatzResearch.WordTrace]
  refine ⟨140906564579884162582701463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187875419439845550110268617 140906564579884162582701463)
  ·
    refine ⟨211359846869826243874052195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140906564579884162582701463 211359846869826243874052195)
    ·
      refine ⟨317039770304739365811078293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211359846869826243874052195 317039770304739365811078293)
      ·
        refine ⟨14861239233034657772394295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 317039770304739365811078293 14861239233034657772394295)
        ·
          refine ⟨22291858849551986658591443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14861239233034657772394295 22291858849551986658591443)
          ·
            refine ⟨33437788274327979987887165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22291858849551986658591443 33437788274327979987887165)
            ·
              refine ⟨12539170602872992495457687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33437788274327979987887165 12539170602872992495457687)
              ·
                refine ⟨18808755904309488743186531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12539170602872992495457687 18808755904309488743186531)
                ·
                  refine ⟨28213133856464233114779797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18808755904309488743186531 28213133856464233114779797)
                  ·
                    refine ⟨1322490649521760927255303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28213133856464233114779797 1322490649521760927255303)
                    ·
                      rfl

theorem cell23_7726624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 1, 6].length) (baseStart_7726624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726624 prefixEnd_7726624 := by exact prefixLift 7726624
  have htrace : WordTrace (prefixWord ++ tailWord_7726624) baseStart_7726624 baseEnd_7726624 := by
    simpa [prefixWord, tailWord_7726624, baseEnd_7726624] using wordTrace_append hprefix tailTrace_7726624
  have hstable : (prefixWord ++ tailWord_7726624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726624).length < 2 ^ (prefixWord ++ tailWord_7726624).sum := by decide
  have hdescent : baseEnd_7726624 < baseStart_7726624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726691 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 3, 3, 2]
def baseStart_7726691 : Nat := 118140960795 + 7726691 * 2 ^ 59
def prefixEnd_7726691 : Nat := 4983230072969 + 3 ^ 40 * 7726691 * 2
def baseEnd_7726691 : Nat := 3967506351769134019628101

theorem tailTrace_7726691 : CollatzResearch.WordTrace tailWord_7726691 prefixEnd_7726691 3967506351769134019628101 := by
  unfold tailWord_7726691
  simp only [CollatzResearch.WordTrace]
  refine ⟨281815572850525595608091927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187877048567017063738727951 281815572850525595608091927)
  ·
    refine ⟨422723359275788393412137891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281815572850525595608091927 422723359275788393412137891)
    ·
      refine ⟨634085038913682590118206837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422723359275788393412137891 634085038913682590118206837)
      ·
        refine ⟨59445472398157742823581891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 634085038913682590118206837 59445472398157742823581891)
        ·
          refine ⟨89168208597236614235372837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59445472398157742823581891 89168208597236614235372837)
          ·
            refine ⟨16719039111981865169132407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89168208597236614235372837 16719039111981865169132407)
            ·
              refine ⟨25078558667972797753698611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16719039111981865169132407 25078558667972797753698611)
              ·
                refine ⟨37617838001959196630547917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25078558667972797753698611 37617838001959196630547917)
                ·
                  refine ⟨14106689250734698736455469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37617838001959196630547917 14106689250734698736455469)
                  ·
                    refine ⟨5290008469025512026170801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14106689250734698736455469 5290008469025512026170801)
                    ·
                      refine ⟨3967506351769134019628101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5290008469025512026170801 3967506351769134019628101)
                      ·
                        rfl

theorem cell23_7726691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_7726691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726691 prefixEnd_7726691 := by exact prefixLift 7726691
  have htrace : WordTrace (prefixWord ++ tailWord_7726691) baseStart_7726691 baseEnd_7726691 := by
    simpa [prefixWord, tailWord_7726691, baseEnd_7726691] using wordTrace_append hprefix tailTrace_7726691
  have hstable : (prefixWord ++ tailWord_7726691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726691).length < 2 ^ (prefixWord ++ tailWord_7726691).sum := by decide
  have hdescent : baseEnd_7726691 < baseStart_7726691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726734 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_7726734 : Nat := 118140960795 + 7726734 * 2 ^ 59
def prefixEnd_7726734 : Nat := 4983230072969 + 3 ^ 40 * 7726734 * 2
def baseEnd_7726734 : Nat := 3967528431437277351390403

theorem tailTrace_7726734 : CollatzResearch.WordTrace tailWord_7726734 prefixEnd_7726734 3967528431437277351390403 := by
  unfold tailWord_7726734
  simp only [CollatzResearch.WordTrace]
  refine ⟨35227142648671226743988407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187878094126246542634604837 35227142648671226743988407)
  ·
    refine ⟨52840713973006840115982611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35227142648671226743988407 52840713973006840115982611)
    ·
      refine ⟨79261070959510260173973917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52840713973006840115982611 79261070959510260173973917)
      ·
        refine ⟨29722901609816347565240219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79261070959510260173973917 29722901609816347565240219)
        ·
          refine ⟨44584352414724521347860329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29722901609816347565240219 44584352414724521347860329)
          ·
            refine ⟨33438264311043391010895247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44584352414724521347860329 33438264311043391010895247)
            ·
              refine ⟨50157396466565086516342871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33438264311043391010895247 50157396466565086516342871)
              ·
                refine ⟨75236094699847629774514307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50157396466565086516342871 75236094699847629774514307)
                ·
                  refine ⟨112854142049771444661771461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75236094699847629774514307 112854142049771444661771461)
                  ·
                    refine ⟨21160151634332145874082149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112854142049771444661771461 21160151634332145874082149)
                    ·
                      refine ⟨3967528431437277351390403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21160151634332145874082149 3967528431437277351390403)
                      ·
                        rfl

theorem cell23_7726734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_7726734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726734 prefixEnd_7726734 := by exact prefixLift 7726734
  have htrace : WordTrace (prefixWord ++ tailWord_7726734) baseStart_7726734 baseEnd_7726734 := by
    simpa [prefixWord, tailWord_7726734, baseEnd_7726734] using wordTrace_append hprefix tailTrace_7726734
  have hstable : (prefixWord ++ tailWord_7726734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726734).length < 2 ^ (prefixWord ++ tailWord_7726734).sum := by decide
  have hdescent : baseEnd_7726734 < baseStart_7726734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726744 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 7]
def baseStart_7726744 : Nat := 118140960795 + 7726744 * 2 ^ 59
def prefixEnd_7726744 : Nat := 4983230072969 + 3 ^ 40 * 7726744 * 2
def baseEnd_7726744 : Nat := 440837062915980256918373

theorem tailTrace_7726744 : CollatzResearch.WordTrace tailWord_7726744 prefixEnd_7726744 440837062915980256918373 := by
  unfold tailWord_7726744
  simp only [CollatzResearch.WordTrace]
  refine ⟨140908752959666792829885643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187878337279555723773180857 140908752959666792829885643)
  ·
    refine ⟨211363129439500189244828465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140908752959666792829885643 211363129439500189244828465)
    ·
      refine ⟨158522347079625141933621349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211363129439500189244828465 158522347079625141933621349)
      ·
        refine ⟨29722940077429714112554003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158522347079625141933621349 29722940077429714112554003)
        ·
          refine ⟨44584410116144571168831005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29722940077429714112554003 44584410116144571168831005)
          ·
            refine ⟨16719153793554214188311627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44584410116144571168831005 16719153793554214188311627)
            ·
              refine ⟨25078730690331321282467441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16719153793554214188311627 25078730690331321282467441)
              ·
                refine ⟨18809048017748490961850581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25078730690331321282467441 18809048017748490961850581)
                ·
                  refine ⟨440837062915980256918373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18809048017748490961850581 440837062915980256918373)
                  ·
                    rfl

theorem cell23_7726744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 7].length) (baseStart_7726744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726744 prefixEnd_7726744 := by exact prefixLift 7726744
  have htrace : WordTrace (prefixWord ++ tailWord_7726744) baseStart_7726744 baseEnd_7726744 := by
    simpa [prefixWord, tailWord_7726744, baseEnd_7726744] using wordTrace_append hprefix tailTrace_7726744
  have hstable : (prefixWord ++ tailWord_7726744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726744).length < 2 ^ (prefixWord ++ tailWord_7726744).sum := by decide
  have hdescent : baseEnd_7726744 < baseStart_7726744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726812 : List Nat := [2, 2, 5, 1, 3, 1, 1, 3, 5]
def baseStart_7726812 : Nat := 118140960795 + 7726812 * 2 ^ 59
def prefixEnd_7726812 : Nat := 4983230072969 + 3 ^ 40 * 7726812 * 2
def baseEnd_7726812 : Nat := 440840942547592005135005

theorem tailTrace_7726812 : CollatzResearch.WordTrace tailWord_7726812 prefixEnd_7726812 440840942547592005135005 := by
  unfold tailWord_7726812
  simp only [CollatzResearch.WordTrace]
  refine ⟨140909993041543616636623345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187879990722058155515497793 140909993041543616636623345)
  ·
    refine ⟨105682494781157712477467509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140909993041543616636623345 105682494781157712477467509)
    ·
      refine ⟨9907733885733535544762579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105682494781157712477467509 9907733885733535544762579)
      ·
        refine ⟨14861600828600303317143869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9907733885733535544762579 14861600828600303317143869)
        ·
          refine ⟨5573100310725113743928951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14861600828600303317143869 5573100310725113743928951)
          ·
            refine ⟨8359650466087670615893427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5573100310725113743928951 8359650466087670615893427)
            ·
              refine ⟨12539475699131505923840141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8359650466087670615893427 12539475699131505923840141)
              ·
                refine ⟨4702303387174314721440053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12539475699131505923840141 4702303387174314721440053)
                ·
                  refine ⟨440840942547592005135005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4702303387174314721440053 440840942547592005135005)
                  ·
                    rfl

theorem cell23_7726812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 5].length) (baseStart_7726812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726812 prefixEnd_7726812 := by exact prefixLift 7726812
  have htrace : WordTrace (prefixWord ++ tailWord_7726812) baseStart_7726812 baseEnd_7726812 := by
    simpa [prefixWord, tailWord_7726812, baseEnd_7726812] using wordTrace_append hprefix tailTrace_7726812
  have hstable : (prefixWord ++ tailWord_7726812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726812).length < 2 ^ (prefixWord ++ tailWord_7726812).sum := by decide
  have hdescent : baseEnd_7726812 < baseStart_7726812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726831 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 3]
def baseStart_7726831 : Nat := 118140960795 + 7726831 * 2 ^ 59
def prefixEnd_7726831 : Nat := 4983230072969 + 3 ^ 40 * 7726831 * 2
def baseEnd_7726831 : Nat := 3967578239060763471877457

theorem tailTrace_7726831 : CollatzResearch.WordTrace tailWord_7726831 prefixEnd_7726831 3967578239060763471877457 := by
  unfold tailWord_7726831
  simp only [CollatzResearch.WordTrace]
  refine ⟨281820679070018399518188347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187880452713345599678792231 281820679070018399518188347)
  ·
    refine ⟨422731018605027599277282521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281820679070018399518188347 422731018605027599277282521)
    ·
      refine ⟨317048263953770699457961891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422731018605027599277282521 317048263953770699457961891)
      ·
        refine ⟨475572395930656049186942837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317048263953770699457961891 475572395930656049186942837)
        ·
          refine ⟨44584912118499004611275891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 475572395930656049186942837 44584912118499004611275891)
          ·
            refine ⟨66877368177748506916913837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44584912118499004611275891 66877368177748506916913837)
            ·
              refine ⟨25079013066655690093842689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66877368177748506916913837 25079013066655690093842689)
              ·
                refine ⟨18809259799991767570382017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25079013066655690093842689 18809259799991767570382017)
                ·
                  refine ⟨14106944849993825677786513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18809259799991767570382017 14106944849993825677786513)
                  ·
                    refine ⟨10580208637495369258339885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14106944849993825677786513 10580208637495369258339885)
                    ·
                      refine ⟨3967578239060763471877457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10580208637495369258339885 3967578239060763471877457)
                      ·
                        rfl

theorem cell23_7726831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 3].length) (baseStart_7726831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726831 prefixEnd_7726831 := by exact prefixLift 7726831
  have htrace : WordTrace (prefixWord ++ tailWord_7726831) baseStart_7726831 baseEnd_7726831 := by
    simpa [prefixWord, tailWord_7726831, baseEnd_7726831] using wordTrace_append hprefix tailTrace_7726831
  have hstable : (prefixWord ++ tailWord_7726831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726831).length < 2 ^ (prefixWord ++ tailWord_7726831).sum := by decide
  have hdescent : baseEnd_7726831 < baseStart_7726831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726834 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 8]
def baseStart_7726834 : Nat := 118140960795 + 7726834 * 2 ^ 59
def prefixEnd_7726834 : Nat := 4983230072969 + 3 ^ 40 * 7726834 * 2
def baseEnd_7726834 : Nat := 440842197722525217793327

theorem tailTrace_7726834 : CollatzResearch.WordTrace tailWord_7726834 prefixEnd_7726834 440842197722525217793327 := by
  unfold tailWord_7726834
  simp only [CollatzResearch.WordTrace]
  refine ⟨70455197122251882757636889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187880525659338354020365037 70455197122251882757636889)
  ·
    refine ⟨52841397841688912068227667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70455197122251882757636889 52841397841688912068227667)
    ·
      refine ⟨79262096762533368102341501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52841397841688912068227667 79262096762533368102341501)
      ·
        refine ⟨29723286285950013038378063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79262096762533368102341501 29723286285950013038378063)
        ·
          refine ⟨44584929428925019557567095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29723286285950013038378063 44584929428925019557567095)
          ·
            refine ⟨66877394143387529336350643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44584929428925019557567095 66877394143387529336350643)
            ·
              refine ⟨100316091215081294004525965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66877394143387529336350643 100316091215081294004525965)
              ·
                refine ⟨37618534205655485251697237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100316091215081294004525965 37618534205655485251697237)
                ·
                  refine ⟨440842197722525217793327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37618534205655485251697237 440842197722525217793327)
                  ·
                    rfl

theorem cell23_7726834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_7726834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726834 prefixEnd_7726834 := by exact prefixLift 7726834
  have htrace : WordTrace (prefixWord ++ tailWord_7726834) baseStart_7726834 baseEnd_7726834 := by
    simpa [prefixWord, tailWord_7726834, baseEnd_7726834] using wordTrace_append hprefix tailTrace_7726834
  have hstable : (prefixWord ++ tailWord_7726834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726834).length < 2 ^ (prefixWord ++ tailWord_7726834).sum := by decide
  have hdescent : baseEnd_7726834 < baseStart_7726834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726838 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_7726838 : Nat := 118140960795 + 7726838 * 2 ^ 59
def prefixEnd_7726838 : Nat := 4983230072969 + 3 ^ 40 * 7726838 * 2
def baseEnd_7726838 : Nat := 1322527277808448314829975

theorem tailTrace_7726838 : CollatzResearch.WordTrace tailWord_7726838 prefixEnd_7726838 1322527277808448314829975 := by
  unfold tailWord_7726838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17613808398812064982105823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187880622920662026475795445 17613808398812064982105823)
  ·
    refine ⟨26420712598218097473158735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17613808398812064982105823 26420712598218097473158735)
    ·
      refine ⟨39631068897327146209738103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26420712598218097473158735 39631068897327146209738103)
      ·
        refine ⟨59446603345990719314607155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39631068897327146209738103 59446603345990719314607155)
        ·
          refine ⟨89169905018986078971910733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59446603345990719314607155 89169905018986078971910733)
          ·
            refine ⟨33438714382119779614466525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89169905018986078971910733 33438714382119779614466525)
            ·
              refine ⟨12539517893294917355424947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33438714382119779614466525 12539517893294917355424947)
              ·
                refine ⟨18809276839942376033137421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12539517893294917355424947 18809276839942376033137421)
                ·
                  refine ⟨7053478814978391012426533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18809276839942376033137421 7053478814978391012426533)
                  ·
                    refine ⟨1322527277808448314829975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7053478814978391012426533 1322527277808448314829975)
                    ·
                      rfl

theorem cell23_7726838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_7726838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726838 prefixEnd_7726838 := by exact prefixLift 7726838
  have htrace : WordTrace (prefixWord ++ tailWord_7726838) baseStart_7726838 baseEnd_7726838 := by
    simpa [prefixWord, tailWord_7726838, baseEnd_7726838] using wordTrace_append hprefix tailTrace_7726838
  have hstable : (prefixWord ++ tailWord_7726838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726838).length < 2 ^ (prefixWord ++ tailWord_7726838).sum := by decide
  have hdescent : baseEnd_7726838 < baseStart_7726838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726851 : List Nat := [1, 1, 1, 3, 2, 2, 6, 1, 6]
def baseStart_7726851 : Nat := 118140960795 + 7726851 * 2 ^ 59
def prefixEnd_7726851 : Nat := 4983230072969 + 3 ^ 40 * 7726851 * 2
def baseEnd_7726851 : Nat := 440843167630428154847485

theorem tailTrace_7726851 : CollatzResearch.WordTrace tailWord_7726851 prefixEnd_7726851 440843167630428154847485 := by
  unfold tailWord_7726851
  simp only [CollatzResearch.WordTrace]
  refine ⟨281821408529945942933916407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187880939019963961955944271 281821408529945942933916407)
  ·
    refine ⟨422732112794918914400874611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281821408529945942933916407 422732112794918914400874611)
    ·
      refine ⟨634098169192378371601311917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422732112794918914400874611 634098169192378371601311917)
      ·
        refine ⟨237786813447141889350491969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 634098169192378371601311917 237786813447141889350491969)
        ·
          refine ⟨178340110085356417012868977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237786813447141889350491969 178340110085356417012868977)
          ·
            refine ⟨133755082564017312759651733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178340110085356417012868977 133755082564017312759651733)
            ·
              refine ⟨6269769495188311535608675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133755082564017312759651733 6269769495188311535608675)
              ·
                refine ⟨9404654242782467303413013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6269769495188311535608675 9404654242782467303413013)
                ·
                  refine ⟨440843167630428154847485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9404654242782467303413013 440843167630428154847485)
                  ·
                    rfl

theorem cell23_7726851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 6].length) (baseStart_7726851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726851 prefixEnd_7726851 := by exact prefixLift 7726851
  have htrace : WordTrace (prefixWord ++ tailWord_7726851) baseStart_7726851 baseEnd_7726851 := by
    simpa [prefixWord, tailWord_7726851, baseEnd_7726851] using wordTrace_append hprefix tailTrace_7726851
  have hstable : (prefixWord ++ tailWord_7726851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726851).length < 2 ^ (prefixWord ++ tailWord_7726851).sum := by decide
  have hdescent : baseEnd_7726851 < baseStart_7726851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726921 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 3, 2, 3]
def baseStart_7726921 : Nat := 118140960795 + 7726921 * 2 ^ 59
def prefixEnd_7726921 : Nat := 4983230072969 + 3 ^ 40 * 7726921 * 2
def baseEnd_7726921 : Nat := 3967624452319668119752043

theorem tailTrace_7726921 : CollatzResearch.WordTrace tailWord_7726921 prefixEnd_7726921 3967624452319668119752043 := by
  unfold tailWord_7726921
  simp only [CollatzResearch.WordTrace]
  refine ⟨281823961639692344888964617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187882641093128229925976411 281823961639692344888964617)
  ·
    refine ⟨211367971229769258666723463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281823961639692344888964617 211367971229769258666723463)
    ·
      refine ⟨317051956844653888000085195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211367971229769258666723463 317051956844653888000085195)
      ·
        refine ⟨475577935266980832000127793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317051956844653888000085195 475577935266980832000127793)
        ·
          refine ⟨356683451450235624000095845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475577935266980832000127793 356683451450235624000095845)
          ·
            refine ⟨66878147146919179500017971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356683451450235624000095845 66878147146919179500017971)
            ·
              refine ⟨100317220720378769250026957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66878147146919179500017971 100317220720378769250026957)
              ·
                refine ⟨37618957770142038468760109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100317220720378769250026957 37618957770142038468760109)
                ·
                  refine ⟨14107109163803264425785041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37618957770142038468760109 14107109163803264425785041)
                  ·
                    refine ⟨10580331872852448319338781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14107109163803264425785041 10580331872852448319338781)
                    ·
                      refine ⟨3967624452319668119752043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10580331872852448319338781 3967624452319668119752043)
                      ·
                        rfl

theorem cell23_7726921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 2, 3].length) (baseStart_7726921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726921 prefixEnd_7726921 := by exact prefixLift 7726921
  have htrace : WordTrace (prefixWord ++ tailWord_7726921) baseStart_7726921 baseEnd_7726921 := by
    simpa [prefixWord, tailWord_7726921, baseEnd_7726921] using wordTrace_append hprefix tailTrace_7726921
  have hstable : (prefixWord ++ tailWord_7726921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726921).length < 2 ^ (prefixWord ++ tailWord_7726921).sum := by decide
  have hdescent : baseEnd_7726921 < baseStart_7726921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726938 : List Nat := [3, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3]
def baseStart_7726938 : Nat := 118140960795 + 7726938 * 2 ^ 59
def prefixEnd_7726938 : Nat := 4983230072969 + 3 ^ 40 * 7726938 * 2
def baseEnd_7726938 : Nat := 3967633181490794553239465

theorem tailTrace_7726938 : CollatzResearch.WordTrace tailWord_7726938 prefixEnd_7726938 3967633181490794553239465 := by
  unfold tailWord_7726938
  simp only [CollatzResearch.WordTrace]
  refine ⟨70456145420157689198083367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187883054453753837861555645 70456145420157689198083367)
  ·
    refine ⟨105684218130236533797125051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70456145420157689198083367 105684218130236533797125051)
    ·
      refine ⟨158526327195354800695687577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105684218130236533797125051 158526327195354800695687577)
      ·
        refine ⟨118894745396516100521765683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158526327195354800695687577 118894745396516100521765683)
        ·
          refine ⟨178342118094774150782648525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118894745396516100521765683 178342118094774150782648525)
          ·
            refine ⟨66878294285540306543493197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178342118094774150782648525 66878294285540306543493197)
            ·
              refine ⟨25079360357077614953809949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66878294285540306543493197 25079360357077614953809949)
              ·
                refine ⟨9404760133904105607678731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25079360357077614953809949 9404760133904105607678731)
                ·
                  refine ⟨14107140200856158411518097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9404760133904105607678731 14107140200856158411518097)
                  ·
                    refine ⟨10580355150642118808638573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14107140200856158411518097 10580355150642118808638573)
                    ·
                      refine ⟨3967633181490794553239465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10580355150642118808638573 3967633181490794553239465)
                      ·
                        rfl

theorem cell23_7726938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_7726938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726938 prefixEnd_7726938 := by exact prefixLift 7726938
  have htrace : WordTrace (prefixWord ++ tailWord_7726938) baseStart_7726938 baseEnd_7726938 := by
    simpa [prefixWord, tailWord_7726938, baseEnd_7726938] using wordTrace_append hprefix tailTrace_7726938
  have hstable : (prefixWord ++ tailWord_7726938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726938).length < 2 ^ (prefixWord ++ tailWord_7726938).sum := by decide
  have hdescent : baseEnd_7726938 < baseStart_7726938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726952 : List Nat := [2, 1, 4, 2, 1, 1, 1, 6, 1, 2, 2]
def baseStart_7726952 : Nat := 118140960795 + 7726952 * 2 ^ 59
def prefixEnd_7726952 : Nat := 4983230072969 + 3 ^ 40 * 7726952 * 2
def baseEnd_7726952 : Nat := 3967640370219957498464401

theorem tailTrace_7726952 : CollatzResearch.WordTrace tailWord_7726952 prefixEnd_7726952 3967640370219957498464401 := by
  unfold tailWord_7726952
  simp only [CollatzResearch.WordTrace]
  refine ⟨140912546151290018591671555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187883394868386691455562073 140912546151290018591671555)
  ·
    refine ⟨211368819226935027887507333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140912546151290018591671555 211368819226935027887507333)
    ·
      refine ⟨39631653605050317728907625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211368819226935027887507333 39631653605050317728907625)
      ·
        refine ⟨29723740203787738296680719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39631653605050317728907625 29723740203787738296680719)
        ·
          refine ⟨44585610305681607445021079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29723740203787738296680719 44585610305681607445021079)
          ·
            refine ⟨66878415458522411167531619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44585610305681607445021079 66878415458522411167531619)
            ·
              refine ⟨100317623187783616751297429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66878415458522411167531619 100317623187783616751297429)
              ·
                refine ⟨4702388586927357035217067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100317623187783616751297429 4702388586927357035217067)
                ·
                  refine ⟨7053582880391035552825601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4702388586927357035217067 7053582880391035552825601)
                  ·
                    refine ⟨5290187160293276664619201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7053582880391035552825601 5290187160293276664619201)
                    ·
                      refine ⟨3967640370219957498464401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5290187160293276664619201 3967640370219957498464401)
                      ·
                        rfl

theorem cell23_7726952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_7726952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726952 prefixEnd_7726952 := by exact prefixLift 7726952
  have htrace : WordTrace (prefixWord ++ tailWord_7726952) baseStart_7726952 baseEnd_7726952 := by
    simpa [prefixWord, tailWord_7726952, baseEnd_7726952] using wordTrace_append hprefix tailTrace_7726952
  have hstable : (prefixWord ++ tailWord_7726952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726952).length < 2 ^ (prefixWord ++ tailWord_7726952).sum := by decide
  have hdescent : baseEnd_7726952 < baseStart_7726952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726986 : List Nat := [3, 1, 2, 4, 2, 2, 1, 3, 1, 2, 2]
def baseStart_7726986 : Nat := 118140960795 + 7726986 * 2 ^ 59
def prefixEnd_7726986 : Nat := 4983230072969 + 3 ^ 40 * 7726986 * 2
def baseEnd_7726986 : Nat := 3967657828562210365439245

theorem tailTrace_7726986 : CollatzResearch.WordTrace tailWord_7726986 prefixEnd_7726986 3967657828562210365439245 := by
  unfold tailWord_7726986
  simp only [CollatzResearch.WordTrace]
  refine ⟨70456583096114215247520203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187884221589637907326720541 70456583096114215247520203)
  ·
    refine ⟨105684874644171322871280305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70456583096114215247520203 105684874644171322871280305)
    ·
      refine ⟨79263655983128492153460229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105684874644171322871280305 79263655983128492153460229)
      ·
        refine ⟨14861935496836592278773793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79263655983128492153460229 14861935496836592278773793)
        ·
          refine ⟨11146451622627444209080345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14861935496836592278773793 11146451622627444209080345)
          ·
            refine ⟨8359838716970583156810259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11146451622627444209080345 8359838716970583156810259)
            ·
              refine ⟨12539758075455874735215389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8359838716970583156810259 12539758075455874735215389)
              ·
                refine ⟨4702409278295953025705771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12539758075455874735215389 4702409278295953025705771)
                ·
                  refine ⟨7053613917443929538558657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4702409278295953025705771 7053613917443929538558657)
                  ·
                    refine ⟨5290210438082947153918993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7053613917443929538558657 5290210438082947153918993)
                    ·
                      refine ⟨3967657828562210365439245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5290210438082947153918993 3967657828562210365439245)
                      ·
                        rfl

theorem cell23_7726986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_7726986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726986 prefixEnd_7726986 := by exact prefixLift 7726986
  have htrace : WordTrace (prefixWord ++ tailWord_7726986) baseStart_7726986 baseEnd_7726986 := by
    simpa [prefixWord, tailWord_7726986, baseEnd_7726986] using wordTrace_append hprefix tailTrace_7726986
  have hstable : (prefixWord ++ tailWord_7726986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726986).length < 2 ^ (prefixWord ++ tailWord_7726986).sum := by decide
  have hdescent : baseEnd_7726986 < baseStart_7726986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727011 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 3]
def baseStart_7727011 : Nat := 118140960795 + 7727011 * 2 ^ 59
def prefixEnd_7727011 : Nat := 4983230072969 + 3 ^ 40 * 7727011 * 2
def baseEnd_7727011 : Nat := 3967670665578572767626629

theorem tailTrace_7727011 : CollatzResearch.WordTrace tailWord_7727011 prefixEnd_7727011 3967670665578572767626629 := by
  unfold tailWord_7727011
  simp only [CollatzResearch.WordTrace]
  refine ⟨281827244209366290259740887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187884829472910860173160591 281827244209366290259740887)
  ·
    refine ⟨422740866314049435389611331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281827244209366290259740887 422740866314049435389611331)
    ·
      refine ⟨634111299471074153084416997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422740866314049435389611331 634111299471074153084416997)
      ·
        refine ⟨118895868650826403703328187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 634111299471074153084416997 118895868650826403703328187)
        ·
          refine ⟨178343802976239605554992281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118895868650826403703328187 178343802976239605554992281)
          ·
            refine ⟨133757852232179704166244211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178343802976239605554992281 133757852232179704166244211)
            ·
              refine ⟨200636778348269556249366317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133757852232179704166244211 200636778348269556249366317)
              ·
                refine ⟨75238791880601083593512369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200636778348269556249366317 75238791880601083593512369)
                ·
                  refine ⟨56429093910450812695134277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75238791880601083593512369 56429093910450812695134277)
                  ·
                    refine ⟨10580455108209527380337677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56429093910450812695134277 10580455108209527380337677)
                    ·
                      refine ⟨3967670665578572767626629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10580455108209527380337677 3967670665578572767626629)
                      ·
                        rfl

theorem cell23_7727011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_7727011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727011 prefixEnd_7727011 := by exact prefixLift 7727011
  have htrace : WordTrace (prefixWord ++ tailWord_7727011) baseStart_7727011 baseEnd_7727011 := by
    simpa [prefixWord, tailWord_7727011, baseEnd_7727011] using wordTrace_append hprefix tailTrace_7727011
  have hstable : (prefixWord ++ tailWord_7727011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727011).length < 2 ^ (prefixWord ++ tailWord_7727011).sum := by decide
  have hdescent : baseEnd_7727011 < baseStart_7727011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727065 : List Nat := [1, 2, 1, 2, 6, 1, 1, 4, 5]
def baseStart_7727065 : Nat := 118140960795 + 7727065 * 2 ^ 59
def prefixEnd_7727065 : Nat := 4983230072969 + 3 ^ 40 * 7727065 * 2
def baseEnd_7727065 : Nat := 440855377059323950705709

theorem tailTrace_7727065 : CollatzResearch.WordTrace tailWord_7727065 prefixEnd_7727065 440855377059323950705709 := by
  unfold tailWord_7727065
  simp only [CollatzResearch.WordTrace]
  refine ⟨281829213751170657482206649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187886142500780438321471099 281829213751170657482206649)
  ·
    refine ⟨211371910313377993111654987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281829213751170657482206649 211371910313377993111654987)
    ·
      refine ⟨317057865470066989667482481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211371910313377993111654987 317057865470066989667482481)
      ·
        refine ⟨237793399102550242250611861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317057865470066989667482481 237793399102550242250611861)
        ·
          refine ⟨11146565582932042605497431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 237793399102550242250611861 11146565582932042605497431)
          ·
            refine ⟨16719848374398063908246147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11146565582932042605497431 16719848374398063908246147)
            ·
              refine ⟨25079772561597095862369221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16719848374398063908246147 25079772561597095862369221)
              ·
                refine ⟨4702457355299455474194229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25079772561597095862369221 4702457355299455474194229)
                ·
                  refine ⟨440855377059323950705709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4702457355299455474194229 440855377059323950705709)
                  ·
                    rfl

theorem cell23_7727065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 5].length) (baseStart_7727065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727065 prefixEnd_7727065 := by exact prefixLift 7727065
  have htrace : WordTrace (prefixWord ++ tailWord_7727065) baseStart_7727065 baseEnd_7727065 := by
    simpa [prefixWord, tailWord_7727065, baseEnd_7727065] using wordTrace_append hprefix tailTrace_7727065
  have hstable : (prefixWord ++ tailWord_7727065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727065).length < 2 ^ (prefixWord ++ tailWord_7727065).sum := by decide
  have hdescent : baseEnd_7727065 < baseStart_7727065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727182 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3]
def baseStart_7727182 : Nat := 118140960795 + 7727182 * 2 ^ 59
def prefixEnd_7727182 : Nat := 4983230072969 + 3 ^ 40 * 7727182 * 2
def baseEnd_7727182 : Nat := 3967758470770491598588343

theorem tailTrace_7727182 : CollatzResearch.WordTrace tailWord_7727182 prefixEnd_7727182 3967758470770491598588343 := by
  unfold tailWord_7727182
  simp only [CollatzResearch.WordTrace]
  refine ⟨35229185136468348308026975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187888987394497857642810533 35229185136468348308026975)
  ·
    refine ⟨52843777704702522462040463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35229185136468348308026975 52843777704702522462040463)
    ·
      refine ⟨79265666557053783693060695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52843777704702522462040463 79265666557053783693060695)
      ·
        refine ⟨118898499835580675539591043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79265666557053783693060695 118898499835580675539591043)
        ·
          refine ⟨178347749753371013309386565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118898499835580675539591043 178347749753371013309386565)
          ·
            refine ⟨33440203078757064995509981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178347749753371013309386565 33440203078757064995509981)
            ·
              refine ⟨12540076154533899373316243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33440203078757064995509981 12540076154533899373316243)
              ·
                refine ⟨18810114231800849059974365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12540076154533899373316243 18810114231800849059974365)
                ·
                  refine ⟨7053792836925318397490387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18810114231800849059974365 7053792836925318397490387)
                  ·
                    refine ⟨10580689255387977596235581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7053792836925318397490387 10580689255387977596235581)
                    ·
                      refine ⟨3967758470770491598588343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10580689255387977596235581 3967758470770491598588343)
                      ·
                        rfl

theorem cell23_7727182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_7727182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727182 prefixEnd_7727182 := by exact prefixLift 7727182
  have htrace : WordTrace (prefixWord ++ tailWord_7727182) baseStart_7727182 baseEnd_7727182 := by
    simpa [prefixWord, tailWord_7727182, baseEnd_7727182] using wordTrace_append hprefix tailTrace_7727182
  have hstable : (prefixWord ++ tailWord_7727182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727182).length < 2 ^ (prefixWord ++ tailWord_7727182).sum := by decide
  have hdescent : baseEnd_7727182 < baseStart_7727182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727188 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_7727188 : Nat := 118140960795 + 7727188 * 2 ^ 59
def prefixEnd_7727188 : Nat := 4983230072969 + 3 ^ 40 * 7727188 * 2
def baseEnd_7727188 : Nat := 3967761551654418575113315

theorem tailTrace_7727188 : CollatzResearch.WordTrace tailWord_7727188 prefixEnd_7727188 3967761551654418575113315 := by
  unfold tailWord_7727188
  simp only [CollatzResearch.WordTrace]
  refine ⟨140916849964862524744467109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187889133286483366325956145 140916849964862524744467109)
  ·
    refine ⟨26421909368411723389587583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140916849964862524744467109 26421909368411723389587583)
    ·
      refine ⟨39632864052617585084381375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26421909368411723389587583 39632864052617585084381375)
      ·
        refine ⟨59449296078926377626572063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39632864052617585084381375 59449296078926377626572063)
        ·
          refine ⟨89173944118389566439858095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59449296078926377626572063 89173944118389566439858095)
          ·
            refine ⟨133760916177584349659787143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89173944118389566439858095 133760916177584349659787143)
            ·
              refine ⟨200641374266376524489680715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133760916177584349659787143 200641374266376524489680715)
              ·
                refine ⟨300962061399564786734521073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200641374266376524489680715 300962061399564786734521073)
                ·
                  refine ⟨225721546049673590050890805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300962061399564786734521073 225721546049673590050890805)
                  ·
                    refine ⟨21161394942156899067271013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 225721546049673590050890805 21161394942156899067271013)
                    ·
                      refine ⟨3967761551654418575113315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21161394942156899067271013 3967761551654418575113315)
                      ·
                        rfl

theorem cell23_7727188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_7727188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727188 prefixEnd_7727188 := by exact prefixLift 7727188
  have htrace : WordTrace (prefixWord ++ tailWord_7727188) baseStart_7727188 baseEnd_7727188 := by
    simpa [prefixWord, tailWord_7727188, baseEnd_7727188] using wordTrace_append hprefix tailTrace_7727188
  have hstable : (prefixWord ++ tailWord_7727188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727188).length < 2 ^ (prefixWord ++ tailWord_7727188).sum := by decide
  have hdescent : baseEnd_7727188 < baseStart_7727188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727202 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_7727202 : Nat := 118140960795 + 7727202 * 2 ^ 59
def prefixEnd_7727202 : Nat := 4983230072969 + 3 ^ 40 * 7727202 * 2
def baseEnd_7727202 : Nat := 1322589580127860506779417

theorem tailTrace_7727202 : CollatzResearch.WordTrace tailWord_7727202 prefixEnd_7727202 1322589580127860506779417 := by
  unfold tailWord_7727202
  simp only [CollatzResearch.WordTrace]
  refine ⟨70458552637918582469985965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187889473701116219919962573 70458552637918582469985965)
  ·
    refine ⟨26421957239219468426244737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70458552637918582469985965 26421957239219468426244737)
    ·
      refine ⟨19816467929414601319683553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26421957239219468426244737 19816467929414601319683553)
      ·
        refine ⟨14862350947060950989762665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19816467929414601319683553 14862350947060950989762665)
        ·
          refine ⟨11146763210295713242321999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14862350947060950989762665 11146763210295713242321999)
          ·
            refine ⟨16720144815443569863482999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11146763210295713242321999 16720144815443569863482999)
            ·
              refine ⟨25080217223165354795224499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16720144815443569863482999 25080217223165354795224499)
              ·
                refine ⟨37620325834748032192836749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25080217223165354795224499 37620325834748032192836749)
                ·
                  refine ⟨14107622188030512072313781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37620325834748032192836749 14107622188030512072313781)
                  ·
                    refine ⟨1322589580127860506779417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14107622188030512072313781 1322589580127860506779417)
                    ·
                      rfl

theorem cell23_7727202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_7727202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727202 prefixEnd_7727202 := by exact prefixLift 7727202
  have htrace : WordTrace (prefixWord ++ tailWord_7727202) baseStart_7727202 baseEnd_7727202 := by
    simpa [prefixWord, tailWord_7727202, baseEnd_7727202] using wordTrace_append hprefix tailTrace_7727202
  have hstable : (prefixWord ++ tailWord_7727202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727202).length < 2 ^ (prefixWord ++ tailWord_7727202).sum := by decide
  have hdescent : baseEnd_7727202 < baseStart_7727202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727205 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 3, 1, 4]
def baseStart_7727205 : Nat := 118140960795 + 7727205 * 2 ^ 59
def prefixEnd_7727205 : Nat := 4983230072969 + 3 ^ 40 * 7727205 * 2
def baseEnd_7727205 : Nat := 3967770280825545008600737

theorem tailTrace_7727205 : CollatzResearch.WordTrace tailWord_7727205 prefixEnd_7727205 3967770280825545008600737 := by
  unfold tailWord_7727205
  simp only [CollatzResearch.WordTrace]
  refine ⟨281834319970663461392303069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187889546647108974261535379 281834319970663461392303069)
  ·
    refine ⟨105687869988998798022113651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281834319970663461392303069 105687869988998798022113651)
    ·
      refine ⟨158531804983498197033170477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105687869988998798022113651 158531804983498197033170477)
      ·
        refine ⟨59449426868811823887438929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158531804983498197033170477 59449426868811823887438929)
        ·
          refine ⟨44587070151608867915579197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59449426868811823887438929 44587070151608867915579197)
          ·
            refine ⟨16720151306853325468342199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44587070151608867915579197 16720151306853325468342199)
            ·
              refine ⟨25080226960279988202513299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16720151306853325468342199 25080226960279988202513299)
              ·
                refine ⟨37620340440419982303769949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25080226960279988202513299 37620340440419982303769949)
                ·
                  refine ⟨14107627665157493363913731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37620340440419982303769949 14107627665157493363913731)
                  ·
                    refine ⟨21161441497736240045870597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14107627665157493363913731 21161441497736240045870597)
                    ·
                      refine ⟨3967770280825545008600737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21161441497736240045870597 3967770280825545008600737)
                      ·
                        rfl

theorem cell23_7727205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_7727205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727205 prefixEnd_7727205 := by exact prefixLift 7727205
  have htrace : WordTrace (prefixWord ++ tailWord_7727205) baseStart_7727205 baseEnd_7727205 := by
    simpa [prefixWord, tailWord_7727205, baseEnd_7727205] using wordTrace_append hprefix tailTrace_7727205
  have hstable : (prefixWord ++ tailWord_7727205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727205).length < 2 ^ (prefixWord ++ tailWord_7727205).sum := by decide
  have hdescent : baseEnd_7727205 < baseStart_7727205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727225 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 1, 1, 5]
def baseStart_7727225 : Nat := 118140960795 + 7727225 * 2 ^ 59
def prefixEnd_7727225 : Nat := 4983230072969 + 3 ^ 40 * 7727225 * 2
def baseEnd_7727225 : Nat := 3967780550438634930350645

theorem tailTrace_7727225 : CollatzResearch.WordTrace tailWord_7727225 prefixEnd_7727225 3967780550438634930350645 := by
  unfold tailWord_7727225
  simp only [CollatzResearch.WordTrace]
  refine ⟨281835049430591004808031129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187890032953727336538687419 281835049430591004808031129)
  ·
    refine ⟨211376287072943253606023347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281835049430591004808031129 211376287072943253606023347)
    ·
      refine ⟨317064430609414880409035021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211376287072943253606023347 317064430609414880409035021)
      ·
        refine ⟨118899161478530580153388133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317064430609414880409035021 118899161478530580153388133)
        ·
          refine ⟨22293592777224483778760275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118899161478530580153388133 22293592777224483778760275)
          ·
            refine ⟨33440389165836725668140413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22293592777224483778760275 33440389165836725668140413)
            ·
              refine ⟨12540145937188772125552655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33440389165836725668140413 12540145937188772125552655)
              ·
                refine ⟨18810218905783158188328983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12540145937188772125552655 18810218905783158188328983)
                ·
                  refine ⟨28215328358674737282493475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18810218905783158188328983 28215328358674737282493475)
                  ·
                    refine ⟨42322992538012105923740213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28215328358674737282493475 42322992538012105923740213)
                    ·
                      refine ⟨3967780550438634930350645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42322992538012105923740213 3967780550438634930350645)
                      ·
                        rfl

theorem cell23_7727225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_7727225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727225 prefixEnd_7727225 := by exact prefixLift 7727225
  have htrace : WordTrace (prefixWord ++ tailWord_7727225) baseStart_7727225 baseEnd_7727225 := by
    simpa [prefixWord, tailWord_7727225, baseEnd_7727225] using wordTrace_append hprefix tailTrace_7727225
  have hstable : (prefixWord ++ tailWord_7727225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727225).length < 2 ^ (prefixWord ++ tailWord_7727225).sum := by decide
  have hdescent : baseEnd_7727225 < baseStart_7727225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727233 : List Nat := [1, 2, 4, 2, 3, 2, 2, 2, 1, 1, 3]
def baseStart_7727233 : Nat := 118140960795 + 7727233 * 2 ^ 59
def prefixEnd_7727233 : Nat := 4983230072969 + 3 ^ 40 * 7727233 * 2
def baseEnd_7727233 : Nat := 3967784658283870899050609

theorem tailTrace_7727233 : CollatzResearch.WordTrace tailWord_7727233 prefixEnd_7727233 3967784658283870899050609 := by
  unfold tailWord_7727233
  simp only [CollatzResearch.WordTrace]
  refine ⟨281835341214562022174322353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187890227476374681449548235 281835341214562022174322353)
  ·
    refine ⟨211376505910921516630741765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281835341214562022174322353 211376505910921516630741765)
    ·
      refine ⟨39633094858297784368264081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211376505910921516630741765 39633094858297784368264081)
      ·
        refine ⟨29724821143723338276198061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39633094858297784368264081 29724821143723338276198061)
        ·
          refine ⟨11146807928896251853574273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29724821143723338276198061 11146807928896251853574273)
          ·
            refine ⟨8360105946672188890180705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11146807928896251853574273 8360105946672188890180705)
            ·
              refine ⟨6270079460004141667635529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8360105946672188890180705 6270079460004141667635529)
              ·
                refine ⟨4702559595003106250726647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6270079460004141667635529 4702559595003106250726647)
                ·
                  refine ⟨7053839392504659376089971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4702559595003106250726647 7053839392504659376089971)
                  ·
                    refine ⟨10580759088756989064134957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7053839392504659376089971 10580759088756989064134957)
                    ·
                      refine ⟨3967784658283870899050609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10580759088756989064134957 3967784658283870899050609)
                      ·
                        rfl

theorem cell23_7727233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_7727233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727233 prefixEnd_7727233 := by exact prefixLift 7727233
  have htrace : WordTrace (prefixWord ++ tailWord_7727233) baseStart_7727233 baseEnd_7727233 := by
    simpa [prefixWord, tailWord_7727233, baseEnd_7727233] using wordTrace_append hprefix tailTrace_7727233
  have hstable : (prefixWord ++ tailWord_7727233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727233).length < 2 ^ (prefixWord ++ tailWord_7727233).sum := by decide
  have hdescent : baseEnd_7727233 < baseStart_7727233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727288 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 4, 6]
def baseStart_7727288 : Nat := 118140960795 + 7727288 * 2 ^ 59
def prefixEnd_7727288 : Nat := 4983230072969 + 3 ^ 40 * 7727288 * 2
def baseEnd_7727288 : Nat := 1322604299906622727954285

theorem tailTrace_7727288 : CollatzResearch.WordTrace tailWord_7727288 prefixEnd_7727288 1322604299906622727954285 := by
  unfold tailWord_7727288
  simp only [CollatzResearch.WordTrace]
  refine ⟨140918673614681383283787259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187891564819575177711716345 140918673614681383283787259)
  ·
    refine ⟨211378010422022074925680889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140918673614681383283787259 211378010422022074925680889)
    ·
      refine ⟨158533507816516556194260667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211378010422022074925680889 158533507816516556194260667)
      ·
        refine ⟨237800261724774834291391001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158533507816516556194260667 237800261724774834291391001)
        ·
          refine ⟨178350196293581125718543251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237800261724774834291391001 178350196293581125718543251)
          ·
            refine ⟨267525294440371688577814877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178350196293581125718543251 267525294440371688577814877)
            ·
              refine ⟨100321985415139383216680579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267525294440371688577814877 100321985415139383216680579)
              ·
                refine ⟨150482978122709074825020869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100321985415139383216680579 150482978122709074825020869)
                ·
                  refine ⟨28215558398007951529691413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150482978122709074825020869 28215558398007951529691413)
                  ·
                    refine ⟨1322604299906622727954285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28215558398007951529691413 1322604299906622727954285)
                    ·
                      rfl

theorem cell23_7727288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_7727288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727288 prefixEnd_7727288 := by exact prefixLift 7727288
  have htrace : WordTrace (prefixWord ++ tailWord_7727288) baseStart_7727288 baseEnd_7727288 := by
    simpa [prefixWord, tailWord_7727288, baseEnd_7727288] using wordTrace_append hprefix tailTrace_7727288
  have hstable : (prefixWord ++ tailWord_7727288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727288).length < 2 ^ (prefixWord ++ tailWord_7727288).sum := by decide
  have hdescent : baseEnd_7727288 < baseStart_7727288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727345 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 4, 3, 3]
def baseStart_7727345 : Nat := 118140960795 + 7727345 * 2 ^ 59
def prefixEnd_7727345 : Nat := 4983230072969 + 3 ^ 40 * 7727345 * 2
def baseEnd_7727345 : Nat := 3967842168117174460850093

theorem tailTrace_7727345 : CollatzResearch.WordTrace tailWord_7727345 prefixEnd_7727345 3967842168117174460850093 := by
  unfold tailWord_7727345
  simp only [CollatzResearch.WordTrace]
  refine ⟨281839426190156265302399489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187892950793437510201599659 281839426190156265302399489)
  ·
    refine ⟨211379569642617198976799617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281839426190156265302399489 211379569642617198976799617)
    ·
      refine ⟨158534677231962899232599713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211379569642617198976799617 158534677231962899232599713)
      ·
        refine ⟨118901007923972174424449785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158534677231962899232599713 118901007923972174424449785)
        ·
          refine ⟨89175755942979130818337339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118901007923972174424449785 89175755942979130818337339)
          ·
            refine ⟨133763633914468696227506009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89175755942979130818337339 133763633914468696227506009)
            ·
              refine ⟨100322725435851522170629507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133763633914468696227506009 100322725435851522170629507)
              ·
                refine ⟨150484088153777283255944261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100322725435851522170629507 150484088153777283255944261)
                ·
                  refine ⟨28215766528833240610489549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150484088153777283255944261 28215766528833240610489549)
                  ·
                    refine ⟨10580912448312465228933581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28215766528833240610489549 10580912448312465228933581)
                    ·
                      refine ⟨3967842168117174460850093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10580912448312465228933581 3967842168117174460850093)
                      ·
                        rfl

theorem cell23_7727345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_7727345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727345 prefixEnd_7727345 := by exact prefixLift 7727345
  have htrace : WordTrace (prefixWord ++ tailWord_7727345) baseStart_7727345 baseEnd_7727345 := by
    simpa [prefixWord, tailWord_7727345, baseEnd_7727345] using wordTrace_append hprefix tailTrace_7727345
  have hstable : (prefixWord ++ tailWord_7727345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727345).length < 2 ^ (prefixWord ++ tailWord_7727345).sum := by decide
  have hdescent : baseEnd_7727345 < baseStart_7727345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727435 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 3]
def baseStart_7727435 : Nat := 118140960795 + 7727435 * 2 ^ 59
def prefixEnd_7727435 : Nat := 4983230072969 + 3 ^ 40 * 7727435 * 2
def baseEnd_7727435 : Nat := 3967888381376079108724679

theorem tailTrace_7727435 : CollatzResearch.WordTrace tailWord_7727435 prefixEnd_7727435 3967888381376079108724679 := by
  unfold tailWord_7727435
  simp only [CollatzResearch.WordTrace]
  refine ⟨281842708759830210673175759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187895139173220140448783839 281842708759830210673175759)
  ·
    refine ⟨422764063139745316009763639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281842708759830210673175759 422764063139745316009763639)
    ·
      refine ⟨634146094709617974014645459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422764063139745316009763639 634146094709617974014645459)
      ·
        refine ⟨951219142064426961021968189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634146094709617974014645459 951219142064426961021968189)
        ·
          refine ⟨356707178274160110383238071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 951219142064426961021968189 356707178274160110383238071)
          ·
            refine ⟨535060767411240165574857107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356707178274160110383238071 535060767411240165574857107)
            ·
              refine ⟨802591151116860248362285661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535060767411240165574857107 802591151116860248362285661)
              ·
                refine ⟨300971681668822593135857123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 802591151116860248362285661 300971681668822593135857123)
                ·
                  refine ⟨451457522503233889703785685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300971681668822593135857123 451457522503233889703785685)
                  ·
                    refine ⟨10581035683669544289932477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 451457522503233889703785685 10581035683669544289932477)
                    ·
                      refine ⟨3967888381376079108724679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10581035683669544289932477 3967888381376079108724679)
                      ·
                        rfl

theorem cell23_7727435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 3].length) (baseStart_7727435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727435 prefixEnd_7727435 := by exact prefixLift 7727435
  have htrace : WordTrace (prefixWord ++ tailWord_7727435) baseStart_7727435 baseEnd_7727435 := by
    simpa [prefixWord, tailWord_7727435, baseEnd_7727435] using wordTrace_append hprefix tailTrace_7727435
  have hstable : (prefixWord ++ tailWord_7727435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727435).length < 2 ^ (prefixWord ++ tailWord_7727435).sum := by decide
  have hdescent : baseEnd_7727435 < baseStart_7727435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727489 : List Nat := [1, 2, 4, 3, 1, 1, 1, 4, 1, 5]
def baseStart_7727489 : Nat := 118140960795 + 7727489 * 2 ^ 59
def prefixEnd_7727489 : Nat := 4983230072969 + 3 ^ 40 * 7727489 * 2
def baseEnd_7727489 : Nat := 1322638703110473965816477

theorem tailTrace_7727489 : CollatzResearch.WordTrace tailWord_7727489 prefixEnd_7727489 1322638703110473965816477 := by
  unfold tailWord_7727489
  simp only [CollatzResearch.WordTrace]
  refine ⟨281844678301634577895641521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187896452201089718597094347 281844678301634577895641521)
  ·
    refine ⟨211383508726225933421731141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281844678301634577895641521 211383508726225933421731141)
    ·
      refine ⟨39634407886167362516574589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211383508726225933421731141 39634407886167362516574589)
      ·
        refine ⟨14862902957312760943715471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39634407886167362516574589 14862902957312760943715471)
        ·
          refine ⟨22294354435969141415573207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14862902957312760943715471 22294354435969141415573207)
          ·
            refine ⟨33441531653953712123359811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22294354435969141415573207 33441531653953712123359811)
            ·
              refine ⟨50162297480930568185039717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33441531653953712123359811 50162297480930568185039717)
              ·
                refine ⟨9405430777674481534694947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50162297480930568185039717 9405430777674481534694947)
                ·
                  refine ⟨14108146166511722302042421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9405430777674481534694947 14108146166511722302042421)
                  ·
                    refine ⟨1322638703110473965816477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14108146166511722302042421 1322638703110473965816477)
                    ·
                      rfl

theorem cell23_7727489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_7727489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727489 prefixEnd_7727489 := by exact prefixLift 7727489
  have htrace : WordTrace (prefixWord ++ tailWord_7727489) baseStart_7727489 baseEnd_7727489 := by
    simpa [prefixWord, tailWord_7727489, baseEnd_7727489] using wordTrace_append hprefix tailTrace_7727489
  have hstable : (prefixWord ++ tailWord_7727489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727489).length < 2 ^ (prefixWord ++ tailWord_7727489).sum := by decide
  have hdescent : baseEnd_7727489 < baseStart_7727489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727505 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_7727505 : Nat := 118140960795 + 7727505 * 2 ^ 59
def prefixEnd_7727505 : Nat := 4983230072969 + 3 ^ 40 * 7727505 * 2
def baseEnd_7727505 : Nat := 3967924325021893834849357

theorem tailTrace_7727505 : CollatzResearch.WordTrace tailWord_7727505 prefixEnd_7727505 3967924325021893834849357 := by
  unfold tailWord_7727505
  simp only [CollatzResearch.WordTrace]
  refine ⟨281845261869576612628223969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187896841246384408418815979 281845261869576612628223969)
  ·
    refine ⟨211383946402182459471167977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281845261869576612628223969 211383946402182459471167977)
    ·
      refine ⟨158537959801636844603375983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211383946402182459471167977 158537959801636844603375983)
      ·
        refine ⟨237806939702455266905063975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158537959801636844603375983 237806939702455266905063975)
        ·
          refine ⟨356710409553682900357595963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237806939702455266905063975 356710409553682900357595963)
          ·
            refine ⟨535065614330524350536393945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356710409553682900357595963 535065614330524350536393945)
            ·
              refine ⟨401299210747893262902295459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535065614330524350536393945 401299210747893262902295459)
              ·
                refine ⟨601948816121839894353443189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401299210747893262902295459 601948816121839894353443189)
                ·
                  refine ⟨56432701511422490095635299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 601948816121839894353443189 56432701511422490095635299)
                  ·
                    refine ⟨84649052267133735143452949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56432701511422490095635299 84649052267133735143452949)
                    ·
                      refine ⟨3967924325021893834849357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84649052267133735143452949 3967924325021893834849357)
                      ·
                        rfl

theorem cell23_7727505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_7727505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727505 prefixEnd_7727505 := by exact prefixLift 7727505
  have htrace : WordTrace (prefixWord ++ tailWord_7727505) baseStart_7727505 baseEnd_7727505 := by
    simpa [prefixWord, tailWord_7727505, baseEnd_7727505] using wordTrace_append hprefix tailTrace_7727505
  have hstable : (prefixWord ++ tailWord_7727505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727505).length < 2 ^ (prefixWord ++ tailWord_7727505).sum := by decide
  have hdescent : baseEnd_7727505 < baseStart_7727505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727519 : List Nat := [1, 1, 2, 5, 1, 1, 2, 4, 2, 4]
def baseStart_7727519 : Nat := 118140960795 + 7727519 * 2 ^ 59
def prefixEnd_7727519 : Nat := 4983230072969 + 3 ^ 40 * 7727519 * 2
def baseEnd_7727519 : Nat := 1322643837917018926691431

theorem tailTrace_7727519 : CollatzResearch.WordTrace tailWord_7727519 prefixEnd_7727519 1322643837917018926691431 := by
  unfold tailWord_7727519
  simp only [CollatzResearch.WordTrace]
  refine ⟨281845772491525893019233611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187897181661017262012822407 281845772491525893019233611)
  ·
    refine ⟨422768658737288839528850417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281845772491525893019233611 422768658737288839528850417)
    ·
      refine ⟨317076494052966629646637813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422768658737288839528850417 317076494052966629646637813)
      ·
        refine ⟨29725921317465621529372295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317076494052966629646637813 29725921317465621529372295)
        ·
          refine ⟨44588881976198432294058443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29725921317465621529372295 44588881976198432294058443)
          ·
            refine ⟨66883322964297648441087665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44588881976198432294058443 66883322964297648441087665)
            ·
              refine ⟨50162492223223236330815749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66883322964297648441087665 50162492223223236330815749)
              ·
                refine ⟨9405467291854356812027953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50162492223223236330815749 9405467291854356812027953)
                ·
                  refine ⟨7054100468890767609020965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9405467291854356812027953 7054100468890767609020965)
                  ·
                    refine ⟨1322643837917018926691431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7054100468890767609020965 1322643837917018926691431)
                    ·
                      rfl

theorem cell23_7727519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 4].length) (baseStart_7727519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727519 prefixEnd_7727519 := by exact prefixLift 7727519
  have htrace : WordTrace (prefixWord ++ tailWord_7727519) baseStart_7727519 baseEnd_7727519 := by
    simpa [prefixWord, tailWord_7727519, baseEnd_7727519] using wordTrace_append hprefix tailTrace_7727519
  have hstable : (prefixWord ++ tailWord_7727519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727519).length < 2 ^ (prefixWord ++ tailWord_7727519).sum := by decide
  have hdescent : baseEnd_7727519 < baseStart_7727519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727522 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_7727522 : Nat := 118140960795 + 7727522 * 2 ^ 59
def prefixEnd_7727522 : Nat := 4983230072969 + 3 ^ 40 * 7727522 * 2
def baseEnd_7727522 : Nat := 3967933054193020268336779

theorem tailTrace_7727522 : CollatzResearch.WordTrace tailWord_7727522 prefixEnd_7727522 3967933054193020268336779 := by
  unfold tailWord_7727522
  simp only [CollatzResearch.WordTrace]
  refine ⟨70461470477628756132898205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187897254607010016354395213 70461470477628756132898205)
  ·
    refine ⟨26423051429110783549836827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70461470477628756132898205 26423051429110783549836827)
    ·
      refine ⟨39634577143666175324755241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26423051429110783549836827 39634577143666175324755241)
      ·
        refine ⟨29725932857749631493566431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39634577143666175324755241 29725932857749631493566431)
        ·
          refine ⟨44588899286624447240349647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29725932857749631493566431 44588899286624447240349647)
          ·
            refine ⟨66883348929936670860524471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44588899286624447240349647 66883348929936670860524471)
            ·
              refine ⟨100325023394905006290786707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66883348929936670860524471 100325023394905006290786707)
              ·
                refine ⟨150487535092357509436180061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100325023394905006290786707 150487535092357509436180061)
                ·
                  refine ⟨56432825659634066038567523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150487535092357509436180061 56432825659634066038567523)
                  ·
                    refine ⟨84649238489451099057851285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56432825659634066038567523 84649238489451099057851285)
                    ·
                      refine ⟨3967933054193020268336779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84649238489451099057851285 3967933054193020268336779)
                      ·
                        rfl

theorem cell23_7727522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_7727522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727522 prefixEnd_7727522 := by exact prefixLift 7727522
  have htrace : WordTrace (prefixWord ++ tailWord_7727522) baseStart_7727522 baseEnd_7727522 := by
    simpa [prefixWord, tailWord_7727522, baseEnd_7727522] using wordTrace_append hprefix tailTrace_7727522
  have hstable : (prefixWord ++ tailWord_7727522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727522).length < 2 ^ (prefixWord ++ tailWord_7727522).sum := by decide
  have hdescent : baseEnd_7727522 < baseStart_7727522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727540 : List Nat := [2, 5, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_7727540 : Nat := 118140960795 + 7727540 * 2 ^ 59
def prefixEnd_7727540 : Nat := 4983230072969 + 3 ^ 40 * 7727540 * 2
def baseEnd_7727540 : Nat := 1322647432281600399303899

theorem tailTrace_7727540 : CollatzResearch.WordTrace tailWord_7727540 prefixEnd_7727540 1322647432281600399303899 := by
  unfold tailWord_7727540
  simp only [CollatzResearch.WordTrace]
  refine ⟨140923269212224906802874037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187897692282966542403832049 140923269212224906802874037)
  ·
    refine ⟨13211556488646085012769441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140923269212224906802874037 13211556488646085012769441)
    ·
      refine ⟨9908667366484563759577081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13211556488646085012769441 9908667366484563759577081)
      ·
        refine ⟨7431500524863422819682811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9908667366484563759577081 7431500524863422819682811)
        ·
          refine ⟨11147250787295134229524217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7431500524863422819682811 11147250787295134229524217)
          ·
            refine ⟨8360438090471350672143163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11147250787295134229524217 8360438090471350672143163)
            ·
              refine ⟨12540657135707026008214745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8360438090471350672143163 12540657135707026008214745)
              ·
                refine ⟨9405492851780269506161059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12540657135707026008214745 9405492851780269506161059)
                ·
                  refine ⟨14108239277670404259241589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9405492851780269506161059 14108239277670404259241589)
                  ·
                    refine ⟨1322647432281600399303899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14108239277670404259241589 1322647432281600399303899)
                    ·
                      rfl

theorem cell23_7727540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_7727540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727540 prefixEnd_7727540 := by exact prefixLift 7727540
  have htrace : WordTrace (prefixWord ++ tailWord_7727540) baseStart_7727540 baseEnd_7727540 := by
    simpa [prefixWord, tailWord_7727540, baseEnd_7727540] using wordTrace_append hprefix tailTrace_7727540
  have hstable : (prefixWord ++ tailWord_7727540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727540).length < 2 ^ (prefixWord ++ tailWord_7727540).sum := by decide
  have hdescent : baseEnd_7727540 < baseStart_7727540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727553 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7727553 : Nat := 118140960795 + 7727553 * 2 ^ 59
def prefixEnd_7727553 : Nat := 4983230072969 + 3 ^ 40 * 7727553 * 2
def baseEnd_7727553 : Nat := 1322649657364436549016379

theorem tailTrace_7727553 : CollatzResearch.WordTrace tailWord_7727553 prefixEnd_7727553 1322649657364436549016379 := by
  unfold tailWord_7727553
  simp only [CollatzResearch.WordTrace]
  refine ⟨281847012573402716825971313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187898008382268477883980875 281847012573402716825971313)
  ·
    refine ⟨211385259430052037619478485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281847012573402716825971313 211385259430052037619478485)
    ·
      refine ⟨4954342017891844631706527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 211385259430052037619478485 4954342017891844631706527)
      ·
        refine ⟨7431513026837766947559791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4954342017891844631706527 7431513026837766947559791)
        ·
          refine ⟨11147269540256650421339687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7431513026837766947559791 11147269540256650421339687)
          ·
            refine ⟨16720904310384975632009531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11147269540256650421339687 16720904310384975632009531)
            ·
              refine ⟨25081356465577463448014297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16720904310384975632009531 25081356465577463448014297)
              ·
                refine ⟨18811017349183097586010723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25081356465577463448014297 18811017349183097586010723)
                ·
                  refine ⟨28216526023774646379016085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18811017349183097586010723 28216526023774646379016085)
                  ·
                    refine ⟨1322649657364436549016379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28216526023774646379016085 1322649657364436549016379)
                    ·
                      rfl

theorem cell23_7727553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7727553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727553 prefixEnd_7727553 := by exact prefixLift 7727553
  have htrace : WordTrace (prefixWord ++ tailWord_7727553) baseStart_7727553 baseEnd_7727553 := by
    simpa [prefixWord, tailWord_7727553, baseEnd_7727553] using wordTrace_append hprefix tailTrace_7727553
  have hstable : (prefixWord ++ tailWord_7727553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727553).length < 2 ^ (prefixWord ++ tailWord_7727553).sum := by decide
  have hdescent : baseEnd_7727553 < baseStart_7727553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727556 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_7727556 : Nat := 118140960795 + 7727556 * 2 ^ 59
def prefixEnd_7727556 : Nat := 4983230072969 + 3 ^ 40 * 7727556 * 2
def baseEnd_7727556 : Nat := 3967950512535273135311623

theorem tailTrace_7727556 : CollatzResearch.WordTrace tailWord_7727556 prefixEnd_7727556 3967950512535273135311623 := by
  unfold tailWord_7727556
  simp only [CollatzResearch.WordTrace]
  refine ⟨140923560996195924169165261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187898081328261232225553681 140923560996195924169165261)
  ·
    refine ⟨52846335373573471563436973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140923560996195924169165261 52846335373573471563436973)
    ·
      refine ⟨19817375765090051836288865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52846335373573471563436973 19817375765090051836288865)
      ·
        refine ⟨14863031823817538877216649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19817375765090051836288865 14863031823817538877216649)
        ·
          refine ⟨11147273867863154157912487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14863031823817538877216649 11147273867863154157912487)
          ·
            refine ⟨16720910801794731236868731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11147273867863154157912487 16720910801794731236868731)
            ·
              refine ⟨25081366202692096855303097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16720910801794731236868731 25081366202692096855303097)
              ·
                refine ⟨18811024652019072641477323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25081366202692096855303097 18811024652019072641477323)
                ·
                  refine ⟨28216536978028608962215985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18811024652019072641477323 28216536978028608962215985)
                  ·
                    refine ⟨21162402733521456721661989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28216536978028608962215985 21162402733521456721661989)
                    ·
                      refine ⟨3967950512535273135311623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21162402733521456721661989 3967950512535273135311623)
                      ·
                        rfl

theorem cell23_7727556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_7727556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727556 prefixEnd_7727556 := by exact prefixLift 7727556
  have htrace : WordTrace (prefixWord ++ tailWord_7727556) baseStart_7727556 baseEnd_7727556 := by
    simpa [prefixWord, tailWord_7727556, baseEnd_7727556] using wordTrace_append hprefix tailTrace_7727556
  have hstable : (prefixWord ++ tailWord_7727556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727556).length < 2 ^ (prefixWord ++ tailWord_7727556).sum := by decide
  have hdescent : baseEnd_7727556 < baseStart_7727556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727559 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_7727559 : Nat := 118140960795 + 7727559 * 2 ^ 59
def prefixEnd_7727559 : Nat := 4983230072969 + 3 ^ 40 * 7727559 * 2
def baseEnd_7727559 : Nat := 3967952052977236623574109

theorem tailTrace_7727559 : CollatzResearch.WordTrace tailWord_7727559 prefixEnd_7727559 3967952052977236623574109 := by
  unfold tailWord_7727559
  simp only [CollatzResearch.WordTrace]
  refine ⟨281847231411380979850689731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187898154274253986567126487 281847231411380979850689731)
  ·
    refine ⟨422770847117071469776034597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281847231411380979850689731 422770847117071469776034597)
    ·
      refine ⟨79269533834450900583006487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 422770847117071469776034597 79269533834450900583006487)
      ·
        refine ⟨118904300751676350874509731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79269533834450900583006487 118904300751676350874509731)
        ·
          refine ⟨178356451127514526311764597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118904300751676350874509731 178356451127514526311764597)
          ·
            refine ⟨16720917293204486841727931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178356451127514526311764597 16720917293204486841727931)
            ·
              refine ⟨25081375939806730262591897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16720917293204486841727931 25081375939806730262591897)
              ·
                refine ⟨18811031954855047696943923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25081375939806730262591897 18811031954855047696943923)
                ·
                  refine ⟨28216547932282571545415885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18811031954855047696943923 28216547932282571545415885)
                  ·
                    refine ⟨10581205474605964329530957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28216547932282571545415885 10581205474605964329530957)
                    ·
                      refine ⟨3967952052977236623574109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10581205474605964329530957 3967952052977236623574109)
                      ·
                        rfl

theorem cell23_7727559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_7727559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727559 prefixEnd_7727559 := by exact prefixLift 7727559
  have htrace : WordTrace (prefixWord ++ tailWord_7727559) baseStart_7727559 baseEnd_7727559 := by
    simpa [prefixWord, tailWord_7727559, baseEnd_7727559] using wordTrace_append hprefix tailTrace_7727559
  have hstable : (prefixWord ++ tailWord_7727559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727559).length < 2 ^ (prefixWord ++ tailWord_7727559).sum := by decide
  have hdescent : baseEnd_7727559 < baseStart_7727559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727592 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 1, 8]
def baseStart_7727592 : Nat := 118140960795 + 7727592 * 2 ^ 59
def prefixEnd_7727592 : Nat := 4983230072969 + 3 ^ 40 * 7727592 * 2
def baseEnd_7727592 : Nat := 1322656332612944998153819

theorem tailTrace_7727592 : CollatzResearch.WordTrace tailWord_7727592 prefixEnd_7727592 1322656332612944998153819 := by
  unfold tailWord_7727592
  simp only [CollatzResearch.WordTrace]
  refine ⟨140924217510130713243320515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187898956680174284324427353 140924217510130713243320515)
  ·
    refine ⟨211386326265196069864980773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140924217510130713243320515 211386326265196069864980773)
    ·
      refine ⟨39634936174724263099683895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211386326265196069864980773 39634936174724263099683895)
      ·
        refine ⟨59452404262086394649525843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39634936174724263099683895 59452404262086394649525843)
        ·
          refine ⟨89178606393129591974288765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59452404262086394649525843 89178606393129591974288765)
          ·
            refine ⟨33441977397423596990358287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89178606393129591974288765 33441977397423596990358287)
            ·
              refine ⟨50162966096135395485537431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33441977397423596990358287 50162966096135395485537431)
              ·
                refine ⟨75244449144203093228306147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50162966096135395485537431 75244449144203093228306147)
                ·
                  refine ⟨112866673716304639842459221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75244449144203093228306147 112866673716304639842459221)
                  ·
                    refine ⟨1322656332612944998153819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112866673716304639842459221 1322656332612944998153819)
                    ·
                      rfl

theorem cell23_7727592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_7727592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727592 prefixEnd_7727592 := by exact prefixLift 7727592
  have htrace : WordTrace (prefixWord ++ tailWord_7727592) baseStart_7727592 baseEnd_7727592 := by
    simpa [prefixWord, tailWord_7727592, baseEnd_7727592] using wordTrace_append hprefix tailTrace_7727592
  have hstable : (prefixWord ++ tailWord_7727592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727592).length < 2 ^ (prefixWord ++ tailWord_7727592).sum := by decide
  have hdescent : baseEnd_7727592 < baseStart_7727592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727612 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_7727612 : Nat := 118140960795 + 7727612 * 2 ^ 59
def prefixEnd_7727612 : Nat := 4983230072969 + 3 ^ 40 * 7727612 * 2
def baseEnd_7727612 : Nat := 3967979267451924916211365

theorem tailTrace_7727612 : CollatzResearch.WordTrace tailWord_7727612 prefixEnd_7727612 3967979267451924916211365 := by
  unfold tailWord_7727612
  simp only [CollatzResearch.WordTrace]
  refine ⟨140924582240094484951184545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187899442986792646601579393 140924582240094484951184545)
  ·
    refine ⟨105693436680070863713388409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140924582240094484951184545 105693436680070863713388409)
    ·
      refine ⟨79270077510053147785041307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105693436680070863713388409 79270077510053147785041307)
      ·
        refine ⟨118905116265079721677561961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79270077510053147785041307 118905116265079721677561961)
        ·
          refine ⟨89178837198809791258171471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118905116265079721677561961 89178837198809791258171471)
          ·
            refine ⟨133768255798214686887257207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89178837198809791258171471 133768255798214686887257207)
            ·
              refine ⟨200652383697322030330885811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133768255798214686887257207 200652383697322030330885811)
              ·
                refine ⟨300978575545983045496328717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200652383697322030330885811 300978575545983045496328717)
                ·
                  refine ⟨112866965829743642061123269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300978575545983045496328717 112866965829743642061123269)
                  ·
                    refine ⟨21162556093076932886460613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112866965829743642061123269 21162556093076932886460613)
                    ·
                      refine ⟨3967979267451924916211365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21162556093076932886460613 3967979267451924916211365)
                      ·
                        rfl

theorem cell23_7727612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_7727612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727612 prefixEnd_7727612 := by exact prefixLift 7727612
  have htrace : WordTrace (prefixWord ++ tailWord_7727612) baseStart_7727612 baseEnd_7727612 := by
    simpa [prefixWord, tailWord_7727612, baseEnd_7727612] using wordTrace_append hprefix tailTrace_7727612
  have hstable : (prefixWord ++ tailWord_7727612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727612).length < 2 ^ (prefixWord ++ tailWord_7727612).sum := by decide
  have hdescent : baseEnd_7727612 < baseStart_7727612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727620 : List Nat := [2, 3, 2, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_7727620 : Nat := 118140960795 + 7727620 * 2 ^ 59
def prefixEnd_7727620 : Nat := 4983230072969 + 3 ^ 40 * 7727620 * 2
def baseEnd_7727620 : Nat := 3967983375297160884911329

theorem tailTrace_7727620 : CollatzResearch.WordTrace tailWord_7727620 prefixEnd_7727620 3967983375297160884911329 := by
  unfold tailWord_7727620
  simp only [CollatzResearch.WordTrace]
  refine ⟨140924728132079993634330157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187899637509439991512440209 140924728132079993634330157)
  ·
    refine ⟨52846773049529997612873809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140924728132079993634330157 52846773049529997612873809)
    ·
      refine ⟨39635079787147498209655357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52846773049529997612873809 39635079787147498209655357)
      ·
        refine ⟨14863154920180311828620759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39635079787147498209655357 14863154920180311828620759)
        ·
          refine ⟨22294732380270467742931139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14863154920180311828620759 22294732380270467742931139)
          ·
            refine ⟨33442098570405701614396709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22294732380270467742931139 33442098570405701614396709)
            ·
              refine ⟨6270393481951069052699383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33442098570405701614396709 6270393481951069052699383)
              ·
                refine ⟨9405590222926603579049075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6270393481951069052699383 9405590222926603579049075)
                ·
                  refine ⟨14108385334389905368573613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9405590222926603579049075 14108385334389905368573613)
                  ·
                    refine ⟨5290644500396214513215105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14108385334389905368573613 5290644500396214513215105)
                    ·
                      refine ⟨3967983375297160884911329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5290644500396214513215105 3967983375297160884911329)
                      ·
                        rfl

theorem cell23_7727620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_7727620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727620 prefixEnd_7727620 := by exact prefixLift 7727620
  have htrace : WordTrace (prefixWord ++ tailWord_7727620) baseStart_7727620 baseEnd_7727620 := by
    simpa [prefixWord, tailWord_7727620, baseEnd_7727620] using wordTrace_append hprefix tailTrace_7727620
  have hstable : (prefixWord ++ tailWord_7727620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727620).length < 2 ^ (prefixWord ++ tailWord_7727620).sum := by decide
  have hdescent : baseEnd_7727620 < baseStart_7727620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727649 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_7727649 : Nat := 118140960795 + 7727649 * 2 ^ 59
def prefixEnd_7727649 : Nat := 4983230072969 + 3 ^ 40 * 7727649 * 2
def baseEnd_7727649 : Nat := 3967998266236141271448695

theorem tailTrace_7727649 : CollatzResearch.WordTrace tailWord_7727649 prefixEnd_7727649 3967998266236141271448695 := by
  unfold tailWord_7727649
  simp only [CollatzResearch.WordTrace]
  refine ⟨281850513981054925221466001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187900342654036616814310667 281850513981054925221466001)
  ·
    refine ⟨211387885485791193916099501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281850513981054925221466001 211387885485791193916099501)
    ·
      refine ⟨79270457057171697718537313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211387885485791193916099501 79270457057171697718537313)
      ·
        refine ⟨59452842792878773288902985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79270457057171697718537313 59452842792878773288902985)
        ·
          refine ⟨44589632094659079966677239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59452842792878773288902985 44589632094659079966677239)
          ·
            refine ⟨66884448141988619950015859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44589632094659079966677239 66884448141988619950015859)
            ·
              refine ⟨100326672212982929925023789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66884448141988619950015859 100326672212982929925023789)
              ·
                refine ⟨37622502079868598721883921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100326672212982929925023789 37622502079868598721883921)
                ·
                  refine ⟨28216876559901449041412941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37622502079868598721883921 28216876559901449041412941)
                  ·
                    refine ⟨10581328709963043390529853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28216876559901449041412941 10581328709963043390529853)
                    ·
                      refine ⟨3967998266236141271448695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10581328709963043390529853 3967998266236141271448695)
                      ·
                        rfl

theorem cell23_7727649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_7727649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727649 prefixEnd_7727649 := by exact prefixLift 7727649
  have htrace : WordTrace (prefixWord ++ tailWord_7727649) baseStart_7727649 baseEnd_7727649 := by
    simpa [prefixWord, tailWord_7727649, baseEnd_7727649] using wordTrace_append hprefix tailTrace_7727649
  have hstable : (prefixWord ++ tailWord_7727649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727649).length < 2 ^ (prefixWord ++ tailWord_7727649).sum := by decide
  have hdescent : baseEnd_7727649 < baseStart_7727649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727659 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 2, 5, 2]
def baseStart_7727659 : Nat := 118140960795 + 7727659 * 2 ^ 59
def prefixEnd_7727659 : Nat := 4983230072969 + 3 ^ 40 * 7727659 * 2
def baseEnd_7727659 : Nat := 3968003401042686232323649

theorem tailTrace_7727659 : CollatzResearch.WordTrace tailWord_7727659 prefixEnd_7727659 3968003401042686232323649 := by
  unfold tailWord_7727659
  simp only [CollatzResearch.WordTrace]
  refine ⟨281850878711018696929330031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187900585807345797952886687 281850878711018696929330031)
  ·
    refine ⟨422776318066528045393995047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281850878711018696929330031 422776318066528045393995047)
    ·
      refine ⟨634164477099792068090992571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422776318066528045393995047 634164477099792068090992571)
      ·
        refine ⟨951246715649688102136488857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634164477099792068090992571 951246715649688102136488857)
        ·
          refine ⟨713435036737266076602366643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951246715649688102136488857 713435036737266076602366643)
          ·
            refine ⟨1070152555105899114903549965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713435036737266076602366643 1070152555105899114903549965)
            ·
              refine ⟨401307208164712168088831237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1070152555105899114903549965 401307208164712168088831237)
              ·
                refine ⟨75245101530883531516655857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401307208164712168088831237 75245101530883531516655857)
                ·
                  refine ⟨56433826148162648637491893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75245101530883531516655857 56433826148162648637491893)
                  ·
                    refine ⟨5290671201390248309764865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56433826148162648637491893 5290671201390248309764865)
                    ·
                      refine ⟨3968003401042686232323649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5290671201390248309764865 3968003401042686232323649)
                      ·
                        rfl

theorem cell23_7727659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 5, 2].length) (baseStart_7727659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727659 prefixEnd_7727659 := by exact prefixLift 7727659
  have htrace : WordTrace (prefixWord ++ tailWord_7727659) baseStart_7727659 baseEnd_7727659 := by
    simpa [prefixWord, tailWord_7727659, baseEnd_7727659] using wordTrace_append hprefix tailTrace_7727659
  have hstable : (prefixWord ++ tailWord_7727659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727659).length < 2 ^ (prefixWord ++ tailWord_7727659).sum := by decide
  have hdescent : baseEnd_7727659 < baseStart_7727659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727669 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 2, 5]
def baseStart_7727669 : Nat := 118140960795 + 7727669 * 2 ^ 59
def prefixEnd_7727669 : Nat := 4983230072969 + 3 ^ 40 * 7727669 * 2
def baseEnd_7727669 : Nat := 1322669511949743731066201

theorem tailTrace_7727669 : CollatzResearch.WordTrace tailWord_7727669 prefixEnd_7727669 1322669511949743731066201 := by
  unfold tailWord_7727669
  simp only [CollatzResearch.WordTrace]
  refine ⟨281851243440982468637194061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187900828960654979091462707 281851243440982468637194061)
  ·
    refine ⟨105694216290368425738947773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281851243440982468637194061 105694216290368425738947773)
    ·
      refine ⟨39635331108888159652105415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105694216290368425738947773 39635331108888159652105415)
      ·
        refine ⟨59452996663332239478158123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39635331108888159652105415 59452996663332239478158123)
        ·
          refine ⟨89179494994998359217237185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59452996663332239478158123 89179494994998359217237185)
          ·
            refine ⟨66884621246248769412927889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89179494994998359217237185 66884621246248769412927889)
            ·
              refine ⟨50163465934686577059695917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66884621246248769412927889 50163465934686577059695917)
              ·
                refine ⟨18811299725507466397385969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50163465934686577059695917 18811299725507466397385969)
                ·
                  refine ⟨14108474794130599798039477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18811299725507466397385969 14108474794130599798039477)
                  ·
                    refine ⟨1322669511949743731066201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14108474794130599798039477 1322669511949743731066201)
                    ·
                      rfl

theorem cell23_7727669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_7727669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727669 prefixEnd_7727669 := by exact prefixLift 7727669
  have htrace : WordTrace (prefixWord ++ tailWord_7727669) baseStart_7727669 baseEnd_7727669 := by
    simpa [prefixWord, tailWord_7727669, baseEnd_7727669] using wordTrace_append hprefix tailTrace_7727669
  have hstable : (prefixWord ++ tailWord_7727669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727669).length < 2 ^ (prefixWord ++ tailWord_7727669).sum := by decide
  have hdescent : baseEnd_7727669 < baseStart_7727669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727816 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_7727816 : Nat := 118140960795 + 7727816 * 2 ^ 59
def prefixEnd_7727816 : Nat := 4983230072969 + 3 ^ 40 * 7727816 * 2
def baseEnd_7727816 : Nat := 3968084017505442118060427

theorem tailTrace_7727816 : CollatzResearch.WordTrace tailWord_7727816 prefixEnd_7727816 3968084017505442118060427 := by
  unfold tailWord_7727816
  simp only [CollatzResearch.WordTrace]
  refine ⟨140928302485724956371397651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187904403314299941828530201 140928302485724956371397651)
  ·
    refine ⟨211392453728587434557096477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140928302485724956371397651 211392453728587434557096477)
    ·
      refine ⟨79272170148220287958911179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211392453728587434557096477 79272170148220287958911179)
      ·
        refine ⟨118908255222330431938366769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79272170148220287958911179 118908255222330431938366769)
        ·
          refine ⟨89181191416747823953775077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118908255222330431938366769 89181191416747823953775077)
          ·
            refine ⟨16721473390640216991332827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89181191416747823953775077 16721473390640216991332827)
            ·
              refine ⟨25082210085960325486999241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16721473390640216991332827 25082210085960325486999241)
              ·
                refine ⟨18811657564470244115249431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25082210085960325486999241 18811657564470244115249431)
                ·
                  refine ⟨28217486346705366172874147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18811657564470244115249431 28217486346705366172874147)
                  ·
                    refine ⟨42326229520058049259311221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28217486346705366172874147 42326229520058049259311221)
                    ·
                      refine ⟨3968084017505442118060427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42326229520058049259311221 3968084017505442118060427)
                      ·
                        rfl

theorem cell23_7727816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_7727816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727816 prefixEnd_7727816 := by exact prefixLift 7727816
  have htrace : WordTrace (prefixWord ++ tailWord_7727816) baseStart_7727816 baseEnd_7727816 := by
    simpa [prefixWord, tailWord_7727816, baseEnd_7727816] using wordTrace_append hprefix tailTrace_7727816
  have hstable : (prefixWord ++ tailWord_7727816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727816).length < 2 ^ (prefixWord ++ tailWord_7727816).sum := by decide
  have hdescent : baseEnd_7727816 < baseStart_7727816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727833 : List Nat := [1, 2, 1, 2, 3, 2, 4, 2, 1, 2, 3]
def baseStart_7727833 : Nat := 118140960795 + 7727833 * 2 ^ 59
def prefixEnd_7727833 : Nat := 4983230072969 + 3 ^ 40 * 7727833 * 2
def baseEnd_7727833 : Nat := 3968092746676568551547849

theorem tailTrace_7727833 : CollatzResearch.WordTrace tailWord_7727833 prefixEnd_7727833 3968092746676568551547849 := by
  unfold tailWord_7727833
  simp only [CollatzResearch.WordTrace]
  refine ⟨281857225012388324646164153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187904816674925549764109435 281857225012388324646164153)
  ·
    refine ⟨211392918759291243484623115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281857225012388324646164153 211392918759291243484623115)
    ·
      refine ⟨317089378138936865226934673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211392918759291243484623115 317089378138936865226934673)
      ·
        refine ⟨237817033604202648920201005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317089378138936865226934673 237817033604202648920201005)
        ·
          refine ⟨89181387601575993345075377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237817033604202648920201005 89181387601575993345075377)
          ·
            refine ⟨66886040701181995008806533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89181387601575993345075377 66886040701181995008806533)
            ·
              refine ⟨12541132631471624064151225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66886040701181995008806533 12541132631471624064151225)
              ·
                refine ⟨9405849473603718048113419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12541132631471624064151225 9405849473603718048113419)
                ·
                  refine ⟨14108774210405577072170129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9405849473603718048113419 14108774210405577072170129)
                  ·
                    refine ⟨10581580657804182804127597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14108774210405577072170129 10581580657804182804127597)
                    ·
                      refine ⟨3968092746676568551547849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10581580657804182804127597 3968092746676568551547849)
                      ·
                        rfl

theorem cell23_7727833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_7727833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727833 prefixEnd_7727833 := by exact prefixLift 7727833
  have htrace : WordTrace (prefixWord ++ tailWord_7727833) baseStart_7727833 baseEnd_7727833 := by
    simpa [prefixWord, tailWord_7727833, baseEnd_7727833] using wordTrace_append hprefix tailTrace_7727833
  have hstable : (prefixWord ++ tailWord_7727833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727833).length < 2 ^ (prefixWord ++ tailWord_7727833).sum := by decide
  have hdescent : baseEnd_7727833 < baseStart_7727833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727859 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 5]
def baseStart_7727859 : Nat := 118140960795 + 7727859 * 2 ^ 59
def prefixEnd_7727859 : Nat := 4983230072969 + 3 ^ 40 * 7727859 * 2
def baseEnd_7727859 : Nat := 3968106097173585449822729

theorem tailTrace_7727859 : CollatzResearch.WordTrace tailWord_7727859 prefixEnd_7727859 3968106097173585449822729 := by
  unfold tailWord_7727859
  simp only [CollatzResearch.WordTrace]
  refine ⟨281858173310294131086610631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187905448873529420724407087 281858173310294131086610631)
  ·
    refine ⟨422787259965441196629915947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281858173310294131086610631 422787259965441196629915947)
    ·
      refine ⟨634180889948161794944873921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422787259965441196629915947 634180889948161794944873921)
      ·
        refine ⟨475635667461121346208655441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634180889948161794944873921 475635667461121346208655441)
        ·
          refine ⟨356726750595841009656491581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475635667461121346208655441 356726750595841009656491581)
          ·
            refine ⟨133772531473440378621184343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356726750595841009656491581 133772531473440378621184343)
            ·
              refine ⟨200658797210160567931776515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133772531473440378621184343 200658797210160567931776515)
              ·
                refine ⟨300988195815240851897664773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200658797210160567931776515 300988195815240851897664773)
                ·
                  refine ⟨56435286715357659730812145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300988195815240851897664773 56435286715357659730812145)
                  ·
                    refine ⟨42326465036518244798109109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56435286715357659730812145 42326465036518244798109109)
                    ·
                      refine ⟨3968106097173585449822729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42326465036518244798109109 3968106097173585449822729)
                      ·
                        rfl

theorem cell23_7727859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_7727859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727859 prefixEnd_7727859 := by exact prefixLift 7727859
  have htrace : WordTrace (prefixWord ++ tailWord_7727859) baseStart_7727859 baseEnd_7727859 := by
    simpa [prefixWord, tailWord_7727859, baseEnd_7727859] using wordTrace_append hprefix tailTrace_7727859
  have hstable : (prefixWord ++ tailWord_7727859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727859).length < 2 ^ (prefixWord ++ tailWord_7727859).sum := by decide
  have hdescent : baseEnd_7727859 < baseStart_7727859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727863 : List Nat := [1, 1, 3, 1, 1, 1, 3, 6, 2, 1, 3]
def baseStart_7727863 : Nat := 118140960795 + 7727863 * 2 ^ 59
def prefixEnd_7727863 : Nat := 4983230072969 + 3 ^ 40 * 7727863 * 2
def baseEnd_7727863 : Nat := 3968108151096203434172711

theorem tailTrace_7727863 : CollatzResearch.WordTrace tailWord_7727863 prefixEnd_7727863 3968108151096203434172711 := by
  unfold tailWord_7727863
  simp only [CollatzResearch.WordTrace]
  refine ⟨281858319202279639769756243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187905546134853093179837495 281858319202279639769756243)
  ·
    refine ⟨422787478803419459654634365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281858319202279639769756243 422787478803419459654634365)
    ·
      refine ⟨158545304551282297370487887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422787478803419459654634365 158545304551282297370487887)
      ·
        refine ⟨237817956826923446055731831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158545304551282297370487887 237817956826923446055731831)
        ·
          refine ⟨356726935240385169083597747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237817956826923446055731831 356726935240385169083597747)
          ·
            refine ⟨535090402860577753625396621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356726935240385169083597747 535090402860577753625396621)
            ·
              refine ⟨200658901072716657609523733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 535090402860577753625396621 200658901072716657609523733)
              ·
                refine ⟨9405885987783593325446425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 200658901072716657609523733 9405885987783593325446425)
                ·
                  refine ⟨7054414490837694994084819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9405885987783593325446425 7054414490837694994084819)
                  ·
                    refine ⟨10581621736256542491127229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7054414490837694994084819 10581621736256542491127229)
                    ·
                      refine ⟨3968108151096203434172711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10581621736256542491127229 3968108151096203434172711)
                      ·
                        rfl

theorem cell23_7727863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_7727863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727863 prefixEnd_7727863 := by exact prefixLift 7727863
  have htrace : WordTrace (prefixWord ++ tailWord_7727863) baseStart_7727863 baseEnd_7727863 := by
    simpa [prefixWord, tailWord_7727863, baseEnd_7727863] using wordTrace_append hprefix tailTrace_7727863
  have hstable : (prefixWord ++ tailWord_7727863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727863).length < 2 ^ (prefixWord ++ tailWord_7727863).sum := by decide
  have hdescent : baseEnd_7727863 < baseStart_7727863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727873 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_7727873 : Nat := 118140960795 + 7727873 * 2 ^ 59
def prefixEnd_7727873 : Nat := 4983230072969 + 3 ^ 40 * 7727873 * 2
def baseEnd_7727873 : Nat := 3968113285902748395047665

theorem tailTrace_7727873 : CollatzResearch.WordTrace tailWord_7727873 prefixEnd_7727873 3968113285902748395047665 := by
  unfold tailWord_7727873
  simp only [CollatzResearch.WordTrace]
  refine ⟨281858683932243411477620273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187905789288162274318413515 281858683932243411477620273)
  ·
    refine ⟨211394012949182558608215205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281858683932243411477620273 211394012949182558608215205)
    ·
      refine ⟨39636377427971729739040351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211394012949182558608215205 39636377427971729739040351)
      ·
        refine ⟨59454566141957594608560527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39636377427971729739040351 59454566141957594608560527)
        ·
          refine ⟨89181849212936391912840791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59454566141957594608560527 89181849212936391912840791)
          ·
            refine ⟨133772773819404587869261187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89181849212936391912840791 133772773819404587869261187)
            ·
              refine ⟨200659160729106881803891781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133772773819404587869261187 200659160729106881803891781)
              ·
                refine ⟨37623592636707540338229709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200659160729106881803891781 37623592636707540338229709)
                ·
                  refine ⟨14108847238765327626836141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37623592636707540338229709 14108847238765327626836141)
                  ·
                    refine ⟨5290817714536997860063553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14108847238765327626836141 5290817714536997860063553)
                    ·
                      refine ⟨3968113285902748395047665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5290817714536997860063553 3968113285902748395047665)
                      ·
                        rfl

theorem cell23_7727873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_7727873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727873 prefixEnd_7727873 := by exact prefixLift 7727873
  have htrace : WordTrace (prefixWord ++ tailWord_7727873) baseStart_7727873 baseEnd_7727873 := by
    simpa [prefixWord, tailWord_7727873, baseEnd_7727873] using wordTrace_append hprefix tailTrace_7727873
  have hstable : (prefixWord ++ tailWord_7727873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727873).length < 2 ^ (prefixWord ++ tailWord_7727873).sum := by decide
  have hdescent : baseEnd_7727873 < baseStart_7727873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727880 : List Nat := [2, 1, 3, 2, 2, 3, 1, 3, 2, 1, 3]
def baseStart_7727880 : Nat := 118140960795 + 7727880 * 2 ^ 59
def prefixEnd_7727880 : Nat := 4983230072969 + 3 ^ 40 * 7727880 * 2
def baseEnd_7727880 : Nat := 3968116880267329867660133

theorem tailTrace_7727880 : CollatzResearch.WordTrace tailWord_7727880 prefixEnd_7727880 3968116880267329867660133 := by
  unfold tailWord_7727880
  simp only [CollatzResearch.WordTrace]
  refine ⟨140929469621609025836562547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187905959495478701115416729 140929469621609025836562547)
  ·
    refine ⟨211394204432413538754843821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140929469621609025836562547 211394204432413538754843821)
    ·
      refine ⟨79272826662155077033066433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211394204432413538754843821 79272826662155077033066433)
      ·
        refine ⟨59454619996616307774799825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79272826662155077033066433 59454619996616307774799825)
        ·
          refine ⟨44590964997462230831099869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59454619996616307774799825 44590964997462230831099869)
          ·
            refine ⟨16721611874048336561662451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44590964997462230831099869 16721611874048336561662451)
            ·
              refine ⟨25082417811072504842493677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16721611874048336561662451 25082417811072504842493677)
              ·
                refine ⟨9405906679152189315935129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25082417811072504842493677 9405906679152189315935129)
                ·
                  refine ⟨7054430009364141986951347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9405906679152189315935129 7054430009364141986951347)
                  ·
                    refine ⟨10581645014046212980427021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7054430009364141986951347 10581645014046212980427021)
                    ·
                      refine ⟨3968116880267329867660133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10581645014046212980427021 3968116880267329867660133)
                      ·
                        rfl

theorem cell23_7727880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_7727880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727880 prefixEnd_7727880 := by exact prefixLift 7727880
  have htrace : WordTrace (prefixWord ++ tailWord_7727880) baseStart_7727880 baseEnd_7727880 := by
    simpa [prefixWord, tailWord_7727880, baseEnd_7727880] using wordTrace_append hprefix tailTrace_7727880
  have hstable : (prefixWord ++ tailWord_7727880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727880).length < 2 ^ (prefixWord ++ tailWord_7727880).sum := by decide
  have hdescent : baseEnd_7727880 < baseStart_7727880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727903 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 3, 4, 2]
def baseStart_7727903 : Nat := 118140960795 + 7727903 * 2 ^ 59
def prefixEnd_7727903 : Nat := 4983230072969 + 3 ^ 40 * 7727903 * 2
def baseEnd_7727903 : Nat := 3968128690322383277672527

theorem tailTrace_7727903 : CollatzResearch.WordTrace tailWord_7727903 prefixEnd_7727903 3968128690322383277672527 := by
  unfold tailWord_7727903
  simp only [CollatzResearch.WordTrace]
  refine ⟨281859778122134726601212363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187906518748089817734141575 281859778122134726601212363)
  ·
    refine ⟨422789667183202089901818545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281859778122134726601212363 422789667183202089901818545)
    ·
      refine ⟨317092250387401567426363909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422789667183202089901818545 317092250387401567426363909)
      ·
        refine ⟨59454796947637793892443233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317092250387401567426363909 59454796947637793892443233)
        ·
          refine ⟨44591097710728345419332425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59454796947637793892443233 44591097710728345419332425)
          ·
            refine ⟨33443323283046259064499319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44591097710728345419332425 33443323283046259064499319)
            ·
              refine ⟨50164984924569388596748979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33443323283046259064499319 50164984924569388596748979)
              ·
                refine ⟨75247477386854082895123469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50164984924569388596748979 75247477386854082895123469)
                ·
                  refine ⟨28217804020070281085671301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75247477386854082895123469 28217804020070281085671301)
                  ·
                    refine ⟨5290838253763177703563369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28217804020070281085671301 5290838253763177703563369)
                    ·
                      refine ⟨3968128690322383277672527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5290838253763177703563369 3968128690322383277672527)
                      ·
                        rfl

theorem cell23_7727903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_7727903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727903 prefixEnd_7727903 := by exact prefixLift 7727903
  have htrace : WordTrace (prefixWord ++ tailWord_7727903) baseStart_7727903 baseEnd_7727903 := by
    simpa [prefixWord, tailWord_7727903, baseEnd_7727903] using wordTrace_append hprefix tailTrace_7727903
  have hstable : (prefixWord ++ tailWord_7727903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727903).length < 2 ^ (prefixWord ++ tailWord_7727903).sum := by decide
  have hdescent : baseEnd_7727903 < baseStart_7727903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727914 : List Nat := [3, 1, 4, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_7727914 : Nat := 118140960795 + 7727914 * 2 ^ 59
def prefixEnd_7727914 : Nat := 4983230072969 + 3 ^ 40 * 7727914 * 2
def baseEnd_7727914 : Nat := 3968134338609582734634977

theorem tailTrace_7727914 : CollatzResearch.WordTrace tailWord_7727914 prefixEnd_7727914 3968134338609582734634977 := by
  unfold tailWord_7727914
  simp only [CollatzResearch.WordTrace]
  refine ⟨70465044831273718869965699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187906786216729916986575197 70465044831273718869965699)
  ·
    refine ⟨105697567246910578304948549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70465044831273718869965699 105697567246910578304948549)
    ·
      refine ⟨19818293858795733432177853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105697567246910578304948549 19818293858795733432177853)
      ·
        refine ⟨7431860197048400037066695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19818293858795733432177853 7431860197048400037066695)
        ·
          refine ⟨11147790295572600055600043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7431860197048400037066695 11147790295572600055600043)
          ·
            refine ⟨16721685443358900083400065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11147790295572600055600043 16721685443358900083400065)
            ·
              refine ⟨12541264082519175062550049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16721685443358900083400065 12541264082519175062550049)
              ·
                refine ⟨9405948061889381296912537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12541264082519175062550049 9405948061889381296912537)
                ·
                  refine ⟨7054461046417035972684403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9405948061889381296912537 7054461046417035972684403)
                  ·
                    refine ⟨10581691569625553959026605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7054461046417035972684403 10581691569625553959026605)
                    ·
                      refine ⟨3968134338609582734634977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10581691569625553959026605 3968134338609582734634977)
                      ·
                        rfl

theorem cell23_7727914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_7727914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727914 prefixEnd_7727914 := by exact prefixLift 7727914
  have htrace : WordTrace (prefixWord ++ tailWord_7727914) baseStart_7727914 baseEnd_7727914 := by
    simpa [prefixWord, tailWord_7727914, baseEnd_7727914] using wordTrace_append hprefix tailTrace_7727914
  have hstable : (prefixWord ++ tailWord_7727914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727914).length < 2 ^ (prefixWord ++ tailWord_7727914).sum := by decide
  have hdescent : baseEnd_7727914 < baseStart_7727914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7727916 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_7727916 : Nat := 118140960795 + 7727916 * 2 ^ 59
def prefixEnd_7727916 : Nat := 4983230072969 + 3 ^ 40 * 7727916 * 2
def baseEnd_7727916 : Nat := 3968135365570891726809967

theorem tailTrace_7727916 : CollatzResearch.WordTrace tailWord_7727916 prefixEnd_7727916 3968135365570891726809967 := by
  unfold tailWord_7727916
  simp only [CollatzResearch.WordTrace]
  refine ⟨140930126135543814910717801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187906834847391753214290401 140930126135543814910717801)
  ·
    refine ⟨105697594601657861183038351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140930126135543814910717801 105697594601657861183038351)
    ·
      refine ⟨158546391902486791774557527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105697594601657861183038351 158546391902486791774557527)
      ·
        refine ⟨237819587853730187661836291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158546391902486791774557527 237819587853730187661836291)
        ·
          refine ⟨356729381780595281492754437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237819587853730187661836291 356729381780595281492754437)
          ·
            refine ⟨66886759083861615279891457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356729381780595281492754437 66886759083861615279891457)
            ·
              refine ⟨50165069312896211459918593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66886759083861615279891457 50165069312896211459918593)
              ·
                refine ⟨37623801984672158594938945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50165069312896211459918593 37623801984672158594938945)
                ·
                  refine ⟨28217851488504118946204209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37623801984672158594938945 28217851488504118946204209)
                  ·
                    refine ⟨21163388616378089209653157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28217851488504118946204209 21163388616378089209653157)
                    ·
                      refine ⟨3968135365570891726809967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21163388616378089209653157 3968135365570891726809967)
                      ·
                        rfl

theorem cell23_7727916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_7727916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7727916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7727916 prefixEnd_7727916 := by exact prefixLift 7727916
  have htrace : WordTrace (prefixWord ++ tailWord_7727916) baseStart_7727916 baseEnd_7727916 := by
    simpa [prefixWord, tailWord_7727916, baseEnd_7727916] using wordTrace_append hprefix tailTrace_7727916
  have hstable : (prefixWord ++ tailWord_7727916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7727916).length < 2 ^ (prefixWord ++ tailWord_7727916).sum := by decide
  have hdescent : baseEnd_7727916 < baseStart_7727916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7727916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728003 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 3, 4]
def baseStart_7728003 : Nat := 118140960795 + 7728003 * 2 ^ 59
def prefixEnd_7728003 : Nat := 4983230072969 + 3 ^ 40 * 7728003 * 2
def baseEnd_7728003 : Nat := 1322726679462610962140689

theorem tailTrace_7728003 : CollatzResearch.WordTrace tailWord_7728003 prefixEnd_7728003 1322726679462610962140689 := by
  unfold tailWord_7728003
  simp only [CollatzResearch.WordTrace]
  refine ⟨281863425421772443679852663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187908950281181629119901775 281863425421772443679852663)
  ·
    refine ⟨422795138132658665519778995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281863425421772443679852663 422795138132658665519778995)
    ·
      refine ⟨634192707198987998279668493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422795138132658665519778995 634192707198987998279668493)
      ·
        refine ⟨237822265199620499354875685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 634192707198987998279668493 237822265199620499354875685)
        ·
          refine ⟨44591674724928843629039191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237822265199620499354875685 44591674724928843629039191)
          ·
            refine ⟨66887512087393265443558787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44591674724928843629039191 66887512087393265443558787)
            ·
              refine ⟨100331268131089898165338181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66887512087393265443558787 100331268131089898165338181)
              ·
                refine ⟨18812112774579355906000909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100331268131089898165338181 18812112774579355906000909)
                ·
                  refine ⟨7054542290467258464750341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18812112774579355906000909 7054542290467258464750341)
                  ·
                    refine ⟨1322726679462610962140689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7054542290467258464750341 1322726679462610962140689)
                    ·
                      rfl

theorem cell23_7728003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 4].length) (baseStart_7728003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728003 prefixEnd_7728003 := by exact prefixLift 7728003
  have htrace : WordTrace (prefixWord ++ tailWord_7728003) baseStart_7728003 baseEnd_7728003 := by
    simpa [prefixWord, tailWord_7728003, baseEnd_7728003] using wordTrace_append hprefix tailTrace_7728003
  have hstable : (prefixWord ++ tailWord_7728003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728003).length < 2 ^ (prefixWord ++ tailWord_7728003).sum := by decide
  have hdescent : baseEnd_7728003 < baseStart_7728003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728033 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 8]
def baseStart_7728033 : Nat := 118140960795 + 7728033 * 2 ^ 59
def prefixEnd_7728033 : Nat := 4983230072969 + 3 ^ 40 * 7728033 * 2
def baseEnd_7728033 : Nat := 440910604756385307671881

theorem tailTrace_7728033 : CollatzResearch.WordTrace tailWord_7728033 prefixEnd_7728033 440910604756385307671881 := by
  unfold tailWord_7728033
  simp only [CollatzResearch.WordTrace]
  refine ⟨281864519611663758803444753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187909679741109172535629835 281864519611663758803444753)
  ·
    refine ⟨211398389708747819102583565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281864519611663758803444753 211398389708747819102583565)
    ·
      refine ⟨79274396140780432163468837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211398389708747819102583565 79274396140780432163468837)
      ·
        refine ⟨14863949276396331030650407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79274396140780432163468837 14863949276396331030650407)
        ·
          refine ⟨22295923914594496545975611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14863949276396331030650407 22295923914594496545975611)
          ·
            refine ⟨33443885871891744818963417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22295923914594496545975611 33443885871891744818963417)
            ·
              refine ⟨25082914403918808614222563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33443885871891744818963417 25082914403918808614222563)
              ·
                refine ⟨37624371605878212921333845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25082914403918808614222563 37624371605878212921333845)
                ·
                  refine ⟨440910604756385307671881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37624371605878212921333845 440910604756385307671881)
                  ·
                    rfl

theorem cell23_7728033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 8].length) (baseStart_7728033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728033 prefixEnd_7728033 := by exact prefixLift 7728033
  have htrace : WordTrace (prefixWord ++ tailWord_7728033) baseStart_7728033 baseEnd_7728033 := by
    simpa [prefixWord, tailWord_7728033, baseEnd_7728033] using wordTrace_append hprefix tailTrace_7728033
  have hstable : (prefixWord ++ tailWord_7728033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728033).length < 2 ^ (prefixWord ++ tailWord_7728033).sum := by decide
  have hdescent : baseEnd_7728033 < baseStart_7728033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728063 : List Nat := [1, 1, 2, 2, 2, 1, 2, 6, 1, 5]
def baseStart_7728063 : Nat := 118140960795 + 7728063 * 2 ^ 59
def prefixEnd_7728063 : Nat := 4983230072969 + 3 ^ 40 * 7728063 * 2
def baseEnd_7728063 : Nat := 1322736949075700883890597

theorem tailTrace_7728063 : CollatzResearch.WordTrace tailWord_7728063 prefixEnd_7728063 1322736949075700883890597 := by
  unfold tailWord_7728063
  simp only [CollatzResearch.WordTrace]
  refine ⟨281865613801555073927036843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187910409201036715951357895 281865613801555073927036843)
  ·
    refine ⟨422798420702332610890555265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281865613801555073927036843 422798420702332610890555265)
    ·
      refine ⟨317098815526749458167916449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422798420702332610890555265 317098815526749458167916449)
      ·
        refine ⟨237824111645062093625937337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317098815526749458167916449 237824111645062093625937337)
        ·
          refine ⟨178368083733796570219453003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237824111645062093625937337 178368083733796570219453003)
          ·
            refine ⟨267552125600694855329179505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178368083733796570219453003 267552125600694855329179505)
            ·
              refine ⟨200664094200521141496884629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267552125600694855329179505 200664094200521141496884629)
              ·
                refine ⟨9406129415649428507666467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 200664094200521141496884629 9406129415649428507666467)
                ·
                  refine ⟨14109194123474142761499701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9406129415649428507666467 14109194123474142761499701)
                  ·
                    refine ⟨1322736949075700883890597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14109194123474142761499701 1322736949075700883890597)
                    ·
                      rfl

theorem cell23_7728063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 5].length) (baseStart_7728063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728063 prefixEnd_7728063 := by exact prefixLift 7728063
  have htrace : WordTrace (prefixWord ++ tailWord_7728063) baseStart_7728063 baseEnd_7728063 := by
    simpa [prefixWord, tailWord_7728063, baseEnd_7728063] using wordTrace_append hprefix tailTrace_7728063
  have hstable : (prefixWord ++ tailWord_7728063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728063).length < 2 ^ (prefixWord ++ tailWord_7728063).sum := by decide
  have hdescent : baseEnd_7728063 < baseStart_7728063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728120 : List Nat := [2, 1, 2, 1, 1, 3, 1, 6, 1, 2, 3]
def baseStart_7728120 : Nat := 118140960795 + 7728120 * 2 ^ 59
def prefixEnd_7728120 : Nat := 4983230072969 + 3 ^ 40 * 7728120 * 2
def baseEnd_7728120 : Nat := 3968240115624408928659029

theorem tailTrace_7728120 : CollatzResearch.WordTrace tailWord_7728120 prefixEnd_7728120 3968240115624408928659029 := by
  unfold tailWord_7728120
  simp only [CollatzResearch.WordTrace]
  refine ⟨140933846381174286330930907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187911795174899048441241209 140933846381174286330930907)
  ·
    refine ⟨211400769571761429496396361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140933846381174286330930907 211400769571761429496396361)
    ·
      refine ⟨158550577178821072122297271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211400769571761429496396361 158550577178821072122297271)
      ·
        refine ⟨237825865768231608183445907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158550577178821072122297271 237825865768231608183445907)
        ·
          refine ⟨356738798652347412275168861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237825865768231608183445907 356738798652347412275168861)
          ·
            refine ⟨133777049494630279603188323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356738798652347412275168861 133777049494630279603188323)
            ·
              refine ⟨200665574241945419404782485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133777049494630279603188323 200665574241945419404782485)
              ·
                refine ⟨9406198792591191534599179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 200665574241945419404782485 9406198792591191534599179)
                ·
                  refine ⟨14109298188886787301898769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9406198792591191534599179 14109298188886787301898769)
                  ·
                    refine ⟨10581973641665090476424077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14109298188886787301898769 10581973641665090476424077)
                    ·
                      refine ⟨3968240115624408928659029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10581973641665090476424077 3968240115624408928659029)
                      ·
                        rfl

theorem cell23_7728120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_7728120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728120 prefixEnd_7728120 := by exact prefixLift 7728120
  have htrace : WordTrace (prefixWord ++ tailWord_7728120) baseStart_7728120 baseEnd_7728120 := by
    simpa [prefixWord, tailWord_7728120, baseEnd_7728120] using wordTrace_append hprefix tailTrace_7728120
  have hstable : (prefixWord ++ tailWord_7728120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728120).length < 2 ^ (prefixWord ++ tailWord_7728120).sum := by decide
  have hdescent : baseEnd_7728120 < baseStart_7728120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728151 : List Nat := [1, 1, 3, 5, 1, 1, 2, 4, 1, 2, 2]
def baseStart_7728151 : Nat := 118140960795 + 7728151 * 2 ^ 59
def prefixEnd_7728151 : Nat := 4983230072969 + 3 ^ 40 * 7728151 * 2
def baseEnd_7728151 : Nat := 3968256033524698307371387

theorem tailTrace_7728151 : CollatzResearch.WordTrace tailWord_7728151 prefixEnd_7728151 3968256033524698307371387 := by
  unfold tailWord_7728151
  simp only [CollatzResearch.WordTrace]
  refine ⟨281868823425236264956240307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187912548950157509970826871 281868823425236264956240307)
  ·
    refine ⟨422803235137854397434360461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281868823425236264956240307 422803235137854397434360461)
    ·
      refine ⟨158551213176695399037885173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422803235137854397434360461 158551213176695399037885173)
      ·
        refine ⟨14864176235315193659801735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158551213176695399037885173 14864176235315193659801735)
        ·
          refine ⟨22296264352972790489702603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14864176235315193659801735 22296264352972790489702603)
          ·
            refine ⟨33444396529459185734553905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22296264352972790489702603 33444396529459185734553905)
            ·
              refine ⟨25083297397094389300915429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33444396529459185734553905 25083297397094389300915429)
              ·
                refine ⟨4703118261955197993921643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25083297397094389300915429 4703118261955197993921643)
                ·
                  refine ⟨7054677392932796990882465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4703118261955197993921643 7054677392932796990882465)
                  ·
                    refine ⟨5291008044699597743161849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7054677392932796990882465 5291008044699597743161849)
                    ·
                      refine ⟨3968256033524698307371387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5291008044699597743161849 3968256033524698307371387)
                      ·
                        rfl

theorem cell23_7728151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_7728151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728151 prefixEnd_7728151 := by exact prefixLift 7728151
  have htrace : WordTrace (prefixWord ++ tailWord_7728151) baseStart_7728151 baseEnd_7728151 := by
    simpa [prefixWord, tailWord_7728151, baseEnd_7728151] using wordTrace_append hprefix tailTrace_7728151
  have hstable : (prefixWord ++ tailWord_7728151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728151).length < 2 ^ (prefixWord ++ tailWord_7728151).sum := by decide
  have hdescent : baseEnd_7728151 < baseStart_7728151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728220 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_7728220 : Nat := 118140960795 + 7728220 * 2 ^ 59
def prefixEnd_7728220 : Nat := 4983230072969 + 3 ^ 40 * 7728220 * 2
def baseEnd_7728220 : Nat := 3968291463689858537408569

theorem tailTrace_7728220 : CollatzResearch.WordTrace tailWord_7728220 prefixEnd_7728220 3968291463689858537408569 := by
  unfold tailWord_7728220
  simp only [CollatzResearch.WordTrace]
  refine ⟨140935670030993144870251057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187914226707990859827001409 140935670030993144870251057)
  ·
    refine ⟨105701752523244858652688293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140935670030993144870251057 105701752523244858652688293)
    ·
      refine ⟨19819078598108410997379055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105701752523244858652688293 19819078598108410997379055)
      ·
        refine ⟨29728617897162616496068583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19819078598108410997379055 29728617897162616496068583)
        ·
          refine ⟨44592926845743924744102875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29728617897162616496068583 44592926845743924744102875)
          ·
            refine ⟨66889390268615887116154313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44592926845743924744102875 66889390268615887116154313)
            ·
              refine ⟨50167042701461915337115735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66889390268615887116154313 50167042701461915337115735)
              ·
                refine ⟨75250564052192873005673603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50167042701461915337115735 75250564052192873005673603)
                ·
                  refine ⟨112875846078289309508510405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75250564052192873005673603 112875846078289309508510405)
                  ·
                    refine ⟨21164221139679245532845701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112875846078289309508510405 21164221139679245532845701)
                    ·
                      refine ⟨3968291463689858537408569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21164221139679245532845701 3968291463689858537408569)
                      ·
                        rfl

theorem cell23_7728220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_7728220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728220 prefixEnd_7728220 := by exact prefixLift 7728220
  have htrace : WordTrace (prefixWord ++ tailWord_7728220) baseStart_7728220 baseEnd_7728220 := by
    simpa [prefixWord, tailWord_7728220, baseEnd_7728220] using wordTrace_append hprefix tailTrace_7728220
  have hstable : (prefixWord ++ tailWord_7728220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728220).length < 2 ^ (prefixWord ++ tailWord_7728220).sum := by decide
  have hdescent : baseEnd_7728220 < baseStart_7728220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728224 : List Nat := [2, 1, 1, 3, 2, 2, 3, 3, 2, 2, 2]
def baseStart_7728224 : Nat := 118140960795 + 7728224 * 2 ^ 59
def prefixEnd_7728224 : Nat := 4983230072969 + 3 ^ 40 * 7728224 * 2
def baseEnd_7728224 : Nat := 3968293517612476521758551

theorem tailTrace_7728224 : CollatzResearch.WordTrace tailWord_7728224 prefixEnd_7728224 3968293517612476521758551 := by
  unfold tailWord_7728224
  simp only [CollatzResearch.WordTrace]
  refine ⟨140935742976985899211823863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187914323969314532282431817 140935742976985899211823863)
  ·
    refine ⟨211403614465478848817735795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140935742976985899211823863 211403614465478848817735795)
    ·
      refine ⟨317105421698218273226603693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211403614465478848817735795 317105421698218273226603693)
      ·
        refine ⟨118914533136831852459976385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317105421698218273226603693 118914533136831852459976385)
        ·
          refine ⟨89185899852623889344982289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118914533136831852459976385 89185899852623889344982289)
          ·
            refine ⟨66889424889467917008736717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89185899852623889344982289 66889424889467917008736717)
            ·
              refine ⟨25083534333550468878276269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66889424889467917008736717 25083534333550468878276269)
              ·
                refine ⟨9406325375081425829353601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25083534333550468878276269 9406325375081425829353601)
                ·
                  refine ⟨7054744031311069372015201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9406325375081425829353601 7054744031311069372015201)
                  ·
                    refine ⟨5291058023483302029011401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7054744031311069372015201 5291058023483302029011401)
                    ·
                      refine ⟨3968293517612476521758551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5291058023483302029011401 3968293517612476521758551)
                      ·
                        rfl

theorem cell23_7728224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_7728224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728224 prefixEnd_7728224 := by exact prefixLift 7728224
  have htrace : WordTrace (prefixWord ++ tailWord_7728224) baseStart_7728224 baseEnd_7728224 := by
    simpa [prefixWord, tailWord_7728224, baseEnd_7728224] using wordTrace_append hprefix tailTrace_7728224
  have hstable : (prefixWord ++ tailWord_7728224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728224).length < 2 ^ (prefixWord ++ tailWord_7728224).sum := by decide
  have hdescent : baseEnd_7728224 < baseStart_7728224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728264 : List Nat := [2, 1, 3, 4, 2, 1, 1, 4, 5]
def baseStart_7728264 : Nat := 118140960795 + 7728264 * 2 ^ 59
def prefixEnd_7728264 : Nat := 4983230072969 + 3 ^ 40 * 7728264 * 2
def baseEnd_7728264 : Nat := 440923784093184040584263

theorem tailTrace_7728264 : CollatzResearch.WordTrace tailWord_7728264 prefixEnd_7728264 440923784093184040584263 := by
  unfold tailWord_7728264
  simp only [CollatzResearch.WordTrace]
  refine ⟨140936472436913442627551923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187915296582551256836735897 140936472436913442627551923)
  ·
    refine ⟨211404708655370163941327885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140936472436913442627551923 211404708655370163941327885)
    ·
      refine ⟨79276765745763811477997957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211404708655370163941327885 79276765745763811477997957)
      ·
        refine ⟨14864393577330714652124617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79276765745763811477997957 14864393577330714652124617)
        ·
          refine ⟨11148295182998035989093463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14864393577330714652124617 11148295182998035989093463)
          ·
            refine ⟨16722442774497053983640195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11148295182998035989093463 16722442774497053983640195)
            ·
              refine ⟨25083664161745580975460293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16722442774497053983640195 25083664161745580975460293)
              ·
                refine ⟨4703187030327296432898805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25083664161745580975460293 4703187030327296432898805)
                ·
                  refine ⟨440923784093184040584263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4703187030327296432898805 440923784093184040584263)
                  ·
                    rfl

theorem cell23_7728264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 5].length) (baseStart_7728264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728264 prefixEnd_7728264 := by exact prefixLift 7728264
  have htrace : WordTrace (prefixWord ++ tailWord_7728264) baseStart_7728264 baseEnd_7728264 := by
    simpa [prefixWord, tailWord_7728264, baseEnd_7728264] using wordTrace_append hprefix tailTrace_7728264
  have hstable : (prefixWord ++ tailWord_7728264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728264).length < 2 ^ (prefixWord ++ tailWord_7728264).sum := by decide
  have hdescent : baseEnd_7728264 < baseStart_7728264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728317 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_7728317 : Nat := 118140960795 + 7728317 * 2 ^ 59
def prefixEnd_7728317 : Nat := 4983230072969 + 3 ^ 40 * 7728317 * 2
def baseEnd_7728317 : Nat := 3968341271313344657895623

theorem tailTrace_7728317 : CollatzResearch.WordTrace tailWord_7728317 prefixEnd_7728317 3968341271313344657895623 := by
  unfold tailWord_7728317
  simp only [CollatzResearch.WordTrace]
  refine ⟨281874877942634875306783205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187916585295089916871188803 281874877942634875306783205)
  ·
    refine ⟨52851539614244039120021851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281874877942634875306783205 52851539614244039120021851)
    ·
      refine ⟨79277309421366058680032777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52851539614244039120021851 79277309421366058680032777)
      ·
        refine ⟨59457982066024544010024583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79277309421366058680032777 59457982066024544010024583)
        ·
          refine ⟨89186973099036816015036875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59457982066024544010024583 89186973099036816015036875)
          ·
            refine ⟨133780459648555224022555313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89186973099036816015036875 133780459648555224022555313)
            ·
              refine ⟨100335344736416418016916485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133780459648555224022555313 100335344736416418016916485)
              ·
                refine ⟨18812877138078078378171841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100335344736416418016916485 18812877138078078378171841)
                ·
                  refine ⟨14109657853558558783628881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18812877138078078378171841 14109657853558558783628881)
                  ·
                    refine ⟨10582243390168919087721661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14109657853558558783628881 10582243390168919087721661)
                    ·
                      refine ⟨3968341271313344657895623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10582243390168919087721661 3968341271313344657895623)
                      ·
                        rfl

theorem cell23_7728317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_7728317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728317 prefixEnd_7728317 := by exact prefixLift 7728317
  have htrace : WordTrace (prefixWord ++ tailWord_7728317) baseStart_7728317 baseEnd_7728317 := by
    simpa [prefixWord, tailWord_7728317, baseEnd_7728317] using wordTrace_append hprefix tailTrace_7728317
  have hstable : (prefixWord ++ tailWord_7728317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728317).length < 2 ^ (prefixWord ++ tailWord_7728317).sum := by decide
  have hdescent : baseEnd_7728317 < baseStart_7728317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728421 : List Nat := [1, 3, 1, 2, 4, 2, 3, 1, 1, 1, 4]
def baseStart_7728421 : Nat := 118140960795 + 7728421 * 2 ^ 59
def prefixEnd_7728421 : Nat := 4983230072969 + 3 ^ 40 * 7728421 * 2
def baseEnd_7728421 : Nat := 3968394673301412250995145

theorem tailTrace_7728421 : CollatzResearch.WordTrace tailWord_7728421 prefixEnd_7728421 3968394673301412250995145 := by
  unfold tailWord_7728421
  simp only [CollatzResearch.WordTrace]
  refine ⟨281878671134258101068569117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187919114089505400712379411 281878671134258101068569117)
  ·
    refine ⟨105704501675346787900713419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281878671134258101068569117 105704501675346787900713419)
    ·
      refine ⟨158556752513020181851070129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105704501675346787900713419 158556752513020181851070129)
      ·
        refine ⟨118917564384765136388302597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158556752513020181851070129 118917564384765136388302597)
        ·
          refine ⟨22297043322143463072806737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118917564384765136388302597 22297043322143463072806737)
          ·
            refine ⟨16722782491607597304605053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22297043322143463072806737 16722782491607597304605053)
            ·
              refine ⟨6271043434352848989226895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16722782491607597304605053 6271043434352848989226895)
              ·
                refine ⟨9406565151529273483840343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6271043434352848989226895 9406565151529273483840343)
                ·
                  refine ⟨14109847727293910225760515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9406565151529273483840343 14109847727293910225760515)
                  ·
                    refine ⟨21164771590940865338640773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14109847727293910225760515 21164771590940865338640773)
                    ·
                      refine ⟨3968394673301412250995145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21164771590940865338640773 3968394673301412250995145)
                      ·
                        rfl

theorem cell23_7728421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_7728421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728421 prefixEnd_7728421 := by exact prefixLift 7728421
  have htrace : WordTrace (prefixWord ++ tailWord_7728421) baseStart_7728421 baseEnd_7728421 := by
    simpa [prefixWord, tailWord_7728421, baseEnd_7728421] using wordTrace_append hprefix tailTrace_7728421
  have hstable : (prefixWord ++ tailWord_7728421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728421).length < 2 ^ (prefixWord ++ tailWord_7728421).sum := by decide
  have hdescent : baseEnd_7728421 < baseStart_7728421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728424 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_7728424 : Nat := 118140960795 + 7728424 * 2 ^ 59
def prefixEnd_7728424 : Nat := 4983230072969 + 3 ^ 40 * 7728424 * 2
def baseEnd_7728424 : Nat := 3968396213743375739257631

theorem tailTrace_7728424 : CollatzResearch.WordTrace tailWord_7728424 prefixEnd_7728424 3968396213743375739257631 := by
  unfold tailWord_7728424
  simp only [CollatzResearch.WordTrace]
  refine ⟨140939390276623616290464163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187919187035498155053952217 140939390276623616290464163)
  ·
    refine ⟨211409085414935424435696245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140939390276623616290464163 211409085414935424435696245)
    ·
      refine ⟨19819601757650196040846523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211409085414935424435696245 19819601757650196040846523)
      ·
        refine ⟨29729402636475294061269785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19819601757650196040846523 29729402636475294061269785)
        ·
          refine ⟨22297051977356470545952339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29729402636475294061269785 22297051977356470545952339)
          ·
            refine ⟨33445577966034705818928509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22297051977356470545952339 33445577966034705818928509)
            ·
              refine ⟨12542091737263014682098191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33445577966034705818928509 12542091737263014682098191)
              ·
                refine ⟨18813137605894522023147287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12542091737263014682098191 18813137605894522023147287)
                ·
                  refine ⟨28219706408841783034720931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18813137605894522023147287 28219706408841783034720931)
                  ·
                    refine ⟨42329559613262674552081397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28219706408841783034720931 42329559613262674552081397)
                    ·
                      refine ⟨3968396213743375739257631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42329559613262674552081397 3968396213743375739257631)
                      ·
                        rfl

theorem cell23_7728424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_7728424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728424 prefixEnd_7728424 := by exact prefixLift 7728424
  have htrace : WordTrace (prefixWord ++ tailWord_7728424) baseStart_7728424 baseEnd_7728424 := by
    simpa [prefixWord, tailWord_7728424, baseEnd_7728424] using wordTrace_append hprefix tailTrace_7728424
  have hstable : (prefixWord ++ tailWord_7728424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728424).length < 2 ^ (prefixWord ++ tailWord_7728424).sum := by decide
  have hdescent : baseEnd_7728424 < baseStart_7728424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728464 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 3, 3, 2]
def baseStart_7728464 : Nat := 118140960795 + 7728464 * 2 ^ 59
def prefixEnd_7728464 : Nat := 4983230072969 + 3 ^ 40 * 7728464 * 2
def baseEnd_7728464 : Nat := 3968416752969555582757447

theorem tailTrace_7728464 : CollatzResearch.WordTrace tailWord_7728464 prefixEnd_7728464 3968416752969555582757447 := by
  unfold tailWord_7728464
  simp only [CollatzResearch.WordTrace]
  refine ⟨140940119736551159706192223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187920159648734879608256297 140940119736551159706192223)
  ·
    refine ⟨211410179604826739559288335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140940119736551159706192223 211410179604826739559288335)
    ·
      refine ⟨317115269407240109338932503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211410179604826739559288335 317115269407240109338932503)
      ·
        refine ⟨475672904110860164008398755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317115269407240109338932503 475672904110860164008398755)
        ·
          refine ⟨713509356166290246012598133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475672904110860164008398755 713509356166290246012598133)
          ·
            refine ⟨66891502140589710563681075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 713509356166290246012598133 66891502140589710563681075)
            ·
              refine ⟨100337253210884565845521613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66891502140589710563681075 100337253210884565845521613)
              ·
                refine ⟨37626469954081712192070605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100337253210884565845521613 37626469954081712192070605)
                ·
                  refine ⟨14109926232780642072026477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37626469954081712192070605 14109926232780642072026477)
                  ·
                    refine ⟨5291222337292740777009929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14109926232780642072026477 5291222337292740777009929)
                    ·
                      refine ⟨3968416752969555582757447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5291222337292740777009929 3968416752969555582757447)
                      ·
                        rfl

theorem cell23_7728464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 3, 3, 2].length) (baseStart_7728464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728464 prefixEnd_7728464 := by exact prefixLift 7728464
  have htrace : WordTrace (prefixWord ++ tailWord_7728464) baseStart_7728464 baseEnd_7728464 := by
    simpa [prefixWord, tailWord_7728464, baseEnd_7728464] using wordTrace_append hprefix tailTrace_7728464
  have hstable : (prefixWord ++ tailWord_7728464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728464).length < 2 ^ (prefixWord ++ tailWord_7728464).sum := by decide
  have hdescent : baseEnd_7728464 < baseStart_7728464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728497 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 1, 6, 3]
def baseStart_7728497 : Nat := 118140960795 + 7728497 * 2 ^ 59
def prefixEnd_7728497 : Nat := 4983230072969 + 3 ^ 40 * 7728497 * 2
def baseEnd_7728497 : Nat := 3968433697831153953644795

theorem tailTrace_7728497 : CollatzResearch.WordTrace tailWord_7728497 prefixEnd_7728497 3968433697831153953644795 := by
  unfold tailWord_7728497
  simp only [CollatzResearch.WordTrace]
  refine ⟨281881443081982766048335745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187920962054655177365557163 281881443081982766048335745)
  ·
    refine ⟨211411082311487074536251809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281881443081982766048335745 211411082311487074536251809)
    ·
      refine ⟨158558311733615305902188857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211411082311487074536251809 158558311733615305902188857)
      ·
        refine ⟨118918733800211479426641643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158558311733615305902188857 118918733800211479426641643)
        ·
          refine ⟨178378100700317219139962465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118918733800211479426641643 178378100700317219139962465)
          ·
            refine ⟨133783575525237914354971849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178378100700317219139962465 133783575525237914354971849)
            ·
              refine ⟨100337681643928435766228887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133783575525237914354971849 100337681643928435766228887)
              ·
                refine ⟨150506522465892653649343331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100337681643928435766228887 150506522465892653649343331)
                ·
                  refine ⟨225759783698838980474014997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150506522465892653649343331 225759783698838980474014997)
                  ·
                    refine ⟨10582489860883077209719453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 225759783698838980474014997 10582489860883077209719453)
                    ·
                      refine ⟨3968433697831153953644795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10582489860883077209719453 3968433697831153953644795)
                      ·
                        rfl

theorem cell23_7728497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_7728497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728497 prefixEnd_7728497 := by exact prefixLift 7728497
  have htrace : WordTrace (prefixWord ++ tailWord_7728497) baseStart_7728497 baseEnd_7728497 := by
    simpa [prefixWord, tailWord_7728497, baseEnd_7728497] using wordTrace_append hprefix tailTrace_7728497
  have hstable : (prefixWord ++ tailWord_7728497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728497).length < 2 ^ (prefixWord ++ tailWord_7728497).sum := by decide
  have hdescent : baseEnd_7728497 < baseStart_7728497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728507 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 4]
def baseStart_7728507 : Nat := 118140960795 + 7728507 * 2 ^ 59
def prefixEnd_7728507 : Nat := 4983230072969 + 3 ^ 40 * 7728507 * 2
def baseEnd_7728507 : Nat := 3968438832637698914519749

theorem tailTrace_7728507 : CollatzResearch.WordTrace tailWord_7728507 prefixEnd_7728507 3968438832637698914519749 := by
  unfold tailWord_7728507
  simp only [CollatzResearch.WordTrace]
  refine ⟨281881807811946537756199775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187921205207964358504133183 281881807811946537756199775)
  ·
    refine ⟨422822711717919806634299663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281881807811946537756199775 422822711717919806634299663)
    ·
      refine ⟨634234067576879709951449495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422822711717919806634299663 634234067576879709951449495)
      ·
        refine ⟨951351101365319564927174243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634234067576879709951449495 951351101365319564927174243)
        ·
          refine ⟨1427026652047979347390761365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951351101365319564927174243 1427026652047979347390761365)
          ·
            refine ⟨66891874314749031908941939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1427026652047979347390761365 66891874314749031908941939)
            ·
              refine ⟨100337811472123547863412909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66891874314749031908941939 100337811472123547863412909)
              ·
                refine ⟨37626679302046330448779841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100337811472123547863412909 37626679302046330448779841)
                ·
                  refine ⟨28220009476534747836584881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37626679302046330448779841 28220009476534747836584881)
                  ·
                    refine ⟨21165007107401060877438661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28220009476534747836584881 21165007107401060877438661)
                    ·
                      refine ⟨3968438832637698914519749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21165007107401060877438661 3968438832637698914519749)
                      ·
                        rfl

theorem cell23_7728507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 4].length) (baseStart_7728507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728507 prefixEnd_7728507 := by exact prefixLift 7728507
  have htrace : WordTrace (prefixWord ++ tailWord_7728507) baseStart_7728507 baseEnd_7728507 := by
    simpa [prefixWord, tailWord_7728507, baseEnd_7728507] using wordTrace_append hprefix tailTrace_7728507
  have hstable : (prefixWord ++ tailWord_7728507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728507).length < 2 ^ (prefixWord ++ tailWord_7728507).sum := by decide
  have hdescent : baseEnd_7728507 < baseStart_7728507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728517 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 7]
def baseStart_7728517 : Nat := 118140960795 + 7728517 * 2 ^ 59
def prefixEnd_7728517 : Nat := 4983230072969 + 3 ^ 40 * 7728517 * 2
def baseEnd_7728517 : Nat := 440938218604915986154967

theorem tailTrace_7728517 : CollatzResearch.WordTrace tailWord_7728517 prefixEnd_7728517 440938218604915986154967 := by
  unfold tailWord_7728517
  simp only [CollatzResearch.WordTrace]
  refine ⟨281882172541910309464063805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187921448361273539642709203 281882172541910309464063805)
  ·
    refine ⟨105705814703216366049023927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281882172541910309464063805 105705814703216366049023927)
    ·
      refine ⟨158558722054824549073535891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105705814703216366049023927 158558722054824549073535891)
      ·
        refine ⟨237838083082236823610303837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158558722054824549073535891 237838083082236823610303837)
        ·
          refine ⟨89189281155838808853863939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237838083082236823610303837 89189281155838808853863939)
          ·
            refine ⟨133783921733758213280795909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89189281155838808853863939 133783921733758213280795909)
            ·
              refine ⟨25084485325079664990149233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133783921733758213280795909 25084485325079664990149233)
              ·
                refine ⟨18813363993809748742611925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25084485325079664990149233 18813363993809748742611925)
                ·
                  refine ⟨440938218604915986154967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18813363993809748742611925 440938218604915986154967)
                  ·
                    rfl

theorem cell23_7728517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_7728517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728517 prefixEnd_7728517 := by exact prefixLift 7728517
  have htrace : WordTrace (prefixWord ++ tailWord_7728517) baseStart_7728517 baseEnd_7728517 := by
    simpa [prefixWord, tailWord_7728517, baseEnd_7728517] using wordTrace_append hprefix tailTrace_7728517
  have hstable : (prefixWord ++ tailWord_7728517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728517).length < 2 ^ (prefixWord ++ tailWord_7728517).sum := by decide
  have hdescent : baseEnd_7728517 < baseStart_7728517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728618 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_7728618 : Nat := 118140960795 + 7728618 * 2 ^ 59
def prefixEnd_7728618 : Nat := 4983230072969 + 3 ^ 40 * 7728618 * 2
def baseEnd_7728618 : Nat := 3968495828990347980231739

theorem tailTrace_7728618 : CollatzResearch.WordTrace tailWord_7728618 prefixEnd_7728618 3968495828990347980231739 := by
  unfold tailWord_7728618
  simp only [CollatzResearch.WordTrace]
  refine ⟨70471464078636100928372627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187923904209696269142327005 70471464078636100928372627)
  ·
    refine ⟨105707196117954151392558941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70471464078636100928372627 105707196117954151392558941)
    ·
      refine ⟨39640198544232806772209603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105707196117954151392558941 39640198544232806772209603)
      ·
        refine ⟨59460297816349210158314405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39640198544232806772209603 59460297816349210158314405)
        ·
          refine ⟨11148805840565476904683951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59460297816349210158314405 11148805840565476904683951)
          ·
            refine ⟨16723208760848215357025927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11148805840565476904683951 16723208760848215357025927)
            ·
              refine ⟨25084813141272323035538891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16723208760848215357025927 25084813141272323035538891)
              ·
                refine ⟨37627219711908484553308337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25084813141272323035538891 37627219711908484553308337)
                ·
                  refine ⟨28220414783931363414981253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37627219711908484553308337 28220414783931363414981253)
                  ·
                    refine ⟨5291327771987130640308985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28220414783931363414981253 5291327771987130640308985)
                    ·
                      refine ⟨3968495828990347980231739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5291327771987130640308985 3968495828990347980231739)
                      ·
                        rfl

theorem cell23_7728618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_7728618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728618 prefixEnd_7728618 := by exact prefixLift 7728618
  have htrace : WordTrace (prefixWord ++ tailWord_7728618) baseStart_7728618 baseEnd_7728618 := by
    simpa [prefixWord, tailWord_7728618, baseEnd_7728618] using wordTrace_append hprefix tailTrace_7728618
  have hstable : (prefixWord ++ tailWord_7728618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728618).length < 2 ^ (prefixWord ++ tailWord_7728618).sum := by decide
  have hdescent : baseEnd_7728618 < baseStart_7728618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728624 : List Nat := [2, 1, 1, 1, 3, 4, 2, 3, 6]
def baseStart_7728624 : Nat := 118140960795 + 7728624 * 2 ^ 59
def prefixEnd_7728624 : Nat := 4983230072969 + 3 ^ 40 * 7728624 * 2
def baseEnd_7728624 : Nat := 440944323319363884084079

theorem tailTrace_7728624 : CollatzResearch.WordTrace tailWord_7728624 prefixEnd_7728624 440944323319363884084079 := by
  unfold tailWord_7728624
  simp only [CollatzResearch.WordTrace]
  refine ⟨140943037576261333369104463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187924050101681777825472617 140943037576261333369104463)
  ·
    refine ⟨211414556364392000053656695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140943037576261333369104463 211414556364392000053656695)
    ·
      refine ⟨317121834546588000080485043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211414556364392000053656695 317121834546588000080485043)
      ·
        refine ⟨475682751819882000120727565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317121834546588000080485043 475682751819882000120727565)
        ·
          refine ⟨178381031932455750045272837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475682751819882000120727565 178381031932455750045272837)
          ·
            refine ⟨33446443487335453133488657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178381031932455750045272837 33446443487335453133488657)
            ·
              refine ⟨25084832615501589850116493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33446443487335453133488657 25084832615501589850116493)
              ·
                refine ⟨9406812230813096193793685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25084832615501589850116493 9406812230813096193793685)
                ·
                  refine ⟨440944323319363884084079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9406812230813096193793685 440944323319363884084079)
                  ·
                    rfl

theorem cell23_7728624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 6].length) (baseStart_7728624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728624 prefixEnd_7728624 := by exact prefixLift 7728624
  have htrace : WordTrace (prefixWord ++ tailWord_7728624) baseStart_7728624 baseEnd_7728624 := by
    simpa [prefixWord, tailWord_7728624, baseEnd_7728624] using wordTrace_append hprefix tailTrace_7728624
  have hstable : (prefixWord ++ tailWord_7728624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728624).length < 2 ^ (prefixWord ++ tailWord_7728624).sum := by decide
  have hdescent : baseEnd_7728624 < baseStart_7728624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728627 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 6]
def baseStart_7728627 : Nat := 118140960795 + 7728627 * 2 ^ 59
def prefixEnd_7728627 : Nat := 4983230072969 + 3 ^ 40 * 7728627 * 2
def baseEnd_7728627 : Nat := 3968500450316238445019197

theorem tailTrace_7728627 : CollatzResearch.WordTrace tailWord_7728627 prefixEnd_7728627 3968500450316238445019197 := by
  unfold tailWord_7728627
  simp only [CollatzResearch.WordTrace]
  refine ⟨281886184571511798250568135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187924123047674532167045423 281886184571511798250568135)
  ·
    refine ⟨422829276857267697375852203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281886184571511798250568135 422829276857267697375852203)
    ·
      refine ⟨634243915285901546063778305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422829276857267697375852203 634243915285901546063778305)
      ·
        refine ⟨475682936464426159547833729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634243915285901546063778305 475682936464426159547833729)
        ·
          refine ⟨356762202348319619660875297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475682936464426159547833729 356762202348319619660875297)
          ·
            refine ⟨267571651761239714745656473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356762202348319619660875297 267571651761239714745656473)
            ·
              refine ⟨200678738820929786059242355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267571651761239714745656473 200678738820929786059242355)
              ·
                refine ⟨301018108231394679088863533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200678738820929786059242355 301018108231394679088863533)
                ·
                  refine ⟨112881790586773004658323825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301018108231394679088863533 112881790586773004658323825)
                  ·
                    refine ⟨84661342940079753493742869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112881790586773004658323825 84661342940079753493742869)
                    ·
                      refine ⟨3968500450316238445019197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84661342940079753493742869 3968500450316238445019197)
                      ·
                        rfl

theorem cell23_7728627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_7728627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728627 prefixEnd_7728627 := by exact prefixLift 7728627
  have htrace : WordTrace (prefixWord ++ tailWord_7728627) baseStart_7728627 baseEnd_7728627 := by
    simpa [prefixWord, tailWord_7728627, baseEnd_7728627] using wordTrace_append hprefix tailTrace_7728627
  have hstable : (prefixWord ++ tailWord_7728627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728627).length < 2 ^ (prefixWord ++ tailWord_7728627).sum := by decide
  have hdescent : baseEnd_7728627 < baseStart_7728627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728667 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 1, 12]
def baseStart_7728667 : Nat := 118140960795 + 7728667 * 2 ^ 59
def prefixEnd_7728667 : Nat := 4983230072969 + 3 ^ 40 * 7728667 * 2
def baseEnd_7728667 : Nat := 1322840329847472762839671

theorem tailTrace_7728667 : CollatzResearch.WordTrace tailWord_7728667 prefixEnd_7728667 1322840329847472762839671 := by
  unfold tailWord_7728667
  simp only [CollatzResearch.WordTrace]
  refine ⟨281887643491366885082024255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187925095660911256721349503 281887643491366885082024255)
  ·
    refine ⟨422831465237050327623036383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281887643491366885082024255 422831465237050327623036383)
    ·
      refine ⟨634247197855575491434554575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422831465237050327623036383 634247197855575491434554575)
      ·
        refine ⟨951370796783363237151831863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634247197855575491434554575 951370796783363237151831863)
        ·
          refine ⟨1427056195175044855727747795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951370796783363237151831863 1427056195175044855727747795)
          ·
            refine ⟨2140584292762567283591621693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427056195175044855727747795 2140584292762567283591621693)
            ·
              refine ⟨802719109785962731346858135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2140584292762567283591621693 802719109785962731346858135)
              ·
                refine ⟨1204078664678944097020287203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802719109785962731346858135 1204078664678944097020287203)
                ·
                  refine ⟨1806117997018416145530430805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204078664678944097020287203 1806117997018416145530430805)
                  ·
                    refine ⟨1322840329847472762839671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1806117997018416145530430805 1322840329847472762839671)
                    ·
                      rfl

theorem cell23_7728667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 12].length) (baseStart_7728667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728667 prefixEnd_7728667 := by exact prefixLift 7728667
  have htrace : WordTrace (prefixWord ++ tailWord_7728667) baseStart_7728667 baseEnd_7728667 := by
    simpa [prefixWord, tailWord_7728667, baseEnd_7728667] using wordTrace_append hprefix tailTrace_7728667
  have hstable : (prefixWord ++ tailWord_7728667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728667).length < 2 ^ (prefixWord ++ tailWord_7728667).sum := by decide
  have hdescent : baseEnd_7728667 < baseStart_7728667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728668 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_7728668 : Nat := 118140960795 + 7728668 * 2 ^ 59
def prefixEnd_7728668 : Nat := 4983230072969 + 3 ^ 40 * 7728668 * 2
def baseEnd_7728668 : Nat := 3968521503023072784606509

theorem tailTrace_7728668 : CollatzResearch.WordTrace tailWord_7728668 prefixEnd_7728668 3968521503023072784606509 := by
  unfold tailWord_7728668
  simp only [CollatzResearch.WordTrace]
  refine ⟨140943839982181631126405329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187925119976242174835207105 140943839982181631126405329)
  ·
    refine ⟨105707879986636223344803997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140943839982181631126405329 105707879986636223344803997)
    ·
      refine ⟨39640454994988583754301499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105707879986636223344803997 39640454994988583754301499)
      ·
        refine ⟨59460682492482875631452249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39640454994988583754301499 59460682492482875631452249)
        ·
          refine ⟨44595511869362156723589187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59460682492482875631452249 44595511869362156723589187)
          ·
            refine ⟨66893267804043235085383781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44595511869362156723589187 66893267804043235085383781)
            ·
              refine ⟨12542487713258106578509459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66893267804043235085383781 12542487713258106578509459)
              ·
                refine ⟨18813731569887159867764189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12542487713258106578509459 18813731569887159867764189)
                ·
                  refine ⟨7055149338707684950411571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18813731569887159867764189 7055149338707684950411571)
                  ·
                    refine ⟨10582724008061527425617357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7055149338707684950411571 10582724008061527425617357)
                    ·
                      refine ⟨3968521503023072784606509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10582724008061527425617357 3968521503023072784606509)
                      ·
                        rfl

theorem cell23_7728668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_7728668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728668 prefixEnd_7728668 := by exact prefixLift 7728668
  have htrace : WordTrace (prefixWord ++ tailWord_7728668) baseStart_7728668 baseEnd_7728668 := by
    simpa [prefixWord, tailWord_7728668, baseEnd_7728668] using wordTrace_append hprefix tailTrace_7728668
  have hstable : (prefixWord ++ tailWord_7728668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728668).length < 2 ^ (prefixWord ++ tailWord_7728668).sum := by decide
  have hdescent : baseEnd_7728668 < baseStart_7728668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728691 : List Nat := [1, 1, 1, 2, 4, 3, 1, 4, 1, 1, 4]
def baseStart_7728691 : Nat := 118140960795 + 7728691 * 2 ^ 59
def prefixEnd_7728691 : Nat := 4983230072969 + 3 ^ 40 * 7728691 * 2
def baseEnd_7728691 : Nat := 3968533313078126194618903

theorem tailTrace_7728691 : CollatzResearch.WordTrace tailWord_7728691 prefixEnd_7728691 3968533313078126194618903 := by
  unfold tailWord_7728691
  simp only [CollatzResearch.WordTrace]
  refine ⟨281888518843279937180897927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187925679228853291453931951 281888518843279937180897927)
  ·
    refine ⟨422832778264919905771346891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281888518843279937180897927 422832778264919905771346891)
    ·
      refine ⟨634249167397379858657020337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422832778264919905771346891 634249167397379858657020337)
      ·
        refine ⟨475686875548034893992765253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634249167397379858657020337 475686875548034893992765253)
        ·
          refine ⟨89191289165256542623643485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 475686875548034893992765253 89191289165256542623643485)
          ·
            refine ⟨33446733436971203483866307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89191289165256542623643485 33446733436971203483866307)
            ·
              refine ⟨50170100155456805225799461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33446733436971203483866307 50170100155456805225799461)
              ·
                refine ⟨9406893779148150979837399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50170100155456805225799461 9406893779148150979837399)
                ·
                  refine ⟨14110340668722226469756099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9406893779148150979837399 14110340668722226469756099)
                  ·
                    refine ⟨21165511003083339704634149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14110340668722226469756099 21165511003083339704634149)
                    ·
                      refine ⟨3968533313078126194618903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21165511003083339704634149 3968533313078126194618903)
                      ·
                        rfl

theorem cell23_7728691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 1, 4].length) (baseStart_7728691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728691 prefixEnd_7728691 := by exact prefixLift 7728691
  have htrace : WordTrace (prefixWord ++ tailWord_7728691) baseStart_7728691 baseEnd_7728691 := by
    simpa [prefixWord, tailWord_7728691, baseEnd_7728691] using wordTrace_append hprefix tailTrace_7728691
  have hstable : (prefixWord ++ tailWord_7728691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728691).length < 2 ^ (prefixWord ++ tailWord_7728691).sum := by decide
  have hdescent : baseEnd_7728691 < baseStart_7728691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728704 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 4]
def baseStart_7728704 : Nat := 118140960795 + 7728704 * 2 ^ 59
def prefixEnd_7728704 : Nat := 4983230072969 + 3 ^ 40 * 7728704 * 2
def baseEnd_7728704 : Nat := 3968539988326634643756343

theorem tailTrace_7728704 : CollatzResearch.WordTrace tailWord_7728704 prefixEnd_7728704 3968539988326634643756343 := by
  unfold tailWord_7728704
  simp only [CollatzResearch.WordTrace]
  refine ⟨140944496496116420200560583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187925995328155226934080777 140944496496116420200560583)
  ·
    refine ⟨211416744744174630300840875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140944496496116420200560583 211416744744174630300840875)
    ·
      refine ⟨317125117116261945451261313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211416744744174630300840875 317125117116261945451261313)
      ·
        refine ⟨237843837837196459088445985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317125117116261945451261313 237843837837196459088445985)
        ·
          refine ⟨178382878377897344316334489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237843837837196459088445985 178382878377897344316334489)
          ·
            refine ⟨133787158783423008237250867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178382878377897344316334489 133787158783423008237250867)
            ·
              refine ⟨200680738175134512355876301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133787158783423008237250867 200680738175134512355876301)
              ·
                refine ⟨75255276815675442133453613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200680738175134512355876301 75255276815675442133453613)
                ·
                  refine ⟨28220728805878290800045105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75255276815675442133453613 28220728805878290800045105)
                  ·
                    refine ⟨21165546604408718100033829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28220728805878290800045105 21165546604408718100033829)
                    ·
                      refine ⟨3968539988326634643756343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21165546604408718100033829 3968539988326634643756343)
                      ·
                        rfl

theorem cell23_7728704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_7728704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728704 prefixEnd_7728704 := by exact prefixLift 7728704
  have htrace : WordTrace (prefixWord ++ tailWord_7728704) baseStart_7728704 baseEnd_7728704 := by
    simpa [prefixWord, tailWord_7728704, baseEnd_7728704] using wordTrace_append hprefix tailTrace_7728704
  have hstable : (prefixWord ++ tailWord_7728704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728704).length < 2 ^ (prefixWord ++ tailWord_7728704).sum := by decide
  have hdescent : baseEnd_7728704 < baseStart_7728704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728758 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_7728758 : Nat := 118140960795 + 7728758 * 2 ^ 59
def prefixEnd_7728758 : Nat := 4983230072969 + 3 ^ 40 * 7728758 * 2
def baseEnd_7728758 : Nat := 3968567716281977432481095

theorem tailTrace_7728758 : CollatzResearch.WordTrace tailWord_7728758 prefixEnd_7728758 3968567716281977432481095 := by
  unfold tailWord_7728758
  simp only [CollatzResearch.WordTrace]
  refine ⟨17618185158377325476474183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187927308356024805082391285 17618185158377325476474183)
  ·
    refine ⟨26427277737565988214711275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17618185158377325476474183 26427277737565988214711275)
    ·
      refine ⟨39640916606348982322066913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26427277737565988214711275 39640916606348982322066913)
      ·
        refine ⟨29730687454761736741550185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39640916606348982322066913 29730687454761736741550185)
        ·
          refine ⟨22298015591071302556162639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29730687454761736741550185 22298015591071302556162639)
          ·
            refine ⟨33447023386606953834243959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22298015591071302556162639 33447023386606953834243959)
            ·
              refine ⟨50170535079910430751365939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33447023386606953834243959 50170535079910430751365939)
              ·
                refine ⟨75255802619865646127048909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50170535079910430751365939 75255802619865646127048909)
                ·
                  refine ⟨28220925982449617297643341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75255802619865646127048909 28220925982449617297643341)
                  ·
                    refine ⟨10582847243418606486616253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28220925982449617297643341 10582847243418606486616253)
                    ·
                      refine ⟨3968567716281977432481095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10582847243418606486616253 3968567716281977432481095)
                      ·
                        rfl

theorem cell23_7728758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_7728758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728758 prefixEnd_7728758 := by exact prefixLift 7728758
  have htrace : WordTrace (prefixWord ++ tailWord_7728758) baseStart_7728758 baseEnd_7728758 := by
    simpa [prefixWord, tailWord_7728758, baseEnd_7728758] using wordTrace_append hprefix tailTrace_7728758
  have hstable : (prefixWord ++ tailWord_7728758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728758).length < 2 ^ (prefixWord ++ tailWord_7728758).sum := by decide
  have hdescent : baseEnd_7728758 < baseStart_7728758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728775 : List Nat := [1, 1, 4, 2, 1, 4, 2, 2, 2, 1, 3]
def baseStart_7728775 : Nat := 118140960795 + 7728775 * 2 ^ 59
def prefixEnd_7728775 : Nat := 4983230072969 + 3 ^ 40 * 7728775 * 2
def baseEnd_7728775 : Nat := 3968576445453103865968517

theorem tailTrace_7728775 : CollatzResearch.WordTrace tailWord_7728775 prefixEnd_7728775 3968576445453103865968517 := by
  unfold tailWord_7728775
  simp only [CollatzResearch.WordTrace]
  refine ⟨281891582574975619526955779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187927721716650413017970519 281891582574975619526955779)
  ·
    refine ⟨422837373862463429290433669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281891582574975619526955779 422837373862463429290433669)
    ·
      refine ⟨79282007599211892991956313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 422837373862463429290433669 79282007599211892991956313)
      ·
        refine ⟨59461505699408919743967235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79282007599211892991956313 59461505699408919743967235)
        ·
          refine ⟨89192258549113379615950853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59461505699408919743967235 89192258549113379615950853)
          ·
            refine ⟨16723548477958758677990785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89192258549113379615950853 16723548477958758677990785)
            ·
              refine ⟨12542661358469069008493089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16723548477958758677990785 12542661358469069008493089)
              ·
                refine ⟨9406996018851801756369817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12542661358469069008493089 9406996018851801756369817)
                ·
                  refine ⟨7055247014138851317277363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9406996018851801756369817 7055247014138851317277363)
                  ·
                    refine ⟨10582870521208276975916045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7055247014138851317277363 10582870521208276975916045)
                    ·
                      refine ⟨3968576445453103865968517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10582870521208276975916045 3968576445453103865968517)
                      ·
                        rfl

theorem cell23_7728775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_7728775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728775 prefixEnd_7728775 := by exact prefixLift 7728775
  have htrace : WordTrace (prefixWord ++ tailWord_7728775) baseStart_7728775 baseEnd_7728775 := by
    simpa [prefixWord, tailWord_7728775, baseEnd_7728775] using wordTrace_append hprefix tailTrace_7728775
  have hstable : (prefixWord ++ tailWord_7728775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728775).length < 2 ^ (prefixWord ++ tailWord_7728775).sum := by decide
  have hdescent : baseEnd_7728775 < baseStart_7728775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728784 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 5]
def baseStart_7728784 : Nat := 118140960795 + 7728784 * 2 ^ 59
def prefixEnd_7728784 : Nat := 4983230072969 + 3 ^ 40 * 7728784 * 2
def baseEnd_7728784 : Nat := 3968581066778994330755975

theorem tailTrace_7728784 : CollatzResearch.WordTrace tailWord_7728784 prefixEnd_7728784 3968581066778994330755975 := by
  unfold tailWord_7728784
  simp only [CollatzResearch.WordTrace]
  refine ⟨140945955415971507032016703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187927940554628676042688937 140945955415971507032016703)
  ·
    refine ⟨211418933123957260548025055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140945955415971507032016703 211418933123957260548025055)
    ·
      refine ⟨317128399685935890822037583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211418933123957260548025055 317128399685935890822037583)
      ·
        refine ⟨475692599528903836233056375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317128399685935890822037583 475692599528903836233056375)
        ·
          refine ⟨713538899293355754349584563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475692599528903836233056375 713538899293355754349584563)
          ·
            refine ⟨1070308348940033631524376845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713538899293355754349584563 1070308348940033631524376845)
            ·
              refine ⟨401365630852512611821641317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1070308348940033631524376845 401365630852512611821641317)
              ·
                refine ⟨75256055784846114716557747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401365630852512611821641317 75256055784846114716557747)
                ·
                  refine ⟨112884083677269172074836621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75256055784846114716557747 112884083677269172074836621)
                  ·
                    refine ⟨42331531378975939528063733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112884083677269172074836621 42331531378975939528063733)
                    ·
                      refine ⟨3968581066778994330755975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42331531378975939528063733 3968581066778994330755975)
                      ·
                        rfl

theorem cell23_7728784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_7728784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728784 prefixEnd_7728784 := by exact prefixLift 7728784
  have htrace : WordTrace (prefixWord ++ tailWord_7728784) baseStart_7728784 baseEnd_7728784 := by
    simpa [prefixWord, tailWord_7728784, baseEnd_7728784] using wordTrace_append hprefix tailTrace_7728784
  have hstable : (prefixWord ++ tailWord_7728784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728784).length < 2 ^ (prefixWord ++ tailWord_7728784).sum := by decide
  have hdescent : baseEnd_7728784 < baseStart_7728784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728791 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 2, 6]
def baseStart_7728791 : Nat := 118140960795 + 7728791 * 2 ^ 59
def prefixEnd_7728791 : Nat := 4983230072969 + 3 ^ 40 * 7728791 * 2
def baseEnd_7728791 : Nat := 1322861553714525267789481

theorem tailTrace_7728791 : CollatzResearch.WordTrace tailWord_7728791 prefixEnd_7728791 1322861553714525267789481 := by
  unfold tailWord_7728791
  simp only [CollatzResearch.WordTrace]
  refine ⟨281892166142917654259538227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187928110761945102839692151 281892166142917654259538227)
  ·
    refine ⟨422838249214376481389307341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281892166142917654259538227 422838249214376481389307341)
    ·
      refine ⟨158564343455391180520990253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422838249214376481389307341 158564343455391180520990253)
      ·
        refine ⟨59461628795771692695371345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158564343455391180520990253 59461628795771692695371345)
        ·
          refine ⟨44596221596828769521528509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59461628795771692695371345 44596221596828769521528509)
          ·
            refine ⟨16723583098810788570573191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44596221596828769521528509 16723583098810788570573191)
            ·
              refine ⟨25085374648216182855859787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16723583098810788570573191 25085374648216182855859787)
              ·
                refine ⟨37628061972324274283789681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25085374648216182855859787 37628061972324274283789681)
                ·
                  refine ⟨28221046479243205712842261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37628061972324274283789681 28221046479243205712842261)
                  ·
                    refine ⟨1322861553714525267789481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28221046479243205712842261 1322861553714525267789481)
                    ·
                      rfl

theorem cell23_7728791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_7728791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728791 prefixEnd_7728791 := by exact prefixLift 7728791
  have htrace : WordTrace (prefixWord ++ tailWord_7728791) baseStart_7728791 baseEnd_7728791 := by
    simpa [prefixWord, tailWord_7728791, baseEnd_7728791] using wordTrace_append hprefix tailTrace_7728791
  have hstable : (prefixWord ++ tailWord_7728791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728791).length < 2 ^ (prefixWord ++ tailWord_7728791).sum := by decide
  have hdescent : baseEnd_7728791 < baseStart_7728791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728831 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 3]
def baseStart_7728831 : Nat := 118140960795 + 7728831 * 2 ^ 59
def prefixEnd_7728831 : Nat := 4983230072969 + 3 ^ 40 * 7728831 * 2
def baseEnd_7728831 : Nat := 3968605200369755646868259

theorem tailTrace_7728831 : CollatzResearch.WordTrace tailWord_7728831 prefixEnd_7728831 3968605200369755646868259 := by
  unfold tailWord_7728831
  simp only [CollatzResearch.WordTrace]
  refine ⟨281893625062772741090994347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187929083375181827393996231 281893625062772741090994347)
  ·
    refine ⟨422840437594159111636491521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281893625062772741090994347 422840437594159111636491521)
    ·
      refine ⟨317130328195619333727368641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422840437594159111636491521 317130328195619333727368641)
      ·
        refine ⟨237847746146714500295526481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317130328195619333727368641 237847746146714500295526481)
        ·
          refine ⟨178385809610035875221644861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237847746146714500295526481 178385809610035875221644861)
          ·
            refine ⟨66894678603763453208116823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178385809610035875221644861 66894678603763453208116823)
            ·
              refine ⟨100342017905645179812175235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66894678603763453208116823 100342017905645179812175235)
              ·
                refine ⟨150513026858467769718262853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100342017905645179812175235 150513026858467769718262853)
                ·
                  refine ⟨28221192535962706822174285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150513026858467769718262853 28221192535962706822174285)
                  ·
                    refine ⟨10582947200986015058315357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28221192535962706822174285 10582947200986015058315357)
                    ·
                      refine ⟨3968605200369755646868259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10582947200986015058315357 3968605200369755646868259)
                      ·
                        rfl

theorem cell23_7728831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_7728831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728831 prefixEnd_7728831 := by exact prefixLift 7728831
  have htrace : WordTrace (prefixWord ++ tailWord_7728831) baseStart_7728831 baseEnd_7728831 := by
    simpa [prefixWord, tailWord_7728831, baseEnd_7728831] using wordTrace_append hprefix tailTrace_7728831
  have hstable : (prefixWord ++ tailWord_7728831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728831).length < 2 ^ (prefixWord ++ tailWord_7728831).sum := by decide
  have hdescent : baseEnd_7728831 < baseStart_7728831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728845 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_7728845 : Nat := 118140960795 + 7728845 * 2 ^ 59
def prefixEnd_7728845 : Nat := 4983230072969 + 3 ^ 40 * 7728845 * 2
def baseEnd_7728845 : Nat := 3968612389098918592093195

theorem tailTrace_7728845 : CollatzResearch.WordTrace tailWord_7728845 prefixEnd_7728845 3968612389098918592093195 := by
  unfold tailWord_7728845
  simp only [CollatzResearch.WordTrace]
  refine ⟨281894135684722021482003989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187929423789814680988002659 281894135684722021482003989)
  ·
    refine ⟨13213787610221344756968937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 281894135684722021482003989 13213787610221344756968937)
    ·
      refine ⟨9910340707666008567726703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13213787610221344756968937 9910340707666008567726703)
      ·
        refine ⟨14865511061499012851590055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9910340707666008567726703 14865511061499012851590055)
        ·
          refine ⟨22298266592248519277385083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14865511061499012851590055 22298266592248519277385083)
          ·
            refine ⟨33447399888372778916077625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22298266592248519277385083 33447399888372778916077625)
            ·
              refine ⟨25085549916279584187058219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33447399888372778916077625 25085549916279584187058219)
              ·
                refine ⟨37628324874419376280587329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25085549916279584187058219 37628324874419376280587329)
                ·
                  refine ⟨28221243655814532210440497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37628324874419376280587329 28221243655814532210440497)
                  ·
                    refine ⟨21165932741860899157830373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28221243655814532210440497 21165932741860899157830373)
                    ·
                      refine ⟨3968612389098918592093195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21165932741860899157830373 3968612389098918592093195)
                      ·
                        rfl

theorem cell23_7728845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_7728845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728845 prefixEnd_7728845 := by exact prefixLift 7728845
  have htrace : WordTrace (prefixWord ++ tailWord_7728845) baseStart_7728845 baseEnd_7728845 := by
    simpa [prefixWord, tailWord_7728845, baseEnd_7728845] using wordTrace_append hprefix tailTrace_7728845
  have hstable : (prefixWord ++ tailWord_7728845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728845).length < 2 ^ (prefixWord ++ tailWord_7728845).sum := by decide
  have hdescent : baseEnd_7728845 < baseStart_7728845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728888 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 2, 4, 2]
def baseStart_7728888 : Nat := 118140960795 + 7728888 * 2 ^ 59
def prefixEnd_7728888 : Nat := 4983230072969 + 3 ^ 40 * 7728888 * 2
def baseEnd_7728888 : Nat := 3968634468767061923855497

theorem tailTrace_7728888 : CollatzResearch.WordTrace tailWord_7728888 prefixEnd_7728888 3968634468767061923855497 := by
  unfold tailWord_7728888
  simp only [CollatzResearch.WordTrace]
  refine ⟨140947852011783119912909659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187930469349044159883879545 140947852011783119912909659)
  ·
    refine ⟨211421778017674679869364489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140947852011783119912909659 211421778017674679869364489)
    ·
      refine ⟨158566333513256009902023367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211421778017674679869364489 158566333513256009902023367)
      ·
        refine ⟨237849500269884014853035051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158566333513256009902023367 237849500269884014853035051)
        ·
          refine ⟨356774250404826022279552577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237849500269884014853035051 356774250404826022279552577)
          ·
            refine ⟨267580687803619516709664433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356774250404826022279552577 267580687803619516709664433)
            ·
              refine ⟨200685515852714637532248325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267580687803619516709664433 200685515852714637532248325)
              ·
                refine ⟨37628534222383994537296561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200685515852714637532248325 37628534222383994537296561)
                ·
                  refine ⟨28221400666787995902972421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37628534222383994537296561 28221400666787995902972421)
                  ·
                    refine ⟨5291512625022749231807329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28221400666787995902972421 5291512625022749231807329)
                    ·
                      refine ⟨3968634468767061923855497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5291512625022749231807329 3968634468767061923855497)
                      ·
                        rfl

theorem cell23_7728888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2, 4, 2].length) (baseStart_7728888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728888 prefixEnd_7728888 := by exact prefixLift 7728888
  have htrace : WordTrace (prefixWord ++ tailWord_7728888) baseStart_7728888 baseEnd_7728888 := by
    simpa [prefixWord, tailWord_7728888, baseEnd_7728888] using wordTrace_append hprefix tailTrace_7728888
  have hstable : (prefixWord ++ tailWord_7728888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728888).length < 2 ^ (prefixWord ++ tailWord_7728888).sum := by decide
  have hdescent : baseEnd_7728888 < baseStart_7728888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728891 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 3]
def baseStart_7728891 : Nat := 118140960795 + 7728891 * 2 ^ 59
def prefixEnd_7728891 : Nat := 4983230072969 + 3 ^ 40 * 7728891 * 2
def baseEnd_7728891 : Nat := 3968636009209025412117983

theorem tailTrace_7728891 : CollatzResearch.WordTrace tailWord_7728891 prefixEnd_7728891 3968636009209025412117983 := by
  unfold tailWord_7728891
  simp only [CollatzResearch.WordTrace]
  refine ⟨281895813442555371338178527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187930542295036914225452351 281895813442555371338178527)
  ·
    refine ⟨422843720163833057007267791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281895813442555371338178527 422843720163833057007267791)
    ·
      refine ⟨634265580245749585510901687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422843720163833057007267791 634265580245749585510901687)
      ·
        refine ⟨951398370368624378266352531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634265580245749585510901687 951398370368624378266352531)
        ·
          refine ⟨1427097555552936567399528797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951398370368624378266352531 1427097555552936567399528797)
          ·
            refine ⟨535161583332351212774823299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1427097555552936567399528797 535161583332351212774823299)
            ·
              refine ⟨802742374998526819162234949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535161583332351212774823299 802742374998526819162234949)
              ·
                refine ⟨150514195312223778592919053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 802742374998526819162234949 150514195312223778592919053)
                ·
                  refine ⟨56442823242083916972344645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150514195312223778592919053 56442823242083916972344645)
                  ·
                    refine ⟨10583029357890734432314621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56442823242083916972344645 10583029357890734432314621)
                    ·
                      refine ⟨3968636009209025412117983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10583029357890734432314621 3968636009209025412117983)
                      ·
                        rfl

theorem cell23_7728891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 3].length) (baseStart_7728891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728891 prefixEnd_7728891 := by exact prefixLift 7728891
  have htrace : WordTrace (prefixWord ++ tailWord_7728891) baseStart_7728891 baseEnd_7728891 := by
    simpa [prefixWord, tailWord_7728891, baseEnd_7728891] using wordTrace_append hprefix tailTrace_7728891
  have hstable : (prefixWord ++ tailWord_7728891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728891).length < 2 ^ (prefixWord ++ tailWord_7728891).sum := by decide
  have hdescent : baseEnd_7728891 < baseStart_7728891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728972 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 3, 1, 3]
def baseStart_7728972 : Nat := 118140960795 + 7728972 * 2 ^ 59
def prefixEnd_7728972 : Nat := 4983230072969 + 3 ^ 40 * 7728972 * 2
def baseEnd_7728972 : Nat := 3968677601142039595205111

theorem tailTrace_7728972 : CollatzResearch.WordTrace tailWord_7728972 prefixEnd_7728972 3968677601142039595205111 := by
  unfold tailWord_7728972
  simp only [CollatzResearch.WordTrace]
  refine ⟨140949383877630961085938585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187932511836841281447918113 140949383877630961085938585)
  ·
    refine ⟨105712037908223220814453939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140949383877630961085938585 105712037908223220814453939)
    ·
      refine ⟨158568056862334831221680909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105712037908223220814453939 158568056862334831221680909)
      ·
        refine ⟨59463021323375561708130341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158568056862334831221680909 59463021323375561708130341)
        ·
          refine ⟨11149316498132917820274439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59463021323375561708130341 11149316498132917820274439)
          ·
            refine ⟨16723974747199376730411659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11149316498132917820274439 16723974747199376730411659)
            ·
              refine ⟨25085962120799065095617489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16723974747199376730411659 25085962120799065095617489)
              ·
                refine ⟨18814471590599298821713117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25085962120799065095617489 18814471590599298821713117)
                ·
                  refine ⟨7055426846474737058142419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18814471590599298821713117 7055426846474737058142419)
                  ·
                    refine ⟨10583140269712105587213629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7055426846474737058142419 10583140269712105587213629)
                    ·
                      refine ⟨3968677601142039595205111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10583140269712105587213629 3968677601142039595205111)
                      ·
                        rfl

theorem cell23_7728972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_7728972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728972 prefixEnd_7728972 := by exact prefixLift 7728972
  have htrace : WordTrace (prefixWord ++ tailWord_7728972) baseStart_7728972 baseEnd_7728972 := by
    simpa [prefixWord, tailWord_7728972, baseEnd_7728972] using wordTrace_append hprefix tailTrace_7728972
  have hstable : (prefixWord ++ tailWord_7728972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728972).length < 2 ^ (prefixWord ++ tailWord_7728972).sum := by decide
  have hdescent : baseEnd_7728972 < baseStart_7728972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7728992 : List Nat := [2, 1, 1, 3, 3, 4, 2, 1, 1, 5]
def baseStart_7728992 : Nat := 118140960795 + 7728992 * 2 ^ 59
def prefixEnd_7728992 : Nat := 4983230072969 + 3 ^ 40 * 7728992 * 2
def baseEnd_7728992 : Nat := 1322895956918376505651673

theorem tailTrace_7728992 : CollatzResearch.WordTrace tailWord_7728992 prefixEnd_7728992 1322895956918376505651673 := by
  unfold tailWord_7728992
  simp only [CollatzResearch.WordTrace]
  refine ⟨140949748607594732793802615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187932998143459643725070153 140949748607594732793802615)
  ·
    refine ⟨211424622911392099190703923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140949748607594732793802615 211424622911392099190703923)
    ·
      refine ⟨317136934367088148786055885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211424622911392099190703923 317136934367088148786055885)
      ·
        refine ⟨118926350387658055794770957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317136934367088148786055885 118926350387658055794770957)
        ·
          refine ⟨44597381395371770923039109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118926350387658055794770957 44597381395371770923039109)
          ·
            refine ⟨8362009011632207048069833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44597381395371770923039109 8362009011632207048069833)
            ·
              refine ⟨6271506758724155286052375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8362009011632207048069833 6271506758724155286052375)
              ·
                refine ⟨9407260138086232929078563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6271506758724155286052375 9407260138086232929078563)
                ·
                  refine ⟨14110890207129349393617845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9407260138086232929078563 14110890207129349393617845)
                  ·
                    refine ⟨1322895956918376505651673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14110890207129349393617845 1322895956918376505651673)
                    ·
                      rfl

theorem cell23_7728992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 1, 5].length) (baseStart_7728992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7728992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7728992 prefixEnd_7728992 := by exact prefixLift 7728992
  have htrace : WordTrace (prefixWord ++ tailWord_7728992) baseStart_7728992 baseEnd_7728992 := by
    simpa [prefixWord, tailWord_7728992, baseEnd_7728992] using wordTrace_append hprefix tailTrace_7728992
  have hstable : (prefixWord ++ tailWord_7728992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7728992).length < 2 ^ (prefixWord ++ tailWord_7728992).sum := by decide
  have hdescent : baseEnd_7728992 < baseStart_7728992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7728992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729011 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 7]
def baseStart_7729011 : Nat := 118140960795 + 7729011 * 2 ^ 59
def prefixEnd_7729011 : Nat := 4983230072969 + 3 ^ 40 * 7729011 * 2
def baseEnd_7729011 : Nat := 3968697626887564942617431

theorem tailTrace_7729011 : CollatzResearch.WordTrace tailWord_7729011 prefixEnd_7729011 3968697626887564942617431 := by
  unfold tailWord_7729011
  simp only [CollatzResearch.WordTrace]
  refine ⟨281900190202120631832546887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187933460134747087888364591 281900190202120631832546887)
  ·
    refine ⟨422850285303180947748820331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281900190202120631832546887 422850285303180947748820331)
    ·
      refine ⟨634275427954771421623230497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422850285303180947748820331 634275427954771421623230497)
      ·
        refine ⟨475706570966078566217422873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634275427954771421623230497 475706570966078566217422873)
        ·
          refine ⟨356779928224558924663067155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475706570966078566217422873 356779928224558924663067155)
          ·
            refine ⟨535169892336838386994600733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356779928224558924663067155 535169892336838386994600733)
            ·
              refine ⟨200688709626314395122975275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 535169892336838386994600733 200688709626314395122975275)
              ·
                refine ⟨301033064439471592684462913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200688709626314395122975275 301033064439471592684462913)
                ·
                  refine ⟨225774798329603694513347185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301033064439471592684462913 225774798329603694513347185)
                  ·
                    refine ⟨169331098747202770885010389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 225774798329603694513347185 169331098747202770885010389)
                    ·
                      refine ⟨3968697626887564942617431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169331098747202770885010389 3968697626887564942617431)
                      ·
                        rfl

theorem cell23_7729011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_7729011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729011 prefixEnd_7729011 := by exact prefixLift 7729011
  have htrace : WordTrace (prefixWord ++ tailWord_7729011) baseStart_7729011 baseEnd_7729011 := by
    simpa [prefixWord, tailWord_7729011, baseEnd_7729011] using wordTrace_append hprefix tailTrace_7729011
  have hstable : (prefixWord ++ tailWord_7729011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729011).length < 2 ^ (prefixWord ++ tailWord_7729011).sum := by decide
  have hdescent : baseEnd_7729011 < baseStart_7729011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729022 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_7729022 : Nat := 118140960795 + 7729022 * 2 ^ 59
def prefixEnd_7729022 : Nat := 4983230072969 + 3 ^ 40 * 7729022 * 2
def baseEnd_7729022 : Nat := 1322901091724921466526627

theorem tailTrace_7729022 : CollatzResearch.WordTrace tailWord_7729022 prefixEnd_7729022 1322901091724921466526627 := by
  unfold tailWord_7729022
  simp only [CollatzResearch.WordTrace]
  refine ⟨35237573925635097588899665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187933727603387187140798213 35237573925635097588899665)
  ·
    refine ⟨26428180444226323191674749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35237573925635097588899665 26428180444226323191674749)
    ·
      refine ⟨9910567666584871196878031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26428180444226323191674749 9910567666584871196878031)
      ·
        refine ⟨14865851499877306795317047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9910567666584871196878031 14865851499877306795317047)
        ·
          refine ⟨22298777249815960192975571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14865851499877306795317047 22298777249815960192975571)
          ·
            refine ⟨33448165874723940289463357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22298777249815960192975571 33448165874723940289463357)
            ·
              refine ⟨12543062203021477608548759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33448165874723940289463357 12543062203021477608548759)
              ·
                refine ⟨18814593304532216412823139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12543062203021477608548759 18814593304532216412823139)
                ·
                  refine ⟨28221889956798324619234709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18814593304532216412823139 28221889956798324619234709)
                  ·
                    refine ⟨1322901091724921466526627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28221889956798324619234709 1322901091724921466526627)
                    ·
                      rfl

theorem cell23_7729022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_7729022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729022 prefixEnd_7729022 := by exact prefixLift 7729022
  have htrace : WordTrace (prefixWord ++ tailWord_7729022) baseStart_7729022 baseEnd_7729022 := by
    simpa [prefixWord, tailWord_7729022, baseEnd_7729022] using wordTrace_append hprefix tailTrace_7729022
  have hstable : (prefixWord ++ tailWord_7729022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729022).length < 2 ^ (prefixWord ++ tailWord_7729022).sum := by decide
  have hdescent : baseEnd_7729022 < baseStart_7729022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729045 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 6, 1, 3]
def baseStart_7729045 : Nat := 118140960795 + 7729045 * 2 ^ 59
def prefixEnd_7729045 : Nat := 4983230072969 + 3 ^ 40 * 7729045 * 2
def baseEnd_7729045 : Nat := 3968715085229817809592275

theorem tailTrace_7729045 : CollatzResearch.WordTrace tailWord_7729045 prefixEnd_7729045 3968715085229817809592275 := by
  unfold tailWord_7729045
  simp only [CollatzResearch.WordTrace]
  refine ⟨281901430283997455639284589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187934286855998303759523059 281901430283997455639284589)
  ·
    refine ⟨105713036356499045864731721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281901430283997455639284589 105713036356499045864731721)
    ·
      refine ⟨79284777267374284398548791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105713036356499045864731721 79284777267374284398548791)
      ·
        refine ⟨118927165901061426597823187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79284777267374284398548791 118927165901061426597823187)
        ·
          refine ⟨178390748851592139896734781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118927165901061426597823187 178390748851592139896734781)
          ·
            refine ⟨66896530819347052461275543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178390748851592139896734781 66896530819347052461275543)
            ·
              refine ⟨100344796229020578691913315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66896530819347052461275543 100344796229020578691913315)
              ·
                refine ⟨150517194343530868037869973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100344796229020578691913315 150517194343530868037869973)
                ·
                  refine ⟨7055493484853009439275155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150517194343530868037869973 7055493484853009439275155)
                  ·
                    refine ⟨10583240227279514158912733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7055493484853009439275155 10583240227279514158912733)
                    ·
                      refine ⟨3968715085229817809592275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10583240227279514158912733 3968715085229817809592275)
                      ·
                        rfl

theorem cell23_7729045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_7729045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729045 prefixEnd_7729045 := by exact prefixLift 7729045
  have htrace : WordTrace (prefixWord ++ tailWord_7729045) baseStart_7729045 baseEnd_7729045 := by
    simpa [prefixWord, tailWord_7729045, baseEnd_7729045] using wordTrace_append hprefix tailTrace_7729045
  have hstable : (prefixWord ++ tailWord_7729045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729045).length < 2 ^ (prefixWord ++ tailWord_7729045).sum := by decide
  have hdescent : baseEnd_7729045 < baseStart_7729045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729063 : List Nat := [1, 1, 6, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_7729063 : Nat := 118140960795 + 7729063 * 2 ^ 59
def prefixEnd_7729063 : Nat := 4983230072969 + 3 ^ 40 * 7729063 * 2
def baseEnd_7729063 : Nat := 3968724327881598739167193

theorem tailTrace_7729063 : CollatzResearch.WordTrace tailWord_7729063 prefixEnd_7729063 3968724327881598739167193 := by
  unfold tailWord_7729063
  simp only [CollatzResearch.WordTrace]
  refine ⟨281902086797932244713439843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187934724531954829808959895 281902086797932244713439843)
  ·
    refine ⟨422853130196898367070159765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281902086797932244713439843 422853130196898367070159765)
    ·
      refine ⟨19821240477979610956413739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 422853130196898367070159765 19821240477979610956413739)
      ·
        refine ⟨29731860716969416434620609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19821240477979610956413739 29731860716969416434620609)
        ·
          refine ⟨22298895537727062325965457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29731860716969416434620609 22298895537727062325965457)
          ·
            refine ⟨16724171653295296744474093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22298895537727062325965457 16724171653295296744474093)
            ·
              refine ⟨6271564369985736279177785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16724171653295296744474093 6271564369985736279177785)
              ·
                refine ⟨4703673277489302209383339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6271564369985736279177785 4703673277489302209383339)
                ·
                  refine ⟨7055509916233953314075009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4703673277489302209383339 7055509916233953314075009)
                  ·
                    refine ⟨5291632437175464985556257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7055509916233953314075009 5291632437175464985556257)
                    ·
                      refine ⟨3968724327881598739167193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5291632437175464985556257 3968724327881598739167193)
                      ·
                        rfl

theorem cell23_7729063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_7729063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729063 prefixEnd_7729063 := by exact prefixLift 7729063
  have htrace : WordTrace (prefixWord ++ tailWord_7729063) baseStart_7729063 baseEnd_7729063 := by
    simpa [prefixWord, tailWord_7729063, baseEnd_7729063] using wordTrace_append hprefix tailTrace_7729063
  have hstable : (prefixWord ++ tailWord_7729063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729063).length < 2 ^ (prefixWord ++ tailWord_7729063).sum := by decide
  have hdescent : baseEnd_7729063 < baseStart_7729063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729088 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 5]
def baseStart_7729088 : Nat := 118140960795 + 7729088 * 2 ^ 59
def prefixEnd_7729088 : Nat := 4983230072969 + 3 ^ 40 * 7729088 * 2
def baseEnd_7729088 : Nat := 3968737164897961141354577

theorem tailTrace_7729088 : CollatzResearch.WordTrace tailWord_7729088 prefixEnd_7729088 3968737164897961141354577 := by
  unfold tailWord_7729088
  simp only [CollatzResearch.WordTrace]
  refine ⟨140951499311420836991549959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187935332415227782655399945 140951499311420836991549959)
  ·
    refine ⟨211427248967131255487324939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140951499311420836991549959 211427248967131255487324939)
    ·
      refine ⟨317140873450696883230987409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211427248967131255487324939 317140873450696883230987409)
      ·
        refine ⟨237855655088022662423240557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317140873450696883230987409 237855655088022662423240557)
        ·
          refine ⟨89195870658008498408715209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237855655088022662423240557 89195870658008498408715209)
          ·
            refine ⟨66896902993506373806536407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89195870658008498408715209 66896902993506373806536407)
            ·
              refine ⟨100345354490259560709804611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66896902993506373806536407 100345354490259560709804611)
              ·
                refine ⟨150518031735389341064706917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100345354490259560709804611 150518031735389341064706917)
                ·
                  refine ⟨28222130950385501449632547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150518031735389341064706917 28222130950385501449632547)
                  ·
                    refine ⟨42333196425578252174448821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28222130950385501449632547 42333196425578252174448821)
                    ·
                      refine ⟨3968737164897961141354577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42333196425578252174448821 3968737164897961141354577)
                      ·
                        rfl

theorem cell23_7729088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_7729088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729088 prefixEnd_7729088 := by exact prefixLift 7729088
  have htrace : WordTrace (prefixWord ++ tailWord_7729088) baseStart_7729088 baseEnd_7729088 := by
    simpa [prefixWord, tailWord_7729088, baseEnd_7729088] using wordTrace_append hprefix tailTrace_7729088
  have hstable : (prefixWord ++ tailWord_7729088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729088).length < 2 ^ (prefixWord ++ tailWord_7729088).sum := by decide
  have hdescent : baseEnd_7729088 < baseStart_7729088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729102 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2]
def baseStart_7729102 : Nat := 118140960795 + 7729102 * 2 ^ 59
def prefixEnd_7729102 : Nat := 4983230072969 + 3 ^ 40 * 7729102 * 2
def baseEnd_7729102 : Nat := 3968744353627124086579513

theorem tailTrace_7729102 : CollatzResearch.WordTrace tailWord_7729102 prefixEnd_7729102 3968744353627124086579513 := by
  unfold tailWord_7729102
  simp only [CollatzResearch.WordTrace]
  refine ⟨35237938655598869296763695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187935672829860636249406373 35237938655598869296763695)
  ·
    refine ⟨52856907983398303945145543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35237938655598869296763695 52856907983398303945145543)
    ·
      refine ⟨79285361975097455917718315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52856907983398303945145543 79285361975097455917718315)
      ·
        refine ⟨118928042962646183876577473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79285361975097455917718315 118928042962646183876577473)
        ·
          refine ⟨89196032221984637907433105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118928042962646183876577473 89196032221984637907433105)
          ·
            refine ⟨66897024166488478430574829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89196032221984637907433105 66897024166488478430574829)
            ·
              refine ⟨25086384062433179411465561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66897024166488478430574829 25086384062433179411465561)
              ·
                refine ⟨18814788046824884558599171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25086384062433179411465561 18814788046824884558599171)
                ·
                  refine ⟨28222182070237326837898757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18814788046824884558599171 28222182070237326837898757)
                  ·
                    refine ⟨5291659138169498782106017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28222182070237326837898757 5291659138169498782106017)
                    ·
                      refine ⟨3968744353627124086579513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5291659138169498782106017 3968744353627124086579513)
                      ·
                        rfl

theorem cell23_7729102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_7729102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729102 prefixEnd_7729102 := by exact prefixLift 7729102
  have htrace : WordTrace (prefixWord ++ tailWord_7729102) baseStart_7729102 baseEnd_7729102 := by
    simpa [prefixWord, tailWord_7729102, baseEnd_7729102] using wordTrace_append hprefix tailTrace_7729102
  have hstable : (prefixWord ++ tailWord_7729102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729102).length < 2 ^ (prefixWord ++ tailWord_7729102).sum := by decide
  have hdescent : baseEnd_7729102 < baseStart_7729102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729119 : List Nat := [1, 1, 2, 3, 4, 1, 1, 4, 2, 2, 2]
def baseStart_7729119 : Nat := 118140960795 + 7729119 * 2 ^ 59
def prefixEnd_7729119 : Nat := 4983230072969 + 3 ^ 40 * 7729119 * 2
def baseEnd_7729119 : Nat := 3968753082798250520066935

theorem tailTrace_7729119 : CollatzResearch.WordTrace tailWord_7729119 prefixEnd_7729119 3968753082798250520066935 := by
  unfold tailWord_7729119
  simp only [CollatzResearch.WordTrace]
  refine ⟨281904129285729366277478411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187936086190486244184985607 281904129285729366277478411)
  ·
    refine ⟨422856193928594049416217617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281904129285729366277478411 422856193928594049416217617)
    ·
      refine ⟨317142145446445537062163213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422856193928594049416217617 317142145446445537062163213)
      ·
        refine ⟨118928304542417076398311205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317142145446445537062163213 118928304542417076398311205)
        ·
          refine ⟨22299057101703201824683351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118928304542417076398311205 22299057101703201824683351)
          ·
            refine ⟨33448585652554802737025027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22299057101703201824683351 33448585652554802737025027)
            ·
              refine ⟨50172878478832204105537541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33448585652554802737025027 50172878478832204105537541)
              ·
                refine ⟨9407414714781038269788289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50172878478832204105537541 9407414714781038269788289)
                ·
                  refine ⟨7055561036085778702341217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9407414714781038269788289 7055561036085778702341217)
                  ·
                    refine ⟨5291670777064334026755913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7055561036085778702341217 5291670777064334026755913)
                    ·
                      refine ⟨3968753082798250520066935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5291670777064334026755913 3968753082798250520066935)
                      ·
                        rfl

theorem cell23_7729119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_7729119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729119 prefixEnd_7729119 := by exact prefixLift 7729119
  have htrace : WordTrace (prefixWord ++ tailWord_7729119) baseStart_7729119 baseEnd_7729119 := by
    simpa [prefixWord, tailWord_7729119, baseEnd_7729119] using wordTrace_append hprefix tailTrace_7729119
  have hstable : (prefixWord ++ tailWord_7729119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729119).length < 2 ^ (prefixWord ++ tailWord_7729119).sum := by decide
  have hdescent : baseEnd_7729119 < baseStart_7729119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729128 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_7729128 : Nat := 118140960795 + 7729128 * 2 ^ 59
def prefixEnd_7729128 : Nat := 4983230072969 + 3 ^ 40 * 7729128 * 2
def baseEnd_7729128 : Nat := 3968757704124140984854393

theorem tailTrace_7729128 : CollatzResearch.WordTrace tailWord_7729128 prefixEnd_7729128 3968757704124140984854393 := by
  unfold tailWord_7729128
  simp only [CollatzResearch.WordTrace]
  refine ⟨140952228771348380407278019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187936305028464507209704025 140952228771348380407278019)
  ·
    refine ⟨211428343157022570610917029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140952228771348380407278019 211428343157022570610917029)
    ·
      refine ⟨39642814341941731989546943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211428343157022570610917029 39642814341941731989546943)
      ·
        refine ⟨59464221512912597984320415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39642814341941731989546943 59464221512912597984320415)
        ·
          refine ⟨89196332269368896976480623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59464221512912597984320415 89196332269368896976480623)
          ·
            refine ⟨133794498404053345464720935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89196332269368896976480623 133794498404053345464720935)
            ·
              refine ⟨200691747606080018197081403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133794498404053345464720935 200691747606080018197081403)
              ·
                refine ⟨301037621409120027295622105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200691747606080018197081403 301037621409120027295622105)
                ·
                  refine ⟨225778216056840020471716579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301037621409120027295622105 225778216056840020471716579)
                  ·
                    refine ⟨338667324085260030707574869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 225778216056840020471716579 338667324085260030707574869)
                    ·
                      refine ⟨3968757704124140984854393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 338667324085260030707574869 3968757704124140984854393)
                      ·
                        rfl

theorem cell23_7729128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_7729128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729128 prefixEnd_7729128 := by exact prefixLift 7729128
  have htrace : WordTrace (prefixWord ++ tailWord_7729128) baseStart_7729128 baseEnd_7729128 := by
    simpa [prefixWord, tailWord_7729128, baseEnd_7729128] using wordTrace_append hprefix tailTrace_7729128
  have hstable : (prefixWord ++ tailWord_7729128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729128).length < 2 ^ (prefixWord ++ tailWord_7729128).sum := by decide
  have hdescent : baseEnd_7729128 < baseStart_7729128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729135 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 3]
def baseStart_7729135 : Nat := 118140960795 + 7729135 * 2 ^ 59
def prefixEnd_7729135 : Nat := 4983230072969 + 3 ^ 40 * 7729135 * 2
def baseEnd_7729135 : Nat := 3968761298488722457466861

theorem tailTrace_7729135 : CollatzResearch.WordTrace tailWord_7729135 prefixEnd_7729135 3968761298488722457466861 := by
  unfold tailWord_7729135
  simp only [CollatzResearch.WordTrace]
  refine ⟨281904712853671401010060859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187936475235780934006707239 281904712853671401010060859)
  ·
    refine ⟨422857069280507101515091289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281904712853671401010060859 422857069280507101515091289)
    ·
      refine ⟨317142801960380326136318467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422857069280507101515091289 317142801960380326136318467)
      ·
        refine ⟨475714202940570489204477701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317142801960380326136318467 475714202940570489204477701)
        ·
          refine ⟨89196413051356966725839569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 475714202940570489204477701 89196413051356966725839569)
          ·
            refine ⟨66897309788517725044379677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89196413051356966725839569 66897309788517725044379677)
            ·
              refine ⟨25086491170694146891642379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66897309788517725044379677 25086491170694146891642379)
              ·
                refine ⟨37629736756041220337463569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25086491170694146891642379 37629736756041220337463569)
                ·
                  refine ⟨28222302567030915253097677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37629736756041220337463569 28222302567030915253097677)
                  ·
                    refine ⟨10583363462636593219911629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28222302567030915253097677 10583363462636593219911629)
                    ·
                      refine ⟨3968761298488722457466861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10583363462636593219911629 3968761298488722457466861)
                      ·
                        rfl

theorem cell23_7729135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 3].length) (baseStart_7729135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729135 prefixEnd_7729135 := by exact prefixLift 7729135
  have htrace : WordTrace (prefixWord ++ tailWord_7729135) baseStart_7729135 baseEnd_7729135 := by
    simpa [prefixWord, tailWord_7729135, baseEnd_7729135] using wordTrace_append hprefix tailTrace_7729135
  have hstable : (prefixWord ++ tailWord_7729135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729135).length < 2 ^ (prefixWord ++ tailWord_7729135).sum := by decide
  have hdescent : baseEnd_7729135 < baseStart_7729135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729142 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_7729142 : Nat := 118140960795 + 7729142 * 2 ^ 59
def prefixEnd_7729142 : Nat := 4983230072969 + 3 ^ 40 * 7729142 * 2
def baseEnd_7729142 : Nat := 440973876983700436675481

theorem tailTrace_7729142 : CollatzResearch.WordTrace tailWord_7729142 prefixEnd_7729142 440973876983700436675481 := by
  unfold tailWord_7729142
  simp only [CollatzResearch.WordTrace]
  refine ⟨17619060510290377575347855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187936645443097360803710453 17619060510290377575347855)
  ·
    refine ⟨26428590765435566363021783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17619060510290377575347855 26428590765435566363021783)
    ·
      refine ⟨39642886148153349544532675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26428590765435566363021783 39642886148153349544532675)
      ·
        refine ⟨59464329222230024316799013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39642886148153349544532675 59464329222230024316799013)
        ·
          refine ⟨11149561729168129559399815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59464329222230024316799013 11149561729168129559399815)
          ·
            refine ⟨16724342593752194339099723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11149561729168129559399815 16724342593752194339099723)
            ·
              refine ⟨25086513890628291508649585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16724342593752194339099723 25086513890628291508649585)
              ·
                refine ⟨18814885417971218631487189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25086513890628291508649585 18814885417971218631487189)
                ·
                  refine ⟨440973876983700436675481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18814885417971218631487189 440973876983700436675481)
                  ·
                    rfl

theorem cell23_7729142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_7729142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729142 prefixEnd_7729142 := by exact prefixLift 7729142
  have htrace : WordTrace (prefixWord ++ tailWord_7729142) baseStart_7729142 baseEnd_7729142 := by
    simpa [prefixWord, tailWord_7729142, baseEnd_7729142] using wordTrace_append hprefix tailTrace_7729142
  have hstable : (prefixWord ++ tailWord_7729142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729142).length < 2 ^ (prefixWord ++ tailWord_7729142).sum := by decide
  have hdescent : baseEnd_7729142 < baseStart_7729142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729195 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 3]
def baseStart_7729195 : Nat := 118140960795 + 7729195 * 2 ^ 59
def prefixEnd_7729195 : Nat := 4983230072969 + 3 ^ 40 * 7729195 * 2
def baseEnd_7729195 : Nat := 3968792107327992222716585

theorem tailTrace_7729195 : CollatzResearch.WordTrace tailWord_7729195 prefixEnd_7729195 3968792107327992222716585 := by
  unfold tailWord_7729195
  simp only [CollatzResearch.WordTrace]
  refine ⟨281906901233454031257245039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187937934155636020838163359 281906901233454031257245039)
  ·
    refine ⟨422860351850181046885867559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281906901233454031257245039 422860351850181046885867559)
    ·
      refine ⟨634290527775271570328801339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422860351850181046885867559 634290527775271570328801339)
      ·
        refine ⟨951435791662907355493202009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634290527775271570328801339 951435791662907355493202009)
        ·
          refine ⟨713576843747180516619901507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951435791662907355493202009 713576843747180516619901507)
          ·
            refine ⟨1070365265620770774929852261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713576843747180516619901507 1070365265620770774929852261)
            ·
              refine ⟨200693487303894520299347299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1070365265620770774929852261 200693487303894520299347299)
              ·
                refine ⟨301040230955841780449020949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200693487303894520299347299 301040230955841780449020949)
                ·
                  refine ⟨14111260826055083458547857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 301040230955841780449020949 14111260826055083458547857)
                  ·
                    refine ⟨10583445619541312593910893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14111260826055083458547857 10583445619541312593910893)
                    ·
                      refine ⟨3968792107327992222716585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10583445619541312593910893 3968792107327992222716585)
                      ·
                        rfl

theorem cell23_7729195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 3].length) (baseStart_7729195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729195 prefixEnd_7729195 := by exact prefixLift 7729195
  have htrace : WordTrace (prefixWord ++ tailWord_7729195) baseStart_7729195 baseEnd_7729195 := by
    simpa [prefixWord, tailWord_7729195, baseEnd_7729195] using wordTrace_append hprefix tailTrace_7729195
  have hstable : (prefixWord ++ tailWord_7729195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729195).length < 2 ^ (prefixWord ++ tailWord_7729195).sum := by decide
  have hdescent : baseEnd_7729195 < baseStart_7729195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729202 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_7729202 : Nat := 118140960795 + 7729202 * 2 ^ 59
def prefixEnd_7729202 : Nat := 4983230072969 + 3 ^ 40 * 7729202 * 2
def baseEnd_7729202 : Nat := 1322931900564191231776351

theorem tailTrace_7729202 : CollatzResearch.WordTrace tailWord_7729202 prefixEnd_7729202 1322931900564191231776351 := by
  unfold tailWord_7729202
  simp only [CollatzResearch.WordTrace]
  refine ⟨70476789136107167863187465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187938104362952447635166573 70476789136107167863187465)
  ·
    refine ⟨52857591852080375897390599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70476789136107167863187465 52857591852080375897390599)
    ·
      refine ⟨79286387778120563846085899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52857591852080375897390599 79286387778120563846085899)
      ·
        refine ⟨118929581667180845769128849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79286387778120563846085899 118929581667180845769128849)
        ·
          refine ⟨89197186250385634326846637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118929581667180845769128849 89197186250385634326846637)
          ·
            refine ⟨33448944843894612872567489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89197186250385634326846637 33448944843894612872567489)
            ·
              refine ⟨25086708632920959654425617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33448944843894612872567489 25086708632920959654425617)
              ·
                refine ⟨18815031474690719740819213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25086708632920959654425617 18815031474690719740819213)
                ·
                  refine ⟨7055636803009019902807205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18815031474690719740819213 7055636803009019902807205)
                  ·
                    refine ⟨1322931900564191231776351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7055636803009019902807205 1322931900564191231776351)
                    ·
                      rfl

theorem cell23_7729202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_7729202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729202 prefixEnd_7729202 := by exact prefixLift 7729202
  have htrace : WordTrace (prefixWord ++ tailWord_7729202) baseStart_7729202 baseEnd_7729202 := by
    simpa [prefixWord, tailWord_7729202, baseEnd_7729202] using wordTrace_append hprefix tailTrace_7729202
  have hstable : (prefixWord ++ tailWord_7729202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729202).length < 2 ^ (prefixWord ++ tailWord_7729202).sum := by decide
  have hdescent : baseEnd_7729202 < baseStart_7729202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729212 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_7729212 : Nat := 118140960795 + 7729212 * 2 ^ 59
def prefixEnd_7729212 : Nat := 4983230072969 + 3 ^ 40 * 7729212 * 2
def baseEnd_7729212 : Nat := 3968800836499118656204007

theorem tailTrace_7729212 : CollatzResearch.WordTrace tailWord_7729212 prefixEnd_7729212 3968800836499118656204007 := by
  unfold tailWord_7729212
  simp only [CollatzResearch.WordTrace]
  refine ⟨140953760637196221580306945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187938347516261628773742593 140953760637196221580306945)
  ·
    refine ⟨105715320477897166185230209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140953760637196221580306945 105715320477897166185230209)
    ·
      refine ⟨79286490358422874638922657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105715320477897166185230209 79286490358422874638922657)
      ·
        refine ⟨59464867768817155979191993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79286490358422874638922657 59464867768817155979191993)
        ·
          refine ⟨44598650826612866984393995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59464867768817155979191993 44598650826612866984393995)
          ·
            refine ⟨66897976239919300476590993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44598650826612866984393995 66897976239919300476590993)
            ·
              refine ⟨50173482179939475357443245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66897976239919300476590993 50173482179939475357443245)
              ·
                refine ⟨18815055817477303259041217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50173482179939475357443245 18815055817477303259041217)
                ·
                  refine ⟨14111291863107977444280913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18815055817477303259041217 14111291863107977444280913)
                  ·
                    refine ⟨10583468897330983083210685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14111291863107977444280913 10583468897330983083210685)
                    ·
                      refine ⟨3968800836499118656204007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10583468897330983083210685 3968800836499118656204007)
                      ·
                        rfl

theorem cell23_7729212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_7729212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729212 prefixEnd_7729212 := by exact prefixLift 7729212
  have htrace : WordTrace (prefixWord ++ tailWord_7729212) baseStart_7729212 baseEnd_7729212 := by
    simpa [prefixWord, tailWord_7729212, baseEnd_7729212] using wordTrace_append hprefix tailTrace_7729212
  have hstable : (prefixWord ++ tailWord_7729212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729212).length < 2 ^ (prefixWord ++ tailWord_7729212).sum := by decide
  have hdescent : baseEnd_7729212 < baseStart_7729212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729229 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_7729229 : Nat := 118140960795 + 7729229 * 2 ^ 59
def prefixEnd_7729229 : Nat := 4983230072969 + 3 ^ 40 * 7729229 * 2
def baseEnd_7729229 : Nat := 3968809565670245089691429

theorem tailTrace_7729229 : CollatzResearch.WordTrace tailWord_7729229 prefixEnd_7729229 3968809565670245089691429 := by
  unfold tailWord_7729229
  simp only [CollatzResearch.WordTrace]
  refine ⟨281908141315330855063982741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187938760876887236709321827 281908141315330855063982741)
  ·
    refine ⟨13214444124156133831124191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 281908141315330855063982741 13214444124156133831124191)
    ·
      refine ⟨19821666186234200746686287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13214444124156133831124191 19821666186234200746686287)
      ·
        refine ⟨29732499279351301120029431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19821666186234200746686287 29732499279351301120029431)
        ·
          refine ⟨44598748919026951680044147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29732499279351301120029431 44598748919026951680044147)
          ·
            refine ⟨66898123378540427520066221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44598748919026951680044147 66898123378540427520066221)
            ·
              refine ⟨25086796266952660320024833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66898123378540427520066221 25086796266952660320024833)
              ·
                refine ⟨18815097200214495240018625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25086796266952660320024833 18815097200214495240018625)
                ·
                  refine ⟨14111322900160871430013969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18815097200214495240018625 14111322900160871430013969)
                  ·
                    refine ⟨10583492175120653572510477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14111322900160871430013969 10583492175120653572510477)
                    ·
                      refine ⟨3968809565670245089691429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10583492175120653572510477 3968809565670245089691429)
                      ·
                        rfl

theorem cell23_7729229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_7729229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729229 prefixEnd_7729229 := by exact prefixLift 7729229
  have htrace : WordTrace (prefixWord ++ tailWord_7729229) baseStart_7729229 baseEnd_7729229 := by
    simpa [prefixWord, tailWord_7729229, baseEnd_7729229] using wordTrace_append hprefix tailTrace_7729229
  have hstable : (prefixWord ++ tailWord_7729229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729229).length < 2 ^ (prefixWord ++ tailWord_7729229).sum := by decide
  have hdescent : baseEnd_7729229 < baseStart_7729229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729252 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 3, 5, 2]
def baseStart_7729252 : Nat := 118140960795 + 7729252 * 2 ^ 59
def prefixEnd_7729252 : Nat := 4983230072969 + 3 ^ 40 * 7729252 * 2
def baseEnd_7729252 : Nat := 3968821375725298499703823

theorem tailTrace_7729252 : CollatzResearch.WordTrace tailWord_7729252 prefixEnd_7729252 3968821375725298499703823 := by
  unfold tailWord_7729252
  simp only [CollatzResearch.WordTrace]
  refine ⟨140954490097123764996035005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187939320129498353328046673 140954490097123764996035005)
  ·
    refine ⟨52857933786421411873513127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140954490097123764996035005 52857933786421411873513127)
    ·
      refine ⟨79286900679632117810269691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52857933786421411873513127 79286900679632117810269691)
      ·
        refine ⟨118930351019448176715404537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79286900679632117810269691 118930351019448176715404537)
        ·
          refine ⟨89197763264586132536553403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118930351019448176715404537 89197763264586132536553403)
          ·
            refine ⟨133796644896879198804830105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89197763264586132536553403 133796644896879198804830105)
            ·
              refine ⟨100347483672659399103622579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133796644896879198804830105 100347483672659399103622579)
              ·
                refine ⟨150521225508989098655433869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100347483672659399103622579 150521225508989098655433869)
                ·
                  refine ⟨56445459565870911995787701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150521225508989098655433869 56445459565870911995787701)
                  ·
                    refine ⟨5291761834300397999605097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56445459565870911995787701 5291761834300397999605097)
                    ·
                      refine ⟨3968821375725298499703823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5291761834300397999605097 3968821375725298499703823)
                      ·
                        rfl

theorem cell23_7729252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_7729252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729252 prefixEnd_7729252 := by exact prefixLift 7729252
  have htrace : WordTrace (prefixWord ++ tailWord_7729252) baseStart_7729252 baseEnd_7729252 := by
    simpa [prefixWord, tailWord_7729252, baseEnd_7729252] using wordTrace_append hprefix tailTrace_7729252
  have hstable : (prefixWord ++ tailWord_7729252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729252).length < 2 ^ (prefixWord ++ tailWord_7729252).sum := by decide
  have hdescent : baseEnd_7729252 < baseStart_7729252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729262 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_7729262 : Nat := 118140960795 + 7729262 * 2 ^ 59
def prefixEnd_7729262 : Nat := 4983230072969 + 3 ^ 40 * 7729262 * 2
def baseEnd_7729262 : Nat := 1322942170177281153526259

theorem tailTrace_7729262 : CollatzResearch.WordTrace tailWord_7729262 prefixEnd_7729262 1322942170177281153526259 := by
  unfold tailWord_7729262
  simp only [CollatzResearch.WordTrace]
  refine ⟨35238668115526412712491755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187939563282807534466622693 35238668115526412712491755)
  ·
    refine ⟨52858002173289619068737633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35238668115526412712491755 52858002173289619068737633)
    ·
      refine ⟨39643501629967214301553225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52858002173289619068737633 39643501629967214301553225)
      ·
        refine ⟨29732626222475410726164919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39643501629967214301553225 29732626222475410726164919)
        ·
          refine ⟨44598939333713116089247379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29732626222475410726164919 44598939333713116089247379)
          ·
            refine ⟨66898409000569674133871069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44598939333713116089247379 66898409000569674133871069)
            ·
              refine ⟨25086903375213627800201651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66898409000569674133871069 25086903375213627800201651)
              ·
                refine ⟨37630355062820441700302477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25086903375213627800201651 37630355062820441700302477)
                ·
                  refine ⟨14111383148557665637613429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37630355062820441700302477 14111383148557665637613429)
                  ·
                    refine ⟨1322942170177281153526259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14111383148557665637613429 1322942170177281153526259)
                    ·
                      rfl

theorem cell23_7729262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_7729262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729262 prefixEnd_7729262 := by exact prefixLift 7729262
  have htrace : WordTrace (prefixWord ++ tailWord_7729262) baseStart_7729262 baseEnd_7729262 := by
    simpa [prefixWord, tailWord_7729262, baseEnd_7729262] using wordTrace_append hprefix tailTrace_7729262
  have hstable : (prefixWord ++ tailWord_7729262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729262).length < 2 ^ (prefixWord ++ tailWord_7729262).sum := by decide
  have hdescent : baseEnd_7729262 < baseStart_7729262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729299 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 3, 2, 2]
def baseStart_7729299 : Nat := 118140960795 + 7729299 * 2 ^ 59
def prefixEnd_7729299 : Nat := 4983230072969 + 3 ^ 40 * 7729299 * 2
def baseEnd_7729299 : Nat := 3968845509316059815816107

theorem tailTrace_7729299 : CollatzResearch.WordTrace tailWord_7729299 prefixEnd_7729299 3968845509316059815816107 := by
  unfold tailWord_7729299
  simp only [CollatzResearch.WordTrace]
  refine ⟨281910694425077257019030951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187940462950051504679353967 281910694425077257019030951)
  ·
    refine ⟨422866041637615885528546427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281910694425077257019030951 422866041637615885528546427)
    ·
      refine ⟨634299062456423828292819641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422866041637615885528546427 634299062456423828292819641)
      ·
        refine ⟨475724296842317871219614731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634299062456423828292819641 475724296842317871219614731)
        ·
          refine ⟨713586445263476806829422097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475724296842317871219614731 713586445263476806829422097)
          ·
            refine ⟨535189833947607605122066573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713586445263476806829422097 535189833947607605122066573)
            ·
              refine ⟨200696187730352851920774965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 535189833947607605122066573 200696187730352851920774965)
              ·
                refine ⟨18815267599720579867572653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200696187730352851920774965 18815267599720579867572653)
                ·
                  refine ⟨7055725349895217450339745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18815267599720579867572653 7055725349895217450339745)
                  ·
                    refine ⟨5291794012421413087754809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7055725349895217450339745 5291794012421413087754809)
                    ·
                      refine ⟨3968845509316059815816107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5291794012421413087754809 3968845509316059815816107)
                      ·
                        rfl

theorem cell23_7729299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 2, 2].length) (baseStart_7729299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729299 prefixEnd_7729299 := by exact prefixLift 7729299
  have htrace : WordTrace (prefixWord ++ tailWord_7729299) baseStart_7729299 baseEnd_7729299 := by
    simpa [prefixWord, tailWord_7729299, baseEnd_7729299] using wordTrace_append hprefix tailTrace_7729299
  have hstable : (prefixWord ++ tailWord_7729299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729299).length < 2 ^ (prefixWord ++ tailWord_7729299).sum := by decide
  have hdescent : baseEnd_7729299 < baseStart_7729299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729309 : List Nat := [1, 4, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_7729309 : Nat := 118140960795 + 7729309 * 2 ^ 59
def prefixEnd_7729309 : Nat := 4983230072969 + 3 ^ 40 * 7729309 * 2
def baseEnd_7729309 : Nat := 1322950214707534925563687

theorem tailTrace_7729309 : CollatzResearch.WordTrace tailWord_7729309 prefixEnd_7729309 1322950214707534925563687 := by
  unfold tailWord_7729309
  simp only [CollatzResearch.WordTrace]
  refine ⟨281911059155041028726894981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187940706103360685817929987 281911059155041028726894981)
  ·
    refine ⟨52858323591570192886292809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281911059155041028726894981 52858323591570192886292809)
    ·
      refine ⟨39643742693677644664719607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52858323591570192886292809 39643742693677644664719607)
      ·
        refine ⟨59465614040516466997079411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39643742693677644664719607 59465614040516466997079411)
        ·
          refine ⟨89198421060774700495619117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59465614040516466997079411 89198421060774700495619117)
          ·
            refine ⟨33449407897790512685857169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89198421060774700495619117 33449407897790512685857169)
            ·
              refine ⟨25087055923342884514392877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33449407897790512685857169 25087055923342884514392877)
              ·
                refine ⟨9407645971253581692897329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25087055923342884514392877 9407645971253581692897329)
                ·
                  refine ⟨7055734478440186269672997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9407645971253581692897329 7055734478440186269672997)
                  ·
                    refine ⟨1322950214707534925563687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7055734478440186269672997 1322950214707534925563687)
                    ·
                      rfl

theorem cell23_7729309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_7729309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729309 prefixEnd_7729309 := by exact prefixLift 7729309
  have htrace : WordTrace (prefixWord ++ tailWord_7729309) baseStart_7729309 baseEnd_7729309 := by
    simpa [prefixWord, tailWord_7729309, baseEnd_7729309] using wordTrace_append hprefix tailTrace_7729309
  have hstable : (prefixWord ++ tailWord_7729309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729309).length < 2 ^ (prefixWord ++ tailWord_7729309).sum := by decide
  have hdescent : baseEnd_7729309 < baseStart_7729309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729312 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 4]
def baseStart_7729312 : Nat := 118140960795 + 7729312 * 2 ^ 59
def prefixEnd_7729312 : Nat := 4983230072969 + 3 ^ 40 * 7729312 * 2
def baseEnd_7729312 : Nat := 3968852184564568264953547

theorem tailTrace_7729312 : CollatzResearch.WordTrace tailWord_7729312 prefixEnd_7729312 3968852184564568264953547 := by
  unfold tailWord_7729312
  simp only [CollatzResearch.WordTrace]
  refine ⟨140955584287015080119627095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187940779049353440159502793 140955584287015080119627095)
  ·
    refine ⟨211433376430522620179440643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140955584287015080119627095 211433376430522620179440643)
    ·
      refine ⟨317150064645783930269160965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211433376430522620179440643 317150064645783930269160965)
      ·
        refine ⟨59465637121084486925467681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317150064645783930269160965 59465637121084486925467681)
        ·
          refine ⟨44599227840813365194100761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59465637121084486925467681 44599227840813365194100761)
          ·
            refine ⟨33449420880610023895575571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44599227840813365194100761 33449420880610023895575571)
            ·
              refine ⟨50174131320915035843363357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33449420880610023895575571 50174131320915035843363357)
              ·
                refine ⟨18815299245343138441261259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50174131320915035843363357 18815299245343138441261259)
                ·
                  refine ⟨28222948868014707661891889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18815299245343138441261259 28222948868014707661891889)
                  ·
                    refine ⟨21167211651011030746418917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28222948868014707661891889 21167211651011030746418917)
                    ·
                      refine ⟨3968852184564568264953547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21167211651011030746418917 3968852184564568264953547)
                      ·
                        rfl

theorem cell23_7729312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_7729312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729312 prefixEnd_7729312 := by exact prefixLift 7729312
  have htrace : WordTrace (prefixWord ++ tailWord_7729312) baseStart_7729312 baseEnd_7729312 := by
    simpa [prefixWord, tailWord_7729312, baseEnd_7729312] using wordTrace_append hprefix tailTrace_7729312
  have hstable : (prefixWord ++ tailWord_7729312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729312).length < 2 ^ (prefixWord ++ tailWord_7729312).sum := by decide
  have hdescent : baseEnd_7729312 < baseStart_7729312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729376 : List Nat := [2, 1, 1, 3, 1, 3, 4, 2, 1, 3, 2]
def baseStart_7729376 : Nat := 118140960795 + 7729376 * 2 ^ 59
def prefixEnd_7729376 : Nat := 4983230072969 + 3 ^ 40 * 7729376 * 2
def baseEnd_7729376 : Nat := 3968885047326456014553253

theorem tailTrace_7729376 : CollatzResearch.WordTrace tailWord_7729376 prefixEnd_7729376 3968885047326456014553253 := by
  unfold tailWord_7729376
  simp only [CollatzResearch.WordTrace]
  refine ⟨140956751422899149584791991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187942335230532199446389321 140956751422899149584791991)
  ·
    refine ⟨211435127134348724377187987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140956751422899149584791991 211435127134348724377187987)
    ·
      refine ⟨317152690701523086565781981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211435127134348724377187987 317152690701523086565781981)
      ·
        refine ⟨118932259013071157462168243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317152690701523086565781981 118932259013071157462168243)
        ·
          refine ⟨178398388519606736193252365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118932259013071157462168243 178398388519606736193252365)
          ·
            refine ⟨66899395694852526072469637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178398388519606736193252365 66899395694852526072469637)
            ·
              refine ⟨12543636692784848638588057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66899395694852526072469637 12543636692784848638588057)
              ·
                refine ⟨9407727519588636478941043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12543636692784848638588057 9407727519588636478941043)
                ·
                  refine ⟨14111591279382954718411565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9407727519588636478941043 14111591279382954718411565)
                  ·
                    refine ⟨5291846729768608019404337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14111591279382954718411565 5291846729768608019404337)
                    ·
                      refine ⟨3968885047326456014553253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5291846729768608019404337 3968885047326456014553253)
                      ·
                        rfl

theorem cell23_7729376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_7729376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729376 prefixEnd_7729376 := by exact prefixLift 7729376
  have htrace : WordTrace (prefixWord ++ tailWord_7729376) baseStart_7729376 baseEnd_7729376 := by
    simpa [prefixWord, tailWord_7729376, baseEnd_7729376] using wordTrace_append hprefix tailTrace_7729376
  have hstable : (prefixWord ++ tailWord_7729376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729376).length < 2 ^ (prefixWord ++ tailWord_7729376).sum := by decide
  have hdescent : baseEnd_7729376 < baseStart_7729376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729452 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_7729452 : Nat := 118140960795 + 7729452 * 2 ^ 59
def prefixEnd_7729452 : Nat := 4983230072969 + 3 ^ 40 * 7729452 * 2
def baseEnd_7729452 : Nat := 3968924071856197717202903

theorem tailTrace_7729452 : CollatzResearch.WordTrace tailWord_7729452 prefixEnd_7729452 3968924071856197717202903 := by
  unfold tailWord_7729452
  simp only [CollatzResearch.WordTrace]
  refine ⟨140958137396761482074675305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187944183195681976099567073 140958137396761482074675305)
  ·
    refine ⟨105718603047571111556006479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140958137396761482074675305 105718603047571111556006479)
    ·
      refine ⟨158577904571356667334009719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105718603047571111556006479 158577904571356667334009719)
      ·
        refine ⟨237866856857035001001014579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158577904571356667334009719 237866856857035001001014579)
        ·
          refine ⟨356800285285552501501521869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237866856857035001001014579 356800285285552501501521869)
          ·
            refine ⟨133800106982082188063070701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356800285285552501501521869 133800106982082188063070701)
            ·
              refine ⟨50175040118280820523651513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133800106982082188063070701 50175040118280820523651513)
              ·
                refine ⟨37631280088710615392738635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50175040118280820523651513 37631280088710615392738635)
                ·
                  refine ⟨56446920133065923089107953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37631280088710615392738635 56446920133065923089107953)
                  ·
                    refine ⟨42335190099799442316830965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56446920133065923089107953 42335190099799442316830965)
                    ·
                      refine ⟨3968924071856197717202903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42335190099799442316830965 3968924071856197717202903)
                      ·
                        rfl

theorem cell23_7729452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_7729452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729452 prefixEnd_7729452 := by exact prefixLift 7729452
  have htrace : WordTrace (prefixWord ++ tailWord_7729452) baseStart_7729452 baseEnd_7729452 := by
    simpa [prefixWord, tailWord_7729452, baseEnd_7729452] using wordTrace_append hprefix tailTrace_7729452
  have hstable : (prefixWord ++ tailWord_7729452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729452).length < 2 ^ (prefixWord ++ tailWord_7729452).sum := by decide
  have hdescent : baseEnd_7729452 < baseStart_7729452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729489 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 5, 4]
def baseStart_7729489 : Nat := 118140960795 + 7729489 * 2 ^ 59
def prefixEnd_7729489 : Nat := 4983230072969 + 3 ^ 40 * 7729489 * 2
def baseEnd_7729489 : Nat := 1322981023546804690813411

theorem tailTrace_7729489 : CollatzResearch.WordTrace tailWord_7729489 prefixEnd_7729489 1322981023546804690813411 := by
  unfold tailWord_7729489
  simp only [CollatzResearch.WordTrace]
  refine ⟨281917624294388919468447521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187945082862925946312298347 281917624294388919468447521)
  ·
    refine ⟨211438218220791689601335641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281917624294388919468447521 211438218220791689601335641)
    ·
      refine ⟨158578663665593767201001731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211438218220791689601335641 158578663665593767201001731)
      ·
        refine ⟨237867995498390650801502597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158578663665593767201001731 237867995498390650801502597)
        ·
          refine ⟨44600249155948247025281737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237867995498390650801502597 44600249155948247025281737)
          ·
            refine ⟨33450186866961185268961303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44600249155948247025281737 33450186866961185268961303)
            ·
              refine ⟨50175280300441777903441955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33450186866961185268961303 50175280300441777903441955)
              ·
                refine ⟨75262920450662666855162933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50175280300441777903441955 75262920450662666855162933)
                ·
                  refine ⟨7055898792249625017671525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75262920450662666855162933 7055898792249625017671525)
                  ·
                    refine ⟨1322981023546804690813411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7055898792249625017671525 1322981023546804690813411)
                    ·
                      rfl

theorem cell23_7729489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_7729489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729489 prefixEnd_7729489 := by exact prefixLift 7729489
  have htrace : WordTrace (prefixWord ++ tailWord_7729489) baseStart_7729489 baseEnd_7729489 := by
    simpa [prefixWord, tailWord_7729489, baseEnd_7729489] using wordTrace_append hprefix tailTrace_7729489
  have hstable : (prefixWord ++ tailWord_7729489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729489).length < 2 ^ (prefixWord ++ tailWord_7729489).sum := by decide
  have hdescent : baseEnd_7729489 < baseStart_7729489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729493 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 2, 5]
def baseStart_7729493 : Nat := 118140960795 + 7729493 * 2 ^ 59
def prefixEnd_7729493 : Nat := 4983230072969 + 3 ^ 40 * 7729493 * 2
def baseEnd_7729493 : Nat := 1322981708187677352263405

theorem tailTrace_7729493 : CollatzResearch.WordTrace tailWord_7729493 prefixEnd_7729493 1322981708187677352263405 := by
  unfold tailWord_7729493
  simp only [CollatzResearch.WordTrace]
  refine ⟨281917770186374428151593133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187945180124249618767728755 281917770186374428151593133)
  ·
    refine ⟨105719163819890410556847425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281917770186374428151593133 105719163819890410556847425)
    ·
      refine ⟨79289372864917807917635569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105719163819890410556847425 79289372864917807917635569)
      ·
        refine ⟨59467029648688355938226677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79289372864917807917635569 59467029648688355938226677)
        ·
          refine ⟨5575034029564533369208751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59467029648688355938226677 5575034029564533369208751)
          ·
            refine ⟨8362551044346800053813127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5575034029564533369208751 8362551044346800053813127)
            ·
              refine ⟨12543826566520200080719691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8362551044346800053813127 12543826566520200080719691)
              ·
                refine ⟨18815739849780300121079537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12543826566520200080719691 18815739849780300121079537)
                ·
                  refine ⟨14111804887335225090809653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18815739849780300121079537 14111804887335225090809653)
                  ·
                    refine ⟨1322981708187677352263405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14111804887335225090809653 1322981708187677352263405)
                    ·
                      rfl

theorem cell23_7729493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_7729493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729493 prefixEnd_7729493 := by exact prefixLift 7729493
  have htrace : WordTrace (prefixWord ++ tailWord_7729493) baseStart_7729493 baseEnd_7729493 := by
    simpa [prefixWord, tailWord_7729493, baseEnd_7729493] using wordTrace_append hprefix tailTrace_7729493
  have hstable : (prefixWord ++ tailWord_7729493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729493).length < 2 ^ (prefixWord ++ tailWord_7729493).sum := by decide
  have hdescent : baseEnd_7729493 < baseStart_7729493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729532 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 2, 9]
def baseStart_7729532 : Nat := 118140960795 + 7729532 * 2 ^ 59
def prefixEnd_7729532 : Nat := 4983230072969 + 3 ^ 40 * 7729532 * 2
def baseEnd_7729532 : Nat := 1322988383436185801400845

theorem tailTrace_7729532 : CollatzResearch.WordTrace tailWord_7729532 prefixEnd_7729532 1322988383436185801400845 := by
  unfold tailWord_7729532
  simp only [CollatzResearch.WordTrace]
  refine ⟨140959596316616568906131425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187946128422155425208175233 140959596316616568906131425)
  ·
    refine ⟨105719697237462426679598569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140959596316616568906131425 105719697237462426679598569)
    ·
      refine ⟨79289772928096820009698927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105719697237462426679598569 79289772928096820009698927)
      ·
        refine ⟨118934659392145230014548391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79289772928096820009698927 118934659392145230014548391)
        ·
          refine ⟨178401989088217845021822587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118934659392145230014548391 178401989088217845021822587)
          ·
            refine ⟨267602983632326767532733881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178401989088217845021822587 267602983632326767532733881)
            ·
              refine ⟨200702237724245075649550411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267602983632326767532733881 200702237724245075649550411)
              ·
                refine ⟨301053356586367613474325617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200702237724245075649550411 301053356586367613474325617)
                ·
                  refine ⟨225790017439775710105744213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301053356586367613474325617 225790017439775710105744213)
                  ·
                    refine ⟨1322988383436185801400845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 225790017439775710105744213 1322988383436185801400845)
                    ·
                      rfl

theorem cell23_7729532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_7729532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729532 prefixEnd_7729532 := by exact prefixLift 7729532
  have htrace : WordTrace (prefixWord ++ tailWord_7729532) baseStart_7729532 baseEnd_7729532 := by
    simpa [prefixWord, tailWord_7729532, baseEnd_7729532] using wordTrace_append hprefix tailTrace_7729532
  have hstable : (prefixWord ++ tailWord_7729532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729532).length < 2 ^ (prefixWord ++ tailWord_7729532).sum := by decide
  have hdescent : baseEnd_7729532 < baseStart_7729532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729620 : List Nat := [2, 4, 1, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_7729620 : Nat := 118140960795 + 7729620 * 2 ^ 59
def prefixEnd_7729620 : Nat := 4983230072969 + 3 ^ 40 * 7729620 * 2
def baseEnd_7729620 : Nat := 3969010336606153059902131

theorem tailTrace_7729620 : CollatzResearch.WordTrace tailWord_7729620 prefixEnd_7729620 3969010336606153059902131 := by
  unfold tailWord_7729620
  simp only [CollatzResearch.WordTrace]
  refine ⟨140961201128457164420733157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187948268171276219227644209 140961201128457164420733157)
  ·
    refine ⟨26430225211585718328887467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140961201128457164420733157 26430225211585718328887467)
    ·
      refine ⟨39645337817378577493331201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26430225211585718328887467 39645337817378577493331201)
      ·
        refine ⟨29734003363033933119998401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39645337817378577493331201 29734003363033933119998401)
        ·
          refine ⟨22300502522275449839998801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29734003363033933119998401 22300502522275449839998801)
          ·
            refine ⟨16725376891706587379999101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22300502522275449839998801 16725376891706587379999101)
            ·
              refine ⟨6272016334389970267499663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16725376891706587379999101 6272016334389970267499663)
              ·
                refine ⟨9408024501584955401249495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6272016334389970267499663 9408024501584955401249495)
                ·
                  refine ⟨14112036752377433101874243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9408024501584955401249495 14112036752377433101874243)
                  ·
                    refine ⟨21168055128566149652811365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14112036752377433101874243 21168055128566149652811365)
                    ·
                      refine ⟨3969010336606153059902131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21168055128566149652811365 3969010336606153059902131)
                      ·
                        rfl

theorem cell23_7729620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_7729620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729620 prefixEnd_7729620 := by exact prefixLift 7729620
  have htrace : WordTrace (prefixWord ++ tailWord_7729620) baseStart_7729620 baseEnd_7729620 := by
    simpa [prefixWord, tailWord_7729620, baseEnd_7729620] using wordTrace_append hprefix tailTrace_7729620
  have hstable : (prefixWord ++ tailWord_7729620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729620).length < 2 ^ (prefixWord ++ tailWord_7729620).sum := by decide
  have hdescent : baseEnd_7729620 < baseStart_7729620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729639 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 1, 9]
def baseStart_7729639 : Nat := 118140960795 + 7729639 * 2 ^ 59
def prefixEnd_7729639 : Nat := 4983230072969 + 3 ^ 40 * 7729639 * 2
def baseEnd_7729639 : Nat := 1323006697579529495188181

theorem tailTrace_7729639 : CollatzResearch.WordTrace tailWord_7729639 prefixEnd_7729639 1323006697579529495188181 := by
  unfold tailWord_7729639
  simp only [CollatzResearch.WordTrace]
  refine ⟨281923095243845495086407971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187948730162563663390938647 281923095243845495086407971)
  ·
    refine ⟨422884642865768242629611957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281923095243845495086407971 422884642865768242629611957)
    ·
      refine ⟨39645435268665772746526121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 422884642865768242629611957 39645435268665772746526121)
      ·
        refine ⟨29734076451499329559894591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39645435268665772746526121 29734076451499329559894591)
        ·
          refine ⟨44601114677248994339841887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29734076451499329559894591 44601114677248994339841887)
          ·
            refine ⟨66901672015873491509762831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44601114677248994339841887 66901672015873491509762831)
            ·
              refine ⟨100352508023810237264644247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66901672015873491509762831 100352508023810237264644247)
              ·
                refine ⟨150528762035715355896966371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100352508023810237264644247 150528762035715355896966371)
                ·
                  refine ⟨225793143053573033845449557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150528762035715355896966371 225793143053573033845449557)
                  ·
                    refine ⟨1323006697579529495188181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 225793143053573033845449557 1323006697579529495188181)
                    ·
                      rfl

theorem cell23_7729639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_7729639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729639 prefixEnd_7729639 := by exact prefixLift 7729639
  have htrace : WordTrace (prefixWord ++ tailWord_7729639) baseStart_7729639 baseEnd_7729639 := by
    simpa [prefixWord, tailWord_7729639, baseEnd_7729639] using wordTrace_append hprefix tailTrace_7729639
  have hstable : (prefixWord ++ tailWord_7729639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729639).length < 2 ^ (prefixWord ++ tailWord_7729639).sum := by decide
  have hdescent : baseEnd_7729639 < baseStart_7729639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729663 : List Nat := [1, 1, 2, 2, 1, 2, 4, 4, 1, 3, 2]
def baseStart_7729663 : Nat := 118140960795 + 7729663 * 2 ^ 59
def prefixEnd_7729663 : Nat := 4983230072969 + 3 ^ 40 * 7729663 * 2
def baseEnd_7729663 : Nat := 3969032416274296391664433

theorem tailTrace_7729663 : CollatzResearch.WordTrace tailWord_7729663 prefixEnd_7729663 3969032416274296391664433 := by
  unfold tailWord_7729663
  simp only [CollatzResearch.WordTrace]
  refine ⟨281923970595758547185281643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187949313730505698123521095 281923970595758547185281643)
  ·
    refine ⟨422885955893637820777922465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281923970595758547185281643 422885955893637820777922465)
    ·
      refine ⟨317164466920228365583441849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422885955893637820777922465 317164466920228365583441849)
      ·
        refine ⟨237873350190171274187581387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317164466920228365583441849 237873350190171274187581387)
        ·
          refine ⟨356810025285256911281372081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237873350190171274187581387 356810025285256911281372081)
          ·
            refine ⟨267607518963942683461029061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356810025285256911281372081 267607518963942683461029061)
            ·
              refine ⟨50176409805739253148942949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267607518963942683461029061 50176409805739253148942949)
              ·
                refine ⟨9408076838576109965426803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50176409805739253148942949 9408076838576109965426803)
                ·
                  refine ⟨14112115257864164948140205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9408076838576109965426803 14112115257864164948140205)
                  ·
                    refine ⟨5292043221699061855552577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14112115257864164948140205 5292043221699061855552577)
                    ·
                      refine ⟨3969032416274296391664433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5292043221699061855552577 3969032416274296391664433)
                      ·
                        rfl

theorem cell23_7729663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 3, 2].length) (baseStart_7729663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729663 prefixEnd_7729663 := by exact prefixLift 7729663
  have htrace : WordTrace (prefixWord ++ tailWord_7729663) baseStart_7729663 baseEnd_7729663 := by
    simpa [prefixWord, tailWord_7729663, baseEnd_7729663] using wordTrace_append hprefix tailTrace_7729663
  have hstable : (prefixWord ++ tailWord_7729663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729663).length < 2 ^ (prefixWord ++ tailWord_7729663).sum := by decide
  have hdescent : baseEnd_7729663 < baseStart_7729663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729689 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 3, 4, 4]
def baseStart_7729689 : Nat := 118140960795 + 7729689 * 2 ^ 59
def prefixEnd_7729689 : Nat := 4983230072969 + 3 ^ 40 * 7729689 * 2
def baseEnd_7729689 : Nat := 3969045766771313289939313

theorem tailTrace_7729689 : CollatzResearch.WordTrace tailWord_7729689 prefixEnd_7729689 3969045766771313289939313 := by
  unfold tailWord_7729689
  simp only [CollatzResearch.WordTrace]
  refine ⟨281924918893664353625728121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187949945929109569083818747 281924918893664353625728121)
  ·
    refine ⟨211443689170248265219296091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281924918893664353625728121 211443689170248265219296091)
    ·
      refine ⟨317165533755372397828944137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211443689170248265219296091 317165533755372397828944137)
      ·
        refine ⟨237874150316529298371708103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317165533755372397828944137 237874150316529298371708103)
        ·
          refine ⟨356811225474793947557562155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237874150316529298371708103 356811225474793947557562155)
          ·
            refine ⟨535216838212190921336343233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356811225474793947557562155 535216838212190921336343233)
            ·
              refine ⟨401412628659143191002257425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535216838212190921336343233 401412628659143191002257425)
              ·
                refine ⟨301059471494357393251693069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401412628659143191002257425 301059471494357393251693069)
                ·
                  refine ⟨112897301810384022469384901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301059471494357393251693069 112897301810384022469384901)
                  ·
                    refine ⟨21168244089447004213009669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112897301810384022469384901 21168244089447004213009669)
                    ·
                      refine ⟨3969045766771313289939313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21168244089447004213009669 3969045766771313289939313)
                      ·
                        rfl

theorem cell23_7729689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_7729689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729689 prefixEnd_7729689 := by exact prefixLift 7729689
  have htrace : WordTrace (prefixWord ++ tailWord_7729689) baseStart_7729689 baseEnd_7729689 := by
    simpa [prefixWord, tailWord_7729689, baseEnd_7729689] using wordTrace_append hprefix tailTrace_7729689
  have hstable : (prefixWord ++ tailWord_7729689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729689).length < 2 ^ (prefixWord ++ tailWord_7729689).sum := by decide
  have hdescent : baseEnd_7729689 < baseStart_7729689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729733 : List Nat := [1, 3, 1, 1, 1, 5, 3, 3, 5]
def baseStart_7729733 : Nat := 118140960795 + 7729733 * 2 ^ 59
def prefixEnd_7729733 : Nat := 4983230072969 + 3 ^ 40 * 7729733 * 2
def baseEnd_7729733 : Nat := 441007595546679013087679

theorem tailTrace_7729733 : CollatzResearch.WordTrace tailWord_7729733 prefixEnd_7729733 441007595546679013087679 := by
  unfold tailWord_7729733
  simp only [CollatzResearch.WordTrace]
  refine ⟨281926523705504949140329853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187951015803669966093553235 281926523705504949140329853)
  ·
    refine ⟨105722446389564355927623695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281926523705504949140329853 105722446389564355927623695)
    ·
      refine ⟨158583669584346533891435543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105722446389564355927623695 158583669584346533891435543)
      ·
        refine ⟨237875504376519800837153315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158583669584346533891435543 237875504376519800837153315)
        ·
          refine ⟨356813256564779701255729973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237875504376519800837153315 356813256564779701255729973)
          ·
            refine ⟨33451242802948096992724685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 356813256564779701255729973 33451242802948096992724685)
            ·
              refine ⟨12544216051105536372271757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33451242802948096992724685 12544216051105536372271757)
              ·
                refine ⟨4704081019164576139601909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12544216051105536372271757 4704081019164576139601909)
                ·
                  refine ⟨441007595546679013087679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4704081019164576139601909 441007595546679013087679)
                  ·
                    rfl

theorem cell23_7729733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 5].length) (baseStart_7729733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729733 prefixEnd_7729733 := by exact prefixLift 7729733
  have htrace : WordTrace (prefixWord ++ tailWord_7729733) baseStart_7729733 baseEnd_7729733 := by
    simpa [prefixWord, tailWord_7729733, baseEnd_7729733] using wordTrace_append hprefix tailTrace_7729733
  have hstable : (prefixWord ++ tailWord_7729733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729733).length < 2 ^ (prefixWord ++ tailWord_7729733).sum := by decide
  have hdescent : baseEnd_7729733 < baseStart_7729733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729786 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3]
def baseStart_7729786 : Nat := 118140960795 + 7729786 * 2 ^ 59
def prefixEnd_7729786 : Nat := 4983230072969 + 3 ^ 40 * 7729786 * 2
def baseEnd_7729786 : Nat := 3969095574394799410426367

theorem tailTrace_7729786 : CollatzResearch.WordTrace tailWord_7729786 prefixEnd_7729786 3969095574394799410426367 := by
  unfold tailWord_7729786
  simp only [CollatzResearch.WordTrace]
  refine ⟨70482114193578234798002303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187952304516208626128006141 70482114193578234798002303)
  ·
    refine ⟨105723171290367352197003455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70482114193578234798002303 105723171290367352197003455)
    ·
      refine ⟨158584756935551028295505183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105723171290367352197003455 158584756935551028295505183)
      ·
        refine ⟨237877135403326542443257775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158584756935551028295505183 237877135403326542443257775)
        ·
          refine ⟨356815703104989813664886663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237877135403326542443257775 356815703104989813664886663)
          ·
            refine ⟨535223554657484720497329995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356815703104989813664886663 535223554657484720497329995)
            ·
              refine ⟨802835331986227080745994993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535223554657484720497329995 802835331986227080745994993)
              ·
                refine ⟨602126498989670310559496245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802835331986227080745994993 602126498989670310559496245)
                ·
                  refine ⟨56449359280281591614952773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 602126498989670310559496245 56449359280281591614952773)
                  ·
                    refine ⟨10584254865052798427803645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56449359280281591614952773 10584254865052798427803645)
                    ·
                      refine ⟨3969095574394799410426367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10584254865052798427803645 3969095574394799410426367)
                      ·
                        rfl

theorem cell23_7729786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_7729786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729786 prefixEnd_7729786 := by exact prefixLift 7729786
  have htrace : WordTrace (prefixWord ++ tailWord_7729786) baseStart_7729786 baseEnd_7729786 := by
    simpa [prefixWord, tailWord_7729786, baseEnd_7729786] using wordTrace_append hprefix tailTrace_7729786
  have hstable : (prefixWord ++ tailWord_7729786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729786).length < 2 ^ (prefixWord ++ tailWord_7729786).sum := by decide
  have hdescent : baseEnd_7729786 < baseStart_7729786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729833 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 5, 1, 3]
def baseStart_7729833 : Nat := 118140960795 + 7729833 * 2 ^ 59
def prefixEnd_7729833 : Nat := 4983230072969 + 3 ^ 40 * 7729833 * 2
def baseEnd_7729833 : Nat := 3969119707985560726538651

theorem tailTrace_7729833 : CollatzResearch.WordTrace tailWord_7729833 prefixEnd_7729833 3969119707985560726538651 := by
  unfold tailWord_7729833
  simp only [CollatzResearch.WordTrace]
  refine ⟨281930171005142666218970153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187953447336761777479313435 281930171005142666218970153)
  ·
    refine ⟨211447628253856999664227615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281930171005142666218970153 211447628253856999664227615)
    ·
      refine ⟨317171442380785499496341423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211447628253856999664227615 317171442380785499496341423)
      ·
        refine ⟨475757163571178249244512135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317171442380785499496341423 475757163571178249244512135)
        ·
          refine ⟨713635745356767373866768203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475757163571178249244512135 713635745356767373866768203)
          ·
            refine ⟨1070453618035151060800152305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713635745356767373866768203 1070453618035151060800152305)
            ·
              refine ⟨802840213526363295600114229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070453618035151060800152305 802840213526363295600114229)
              ·
                refine ⟨75266270018096558962510709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 802840213526363295600114229 75266270018096558962510709)
                ·
                  refine ⟨7056212814196552402735379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75266270018096558962510709 7056212814196552402735379)
                  ·
                    refine ⟨10584319221294828604103069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7056212814196552402735379 10584319221294828604103069)
                    ·
                      refine ⟨3969119707985560726538651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10584319221294828604103069 3969119707985560726538651)
                      ·
                        rfl

theorem cell23_7729833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 1, 3].length) (baseStart_7729833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729833 prefixEnd_7729833 := by exact prefixLift 7729833
  have htrace : WordTrace (prefixWord ++ tailWord_7729833) baseStart_7729833 baseEnd_7729833 := by
    simpa [prefixWord, tailWord_7729833, baseEnd_7729833] using wordTrace_append hprefix tailTrace_7729833
  have hstable : (prefixWord ++ tailWord_7729833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729833).length < 2 ^ (prefixWord ++ tailWord_7729833).sum := by decide
  have hdescent : baseEnd_7729833 < baseStart_7729833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729834 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_7729834 : Nat := 118140960795 + 7729834 * 2 ^ 59
def prefixEnd_7729834 : Nat := 4983230072969 + 3 ^ 40 * 7729834 * 2
def baseEnd_7729834 : Nat := 3969120221466215222626147

theorem tailTrace_7729834 : CollatzResearch.WordTrace tailWord_7729834 prefixEnd_7729834 3969120221466215222626147 := by
  unfold tailWord_7729834
  simp only [CollatzResearch.WordTrace]
  refine ⟨70482551869534760847439139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187953471652092695593171037 70482551869534760847439139)
  ·
    refine ⟨105723827804302141271158709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70482551869534760847439139 105723827804302141271158709)
    ·
      refine ⟨9911608856653325744171129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105723827804302141271158709 9911608856653325744171129)
      ·
        refine ⟨7433706642489994308128347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9911608856653325744171129 7433706642489994308128347)
        ·
          refine ⟨11150559963734991462192521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7433706642489994308128347 11150559963734991462192521)
          ·
            refine ⟨8362919972801243596644391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11150559963734991462192521 8362919972801243596644391)
            ·
              refine ⟨12544379959201865394966587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8362919972801243596644391 12544379959201865394966587)
              ·
                refine ⟨18816569938802798092449881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12544379959201865394966587 18816569938802798092449881)
                ·
                  refine ⟨14112427454102098569337411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18816569938802798092449881 14112427454102098569337411)
                  ·
                    refine ⟨21168641181153147854006117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14112427454102098569337411 21168641181153147854006117)
                    ·
                      refine ⟨3969120221466215222626147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21168641181153147854006117 3969120221466215222626147)
                      ·
                        rfl

theorem cell23_7729834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_7729834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729834 prefixEnd_7729834 := by exact prefixLift 7729834
  have htrace : WordTrace (prefixWord ++ tailWord_7729834) baseStart_7729834 baseEnd_7729834 := by
    simpa [prefixWord, tailWord_7729834, baseEnd_7729834] using wordTrace_append hprefix tailTrace_7729834
  have hstable : (prefixWord ++ tailWord_7729834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729834).length < 2 ^ (prefixWord ++ tailWord_7729834).sum := by decide
  have hdescent : baseEnd_7729834 < baseStart_7729834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729837 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_7729837 : Nat := 118140960795 + 7729837 * 2 ^ 59
def prefixEnd_7729837 : Nat := 4983230072969 + 3 ^ 40 * 7729837 * 2
def baseEnd_7729837 : Nat := 3969121761908178710888633

theorem tailTrace_7729837 : CollatzResearch.WordTrace tailWord_7729837 prefixEnd_7729837 3969121761908178710888633 := by
  unfold tailWord_7729837
  simp only [CollatzResearch.WordTrace]
  refine ⟨281930316897128174902115765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187953544598085449934743843 281930316897128174902115765)
  ·
    refine ⟨26430967209105766397073353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281930316897128174902115765 26430967209105766397073353)
    ·
      refine ⟨19823225406829324797805015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26430967209105766397073353 19823225406829324797805015)
      ·
        refine ⟨29734838110243987196707523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19823225406829324797805015 29734838110243987196707523)
        ·
          refine ⟨44602257165365980795061285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29734838110243987196707523 44602257165365980795061285)
          ·
            refine ⟨8362923218506121399073991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44602257165365980795061285 8362923218506121399073991)
            ·
              refine ⟨12544384827759182098610987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8362923218506121399073991 12544384827759182098610987)
              ·
                refine ⟨18816577241638773147916481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12544384827759182098610987 18816577241638773147916481)
                ·
                  refine ⟨14112432931229079860937361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18816577241638773147916481 14112432931229079860937361)
                  ·
                    refine ⟨10584324698421809895703021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14112432931229079860937361 10584324698421809895703021)
                    ·
                      refine ⟨3969121761908178710888633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10584324698421809895703021 3969121761908178710888633)
                      ·
                        rfl

theorem cell23_7729837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_7729837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729837 prefixEnd_7729837 := by exact prefixLift 7729837
  have htrace : WordTrace (prefixWord ++ tailWord_7729837) baseStart_7729837 baseEnd_7729837 := by
    simpa [prefixWord, tailWord_7729837, baseEnd_7729837] using wordTrace_append hprefix tailTrace_7729837
  have hstable : (prefixWord ++ tailWord_7729837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729837).length < 2 ^ (prefixWord ++ tailWord_7729837).sum := by decide
  have hdescent : baseEnd_7729837 < baseStart_7729837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
