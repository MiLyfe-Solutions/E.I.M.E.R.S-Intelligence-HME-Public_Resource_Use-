import V185TrunkScan23Chunk0352

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2088338 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_2088338 : Nat := 118140960795 + 2088338 * 2 ^ 59
def prefixEnd_2088338 : Nat := 4983230072969 + 3 ^ 40 * 2088338 * 2
def baseEnd_2088338 : Nat := 1072321163049155601670915

theorem tailTrace_2088338 : CollatzResearch.WordTrace tailWord_2088338 prefixEnd_2088338 1072321163049155601670915 := by
  unfold tailWord_2088338
  simp only [CollatzResearch.WordTrace]
  refine ⟨19041986077078890145094417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50778629538877040386918445 19041986077078890145094417)
  ·
    refine ⟨14281489557809167608820813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19041986077078890145094417 14281489557809167608820813)
    ·
      refine ⟨5355558584178437853307805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14281489557809167608820813 5355558584178437853307805)
      ·
        refine ⟨2008334469066914194990427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5355558584178437853307805 2008334469066914194990427)
        ·
          refine ⟨3012501703600371292485641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2008334469066914194990427 3012501703600371292485641)
          ·
            refine ⟨2259376277700278469364231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3012501703600371292485641 2259376277700278469364231)
            ·
              refine ⟨3389064416550417704046347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259376277700278469364231 3389064416550417704046347)
              ·
                refine ⟨5083596624825626556069521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3389064416550417704046347 5083596624825626556069521)
                ·
                  refine ⟨3812697468619219917052141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5083596624825626556069521 3812697468619219917052141)
                  ·
                    refine ⟨1429761550732207468894553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3812697468619219917052141 1429761550732207468894553)
                    ·
                      refine ⟨1072321163049155601670915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1429761550732207468894553 1072321163049155601670915)
                      ·
                        rfl

theorem cell23_2088338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_2088338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088338 prefixEnd_2088338 := by exact prefixLift 2088338
  have htrace : WordTrace (prefixWord ++ tailWord_2088338) baseStart_2088338 baseEnd_2088338 := by
    simpa [prefixWord, tailWord_2088338, baseEnd_2088338] using wordTrace_append hprefix tailTrace_2088338
  have hstable : (prefixWord ++ tailWord_2088338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088338).length < 2 ^ (prefixWord ++ tailWord_2088338).sum := by decide
  have hdescent : baseEnd_2088338 < baseStart_2088338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088348 : List Nat := [2, 2, 3, 4, 2, 1, 2, 1, 1, 5]
def baseStart_2088348 : Nat := 118140960795 + 2088348 * 2 ^ 59
def prefixEnd_2088348 : Nat := 4983230072969 + 3 ^ 40 * 2088348 * 2
def baseEnd_2088348 : Nat := 357442099285233520848623

theorem tailTrace_2088348 : CollatzResearch.WordTrace tailWord_2088348 prefixEnd_2088348 357442099285233520848623 := by
  unfold tailWord_2088348
  simp only [CollatzResearch.WordTrace]
  refine ⟨38084154519139666144120849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50778872692186221525494465 38084154519139666144120849)
  ·
    refine ⟨28563115889354749608090637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38084154519139666144120849 28563115889354749608090637)
    ·
      refine ⟨10711168458508031103033989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28563115889354749608090637 10711168458508031103033989)
      ·
        refine ⟨2008344085970255831818873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10711168458508031103033989 2008344085970255831818873)
        ·
          refine ⟨1506258064477691873864155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2008344085970255831818873 1506258064477691873864155)
          ·
            refine ⟨2259387096716537810796233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506258064477691873864155 2259387096716537810796233)
            ·
              refine ⟨1694540322537403358097175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2259387096716537810796233 1694540322537403358097175)
              ·
                refine ⟨2541810483806105037145763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694540322537403358097175 2541810483806105037145763)
                ·
                  refine ⟨3812715725709157555718645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2541810483806105037145763 3812715725709157555718645)
                  ·
                    refine ⟨357442099285233520848623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3812715725709157555718645 357442099285233520848623)
                    ·
                      rfl

theorem cell23_2088348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_2088348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088348 prefixEnd_2088348 := by exact prefixLift 2088348
  have htrace : WordTrace (prefixWord ++ tailWord_2088348) baseStart_2088348 baseEnd_2088348 := by
    simpa [prefixWord, tailWord_2088348, baseEnd_2088348] using wordTrace_append hprefix tailTrace_2088348
  have hstable : (prefixWord ++ tailWord_2088348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088348).length < 2 ^ (prefixWord ++ tailWord_2088348).sum := by decide
  have hdescent : baseEnd_2088348 < baseStart_2088348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088351 : List Nat := [1, 1, 2, 5, 1, 2, 1, 5, 1, 2, 2]
def baseStart_2088351 : Nat := 118140960795 + 2088351 * 2 ^ 59
def prefixEnd_2088351 : Nat := 4983230072969 + 3 ^ 40 * 2088351 * 2
def baseEnd_2088351 : Nat := 1072327838297664050808355

theorem tailTrace_2088351 : CollatzResearch.WordTrace tailWord_2088351 prefixEnd_2088351 1072327838297664050808355 := by
  unfold tailWord_2088351
  simp only [CollatzResearch.WordTrace]
  refine ⟨76168418457268463800600907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50778945638178975867067271 76168418457268463800600907)
  ·
    refine ⟨114252627685902695700901361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76168418457268463800600907 114252627685902695700901361)
    ·
      refine ⟨85689470764427021775676021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114252627685902695700901361 85689470764427021775676021)
      ·
        refine ⟨8033387884165033291469627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85689470764427021775676021 8033387884165033291469627)
        ·
          refine ⟨12050081826247549937204441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8033387884165033291469627 12050081826247549937204441)
          ·
            refine ⟨9037561369685662452903331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12050081826247549937204441 9037561369685662452903331)
            ·
              refine ⟨13556342054528493679354997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9037561369685662452903331 13556342054528493679354997)
              ·
                refine ⟨1270907067612046282439531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13556342054528493679354997 1270907067612046282439531)
                ·
                  refine ⟨1906360601418069423659297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270907067612046282439531 1906360601418069423659297)
                  ·
                    refine ⟨1429770451063552067744473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1906360601418069423659297 1429770451063552067744473)
                    ·
                      refine ⟨1072327838297664050808355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1429770451063552067744473 1072327838297664050808355)
                      ·
                        rfl

theorem cell23_2088351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_2088351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088351 prefixEnd_2088351 := by exact prefixLift 2088351
  have htrace : WordTrace (prefixWord ++ tailWord_2088351) baseStart_2088351 baseEnd_2088351 := by
    simpa [prefixWord, tailWord_2088351, baseEnd_2088351] using wordTrace_append hprefix tailTrace_2088351
  have hstable : (prefixWord ++ tailWord_2088351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088351).length < 2 ^ (prefixWord ++ tailWord_2088351).sum := by decide
  have hdescent : baseEnd_2088351 < baseStart_2088351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088354 : List Nat := [3, 3, 1, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_2088354 : Nat := 118140960795 + 2088354 * 2 ^ 59
def prefixEnd_2088354 : Nat := 4983230072969 + 3 ^ 40 * 2088354 * 2
def baseEnd_2088354 : Nat := 1072329378739627539070841

theorem tailTrace_2088354 : CollatzResearch.WordTrace tailWord_2088354 prefixEnd_2088354 1072329378739627539070841 := by
  unfold tailWord_2088354
  simp only [CollatzResearch.WordTrace]
  refine ⟨19042131969064398828240029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50779018584171730208640077 19042131969064398828240029)
  ·
    refine ⟨7140799488399149560590011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19042131969064398828240029 7140799488399149560590011)
    ·
      refine ⟨10711199232598724340885017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7140799488399149560590011 10711199232598724340885017)
      ·
        refine ⟨8033399424449043255663763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10711199232598724340885017 8033399424449043255663763)
        ·
          refine ⟨12050099136673564883495645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8033399424449043255663763 12050099136673564883495645)
          ·
            refine ⟨4518787176252586831310867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12050099136673564883495645 4518787176252586831310867)
            ·
              refine ⟨6778180764378880246966301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518787176252586831310867 6778180764378880246966301)
              ·
                refine ⟨2541817786642080092612363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6778180764378880246966301 2541817786642080092612363)
                ·
                  refine ⟨3812726679963120138918545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2541817786642080092612363 3812726679963120138918545)
                  ·
                    refine ⟨2859545009972340104188909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3812726679963120138918545 2859545009972340104188909)
                    ·
                      refine ⟨1072329378739627539070841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2859545009972340104188909 1072329378739627539070841)
                      ·
                        rfl

theorem cell23_2088354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_2088354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088354 prefixEnd_2088354 := by exact prefixLift 2088354
  have htrace : WordTrace (prefixWord ++ tailWord_2088354) baseStart_2088354 baseEnd_2088354 := by
    simpa [prefixWord, tailWord_2088354, baseEnd_2088354] using wordTrace_append hprefix tailTrace_2088354
  have hstable : (prefixWord ++ tailWord_2088354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088354).length < 2 ^ (prefixWord ++ tailWord_2088354).sum := by decide
  have hdescent : baseEnd_2088354 < baseStart_2088354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088394 : List Nat := [3, 1, 2, 1, 2, 3, 1, 4, 1, 3, 2]
def baseStart_2088394 : Nat := 118140960795 + 2088394 * 2 ^ 59
def prefixEnd_2088394 : Nat := 4983230072969 + 3 ^ 40 * 2088394 * 2
def baseEnd_2088394 : Nat := 1072349917965807382570657

theorem tailTrace_2088394 : CollatzResearch.WordTrace tailWord_2088394 prefixEnd_2088394 1072349917965807382570657 := by
  unfold tailWord_2088394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19042496699028170536104059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50779991197408454762944157 19042496699028170536104059)
  ·
    refine ⟨28563745048542255804156089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19042496699028170536104059 28563745048542255804156089)
    ·
      refine ⟨21422808786406691853117067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28563745048542255804156089 21422808786406691853117067)
      ·
        refine ⟨32134213179610037779675601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21422808786406691853117067 32134213179610037779675601)
        ·
          refine ⟨24100659884707528334756701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32134213179610037779675601 24100659884707528334756701)
          ·
            refine ⟨9037747456765323125533763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24100659884707528334756701 9037747456765323125533763)
            ·
              refine ⟨13556621185147984688300645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9037747456765323125533763 13556621185147984688300645)
              ·
                refine ⟨2541866472215247129056371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13556621185147984688300645 2541866472215247129056371)
                ·
                  refine ⟨3812799708322870693584557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2541866472215247129056371 3812799708322870693584557)
                  ·
                    refine ⟨1429799890621076510094209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3812799708322870693584557 1429799890621076510094209)
                    ·
                      refine ⟨1072349917965807382570657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1429799890621076510094209 1072349917965807382570657)
                      ·
                        rfl

theorem cell23_2088394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_2088394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088394 prefixEnd_2088394 := by exact prefixLift 2088394
  have htrace : WordTrace (prefixWord ++ tailWord_2088394) baseStart_2088394 baseEnd_2088394 := by
    simpa [prefixWord, tailWord_2088394, baseEnd_2088394] using wordTrace_append hprefix tailTrace_2088394
  have hstable : (prefixWord ++ tailWord_2088394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088394).length < 2 ^ (prefixWord ++ tailWord_2088394).sum := by decide
  have hdescent : baseEnd_2088394 < baseStart_2088394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088407 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 1, 4, 2]
def baseStart_2088407 : Nat := 118140960795 + 2088407 * 2 ^ 59
def prefixEnd_2088407 : Nat := 4983230072969 + 3 ^ 40 * 2088407 * 2
def baseEnd_2088407 : Nat := 1072356593214315831708097

theorem tailTrace_2088407 : CollatzResearch.WordTrace tailWord_2088407 prefixEnd_2088407 1072356593214315831708097 := by
  unfold tailWord_2088407
  simp only [CollatzResearch.WordTrace]
  refine ⟨76170460945065585364639475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50780307296710390243092983 76170460945065585364639475)
  ·
    refine ⟨114255691417598378046959213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76170460945065585364639475 114255691417598378046959213)
    ·
      refine ⟨42845884281599391767609705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114255691417598378046959213 42845884281599391767609705)
      ·
        refine ⟨32134413211199543825707279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42845884281599391767609705 32134413211199543825707279)
        ·
          refine ⟨48201619816799315738560919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32134413211199543825707279 48201619816799315738560919)
          ·
            refine ⟨72302429725198973607841379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48201619816799315738560919 72302429725198973607841379)
            ·
              refine ⟨108453644587798460411762069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72302429725198973607841379 108453644587798460411762069)
              ·
                refine ⟨5083764590053052831801347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108453644587798460411762069 5083764590053052831801347)
                ·
                  refine ⟨7625646885079579247702021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5083764590053052831801347 7625646885079579247702021)
                  ·
                    refine ⟨1429808790952421108944129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7625646885079579247702021 1429808790952421108944129)
                    ·
                      refine ⟨1072356593214315831708097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1429808790952421108944129 1072356593214315831708097)
                      ·
                        rfl

theorem cell23_2088407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_2088407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088407 prefixEnd_2088407 := by exact prefixLift 2088407
  have htrace : WordTrace (prefixWord ++ tailWord_2088407) baseStart_2088407 baseEnd_2088407 := by
    simpa [prefixWord, tailWord_2088407, baseEnd_2088407] using wordTrace_append hprefix tailTrace_2088407
  have hstable : (prefixWord ++ tailWord_2088407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088407).length < 2 ^ (prefixWord ++ tailWord_2088407).sum := by decide
  have hdescent : baseEnd_2088407 < baseStart_2088407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088410 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_2088410 : Nat := 118140960795 + 2088410 * 2 ^ 59
def prefixEnd_2088410 : Nat := 4983230072969 + 3 ^ 40 * 2088410 * 2
def baseEnd_2088410 : Nat := 1072358133656279319970583

theorem tailTrace_2088410 : CollatzResearch.WordTrace tailWord_2088410 prefixEnd_2088410 1072358133656279319970583 := by
  unfold tailWord_2088410
  simp only [CollatzResearch.WordTrace]
  refine ⟨19042642591013679219249671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50780380242703144584665789 19042642591013679219249671)
  ·
    refine ⟨28563963886520518828874507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19042642591013679219249671 28563963886520518828874507)
    ·
      refine ⟨42845945829780778243311761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28563963886520518828874507 42845945829780778243311761)
      ·
        refine ⟨32134459372335583682483821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42845945829780778243311761 32134459372335583682483821)
        ·
          refine ⟨12050422264625843880931433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32134459372335583682483821 12050422264625843880931433)
          ·
            refine ⟨9037816698469382910698575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12050422264625843880931433 9037816698469382910698575)
            ·
              refine ⟨13556725047704074366047863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9037816698469382910698575 13556725047704074366047863)
              ·
                refine ⟨20335087571556111549071795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13556725047704074366047863 20335087571556111549071795)
                ·
                  refine ⟨30502631357334167323607693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20335087571556111549071795 30502631357334167323607693)
                  ·
                    refine ⟨11438486759000312746352885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30502631357334167323607693 11438486759000312746352885)
                    ·
                      refine ⟨1072358133656279319970583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11438486759000312746352885 1072358133656279319970583)
                      ·
                        rfl

theorem cell23_2088410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_2088410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088410 prefixEnd_2088410 := by exact prefixLift 2088410
  have htrace : WordTrace (prefixWord ++ tailWord_2088410) baseStart_2088410 baseEnd_2088410 := by
    simpa [prefixWord, tailWord_2088410, baseEnd_2088410] using wordTrace_append hprefix tailTrace_2088410
  have hstable : (prefixWord ++ tailWord_2088410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088410).length < 2 ^ (prefixWord ++ tailWord_2088410).sum := by decide
  have hdescent : baseEnd_2088410 < baseStart_2088410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088420 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_2088420 : Nat := 118140960795 + 2088420 * 2 ^ 59
def prefixEnd_2088420 : Nat := 4983230072969 + 3 ^ 40 * 2088420 * 2
def baseEnd_2088420 : Nat := 1072363268462824280845537

theorem tailTrace_2088420 : CollatzResearch.WordTrace tailWord_2088420 prefixEnd_2088420 1072363268462824280845537 := by
  unfold tailWord_2088420
  simp only [CollatzResearch.WordTrace]
  refine ⟨38085467547009244292431357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50780623396012325723241809 38085467547009244292431357)
  ·
    refine ⟨14282050330128466609661759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38085467547009244292431357 14282050330128466609661759)
    ·
      refine ⟨21423075495192699914492639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14282050330128466609661759 21423075495192699914492639)
      ·
        refine ⟨32134613242789049871738959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21423075495192699914492639 32134613242789049871738959)
        ·
          refine ⟨48201919864183574807608439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32134613242789049871738959 48201919864183574807608439)
          ·
            refine ⟨72302879796275362211412659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48201919864183574807608439 72302879796275362211412659)
            ·
              refine ⟨108454319694413043317118989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72302879796275362211412659 108454319694413043317118989)
              ·
                refine ⟨40670369885404891243919621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108454319694413043317118989 40670369885404891243919621)
                ·
                  refine ⟨7625694353513417108234929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40670369885404891243919621 7625694353513417108234929)
                  ·
                    refine ⟨5719270765135062831176197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7625694353513417108234929 5719270765135062831176197)
                    ·
                      refine ⟨1072363268462824280845537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5719270765135062831176197 1072363268462824280845537)
                      ·
                        rfl

theorem cell23_2088420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_2088420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088420 prefixEnd_2088420 := by exact prefixLift 2088420
  have htrace : WordTrace (prefixWord ++ tailWord_2088420) baseStart_2088420 baseEnd_2088420 := by
    simpa [prefixWord, tailWord_2088420, baseEnd_2088420] using wordTrace_append hprefix tailTrace_2088420
  have hstable : (prefixWord ++ tailWord_2088420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088420).length < 2 ^ (prefixWord ++ tailWord_2088420).sum := by decide
  have hdescent : baseEnd_2088420 < baseStart_2088420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088424 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_2088424 : Nat := 118140960795 + 2088424 * 2 ^ 59
def prefixEnd_2088424 : Nat := 4983230072969 + 3 ^ 40 * 2088424 * 2
def baseEnd_2088424 : Nat := 1072365322385442265195519

theorem tailTrace_2088424 : CollatzResearch.WordTrace tailWord_2088424 prefixEnd_2088424 1072365322385442265195519 := by
  unfold tailWord_2088424
  simp only [CollatzResearch.WordTrace]
  refine ⟨38085540493001998634004163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50780720657335998178672217 38085540493001998634004163)
  ·
    refine ⟨57128310739502997951006245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38085540493001998634004163 57128310739502997951006245)
    ·
      refine ⟨10711558263656812115813671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57128310739502997951006245 10711558263656812115813671)
      ·
        refine ⟨16067337395485218173720507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10711558263656812115813671 16067337395485218173720507)
        ·
          refine ⟨24101006093227827260580761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16067337395485218173720507 24101006093227827260580761)
          ·
            refine ⟨18075754569920870445435571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24101006093227827260580761 18075754569920870445435571)
            ·
              refine ⟨27113631854881305668153357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18075754569920870445435571 27113631854881305668153357)
              ·
                refine ⟨10167611945580489625557509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27113631854881305668153357 10167611945580489625557509)
                ·
                  refine ⟨1906427239796341804792033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10167611945580489625557509 1906427239796341804792033)
                  ·
                    refine ⟨1429820429847256353594025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1906427239796341804792033 1429820429847256353594025)
                    ·
                      refine ⟨1072365322385442265195519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1429820429847256353594025 1072365322385442265195519)
                      ·
                        rfl

theorem cell23_2088424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_2088424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088424 prefixEnd_2088424 := by exact prefixLift 2088424
  have htrace : WordTrace (prefixWord ++ tailWord_2088424) baseStart_2088424 baseEnd_2088424 := by
    simpa [prefixWord, tailWord_2088424, baseEnd_2088424] using wordTrace_append hprefix tailTrace_2088424
  have hstable : (prefixWord ++ tailWord_2088424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088424).length < 2 ^ (prefixWord ++ tailWord_2088424).sum := by decide
  have hdescent : baseEnd_2088424 < baseStart_2088424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088477 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_2088477 : Nat := 118140960795 + 2088477 * 2 ^ 59
def prefixEnd_2088477 : Nat := 4983230072969 + 3 ^ 40 * 2088477 * 2
def baseEnd_2088477 : Nat := 357464178953376852610925

theorem tailTrace_2088477 : CollatzResearch.WordTrace tailWord_2088477 prefixEnd_2088477 357464178953376852610925 := by
  unfold tailWord_2088477
  simp only [CollatzResearch.WordTrace]
  refine ⟨76173014054811987319687685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50782009369874658213125123 76173014054811987319687685)
  ·
    refine ⟨14282440135277247622441441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76173014054811987319687685 14282440135277247622441441)
    ·
      refine ⟨10711830101457935716831081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14282440135277247622441441 10711830101457935716831081)
      ·
        refine ⟨8033872576093451787623311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10711830101457935716831081 8033872576093451787623311)
        ·
          refine ⟨12050808864140177681434967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8033872576093451787623311 12050808864140177681434967)
          ·
            refine ⟨18076213296210266522152451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12050808864140177681434967 18076213296210266522152451)
            ·
              refine ⟨27114319944315399783228677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18076213296210266522152451 27114319944315399783228677)
              ·
                refine ⟨5083934989559137459355377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27114319944315399783228677 5083934989559137459355377)
                ·
                  refine ⟨3812951242169353094516533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5083934989559137459355377 3812951242169353094516533)
                  ·
                    refine ⟨357464178953376852610925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3812951242169353094516533 357464178953376852610925)
                    ·
                      rfl

theorem cell23_2088477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_2088477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088477 prefixEnd_2088477 := by exact prefixLift 2088477
  have htrace : WordTrace (prefixWord ++ tailWord_2088477) baseStart_2088477 baseEnd_2088477 := by
    simpa [prefixWord, tailWord_2088477, baseEnd_2088477] using wordTrace_append hprefix tailTrace_2088477
  have hstable : (prefixWord ++ tailWord_2088477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088477).length < 2 ^ (prefixWord ++ tailWord_2088477).sum := by decide
  have hdescent : baseEnd_2088477 < baseStart_2088477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088481 : List Nat := [1, 2, 3, 2, 2, 4, 2, 2, 5]
def baseStart_2088481 : Nat := 118140960795 + 2088481 * 2 ^ 59
def prefixEnd_2088481 : Nat := 4983230072969 + 3 ^ 40 * 2088481 * 2
def baseEnd_2088481 : Nat := 119154954531416504686973

theorem tailTrace_2088481 : CollatzResearch.WordTrace tailWord_2088481 prefixEnd_2088481 119154954531416504686973 := by
  unfold tailWord_2088481
  simp only [CollatzResearch.WordTrace]
  refine ⟨76173159946797496002833297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50782106631198330668555531 76173159946797496002833297)
  ·
    refine ⟨57129869960098122002124973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76173159946797496002833297 57129869960098122002124973)
    ·
      refine ⟨21423701235036795750796865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57129869960098122002124973 21423701235036795750796865)
      ·
        refine ⟨16067775926277596813097649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21423701235036795750796865 16067775926277596813097649)
        ·
          refine ⟨12050831944708197609823237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16067775926277596813097649 12050831944708197609823237)
          ·
            refine ⟨2259530989632787051841857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12050831944708197609823237 2259530989632787051841857)
            ·
              refine ⟨1694648242224590288881393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2259530989632787051841857 1694648242224590288881393)
              ·
                refine ⟨1270986181668442716661045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694648242224590288881393 1270986181668442716661045)
                ·
                  refine ⟨119154954531416504686973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1270986181668442716661045 119154954531416504686973)
                  ·
                    rfl

theorem cell23_2088481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 5].length) (baseStart_2088481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088481 prefixEnd_2088481 := by exact prefixLift 2088481
  have htrace : WordTrace (prefixWord ++ tailWord_2088481) baseStart_2088481 baseEnd_2088481 := by
    simpa [prefixWord, tailWord_2088481, baseEnd_2088481] using wordTrace_append hprefix tailTrace_2088481
  have hstable : (prefixWord ++ tailWord_2088481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088481).length < 2 ^ (prefixWord ++ tailWord_2088481).sum := by decide
  have hdescent : baseEnd_2088481 < baseStart_2088481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088517 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 1, 4, 3]
def baseStart_2088517 : Nat := 118140960795 + 2088517 * 2 ^ 59
def prefixEnd_2088517 : Nat := 4983230072969 + 3 ^ 40 * 2088517 * 2
def baseEnd_2088517 : Nat := 1072413076086310401332591

theorem tailTrace_2088517 : CollatzResearch.WordTrace tailWord_2088517 prefixEnd_2088517 1072413076086310401332591 := by
  unfold tailWord_2088517
  simp only [CollatzResearch.WordTrace]
  refine ⟨76174472974667074151143805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50782981983111382767429203 76174472974667074151143805)
  ·
    refine ⟨28565427365500152806678927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76174472974667074151143805 28565427365500152806678927)
    ·
      refine ⟨42848141048250229210018391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28565427365500152806678927 42848141048250229210018391)
      ·
        refine ⟨64272211572375343815027587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42848141048250229210018391 64272211572375343815027587)
        ·
          refine ⟨96408317358563015722541381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64272211572375343815027587 96408317358563015722541381)
          ·
            refine ⟨18076559504730565447976509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96408317358563015722541381 18076559504730565447976509)
            ·
              refine ⟨6778709814273962042991191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18076559504730565447976509 6778709814273962042991191)
              ·
                refine ⟨10168064721410943064486787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6778709814273962042991191 10168064721410943064486787)
                ·
                  refine ⟨15252097082116414596730181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10168064721410943064486787 15252097082116414596730181)
                  ·
                    refine ⟨2859768202896827736886909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15252097082116414596730181 2859768202896827736886909)
                    ·
                      refine ⟨1072413076086310401332591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2859768202896827736886909 1072413076086310401332591)
                      ·
                        rfl

theorem cell23_2088517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_2088517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088517 prefixEnd_2088517 := by exact prefixLift 2088517
  have htrace : WordTrace (prefixWord ++ tailWord_2088517) baseStart_2088517 baseEnd_2088517 := by
    simpa [prefixWord, tailWord_2088517, baseEnd_2088517] using wordTrace_append hprefix tailTrace_2088517
  have hstable : (prefixWord ++ tailWord_2088517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088517).length < 2 ^ (prefixWord ++ tailWord_2088517).sum := by decide
  have hdescent : baseEnd_2088517 < baseStart_2088517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088634 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4]
def baseStart_2088634 : Nat := 118140960795 + 2088634 * 2 ^ 59
def prefixEnd_2088634 : Nat := 4983230072969 + 3 ^ 40 * 2088634 * 2
def baseEnd_2088634 : Nat := 1072473153322886443569553

theorem tailTrace_2088634 : CollatzResearch.WordTrace tailWord_2088634 prefixEnd_2088634 1072473153322886443569553 := by
  unfold tailWord_2088634
  simp only [CollatzResearch.WordTrace]
  refine ⟨19044685078810800783288239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50785826876828802088768637 19044685078810800783288239)
  ·
    refine ⟨28567027618216201174932359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19044685078810800783288239 28567027618216201174932359)
    ·
      refine ⟨42850541427324301762398539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28567027618216201174932359 42850541427324301762398539)
      ·
        refine ⟨64275812140986452643597809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42850541427324301762398539 64275812140986452643597809)
        ·
          refine ⟨48206859105739839482698357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64275812140986452643597809 48206859105739839482698357)
          ·
            refine ⟨4519393041163109951502971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48206859105739839482698357 4519393041163109951502971)
            ·
              refine ⟨6779089561744664927254457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4519393041163109951502971 6779089561744664927254457)
              ·
                refine ⟨5084317171308498695440843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6779089561744664927254457 5084317171308498695440843)
                ·
                  refine ⟨7626475756962748043161265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5084317171308498695440843 7626475756962748043161265)
                  ·
                    refine ⟨5719856817722061032370949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7626475756962748043161265 5719856817722061032370949)
                    ·
                      refine ⟨1072473153322886443569553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5719856817722061032370949 1072473153322886443569553)
                      ·
                        rfl

theorem cell23_2088634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_2088634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088634 prefixEnd_2088634 := by exact prefixLift 2088634
  have htrace : WordTrace (prefixWord ++ tailWord_2088634) baseStart_2088634 baseEnd_2088634 := by
    simpa [prefixWord, tailWord_2088634, baseEnd_2088634] using wordTrace_append hprefix tailTrace_2088634
  have hstable : (prefixWord ++ tailWord_2088634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088634).length < 2 ^ (prefixWord ++ tailWord_2088634).sum := by decide
  have hdescent : baseEnd_2088634 < baseStart_2088634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088638 : List Nat := [4, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_2088638 : Nat := 118140960795 + 2088638 * 2 ^ 59
def prefixEnd_2088638 : Nat := 4983230072969 + 3 ^ 40 * 2088638 * 2
def baseEnd_2088638 : Nat := 1072475207245504427919535

theorem tailTrace_2088638 : CollatzResearch.WordTrace tailWord_2088638 prefixEnd_2088638 1072475207245504427919535 := by
  unfold tailWord_2088638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9522360775903588977037321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50785924138152474544199045 9522360775903588977037321)
  ·
    refine ⟨7141770581927691732777991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9522360775903588977037321 7141770581927691732777991)
    ·
      refine ⟨10712655872891537599166987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7141770581927691732777991 10712655872891537599166987)
      ·
        refine ⟨16068983809337306398750481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10712655872891537599166987 16068983809337306398750481)
        ·
          refine ⟨12051737857002979799062861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16068983809337306398750481 12051737857002979799062861)
          ·
            refine ⟨4519401696376117424648573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12051737857002979799062861 4519401696376117424648573)
            ·
              refine ⟨1694775636141044034243215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4519401696376117424648573 1694775636141044034243215)
              ·
                refine ⟨2542163454211566051364823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694775636141044034243215 2542163454211566051364823)
                ·
                  refine ⟨3813245181317349077047235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542163454211566051364823 3813245181317349077047235)
                  ·
                    refine ⟨5719867771976023615570853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3813245181317349077047235 5719867771976023615570853)
                    ·
                      refine ⟨1072475207245504427919535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5719867771976023615570853 1072475207245504427919535)
                      ·
                        rfl

theorem cell23_2088638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_2088638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088638 prefixEnd_2088638 := by exact prefixLift 2088638
  have htrace : WordTrace (prefixWord ++ tailWord_2088638) baseStart_2088638 baseEnd_2088638 := by
    simpa [prefixWord, tailWord_2088638, baseEnd_2088638] using wordTrace_append hprefix tailTrace_2088638
  have hstable : (prefixWord ++ tailWord_2088638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088638).length < 2 ^ (prefixWord ++ tailWord_2088638).sum := by decide
  have hdescent : baseEnd_2088638 < baseStart_2088638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088654 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_2088654 : Nat := 118140960795 + 2088654 * 2 ^ 59
def prefixEnd_2088654 : Nat := 4983230072969 + 3 ^ 40 * 2088654 * 2
def baseEnd_2088654 : Nat := 1072483422935976365319461

theorem tailTrace_2088654 : CollatzResearch.WordTrace tailWord_2088654 prefixEnd_2088654 1072483422935976365319461 := by
  unfold tailWord_2088654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9522433721896343318610127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50786313183447164365920677 9522433721896343318610127)
  ·
    refine ⟨14283650582844514977915191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9522433721896343318610127 14283650582844514977915191)
    ·
      refine ⟨21425475874266772466872787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14283650582844514977915191 21425475874266772466872787)
      ·
        refine ⟨32138213811400158700309181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21425475874266772466872787 32138213811400158700309181)
        ·
          refine ⟨12051830179275059512615943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32138213811400158700309181 12051830179275059512615943)
          ·
            refine ⟨18077745268912589268923915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12051830179275059512615943 18077745268912589268923915)
            ·
              refine ⟨27116617903368883903385873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18077745268912589268923915 27116617903368883903385873)
              ·
                refine ⟨20337463427526662927539405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27116617903368883903385873 20337463427526662927539405)
                ·
                  refine ⟨7626548785322498597827277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20337463427526662927539405 7626548785322498597827277)
                  ·
                    refine ⟨2859955794495936974185229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7626548785322498597827277 2859955794495936974185229)
                    ·
                      refine ⟨1072483422935976365319461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2859955794495936974185229 1072483422935976365319461)
                      ·
                        rfl

theorem cell23_2088654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_2088654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088654 prefixEnd_2088654 := by exact prefixLift 2088654
  have htrace : WordTrace (prefixWord ++ tailWord_2088654) baseStart_2088654 baseEnd_2088654 := by
    simpa [prefixWord, tailWord_2088654, baseEnd_2088654] using wordTrace_append hprefix tailTrace_2088654
  have hstable : (prefixWord ++ tailWord_2088654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088654).length < 2 ^ (prefixWord ++ tailWord_2088654).sum := by decide
  have hdescent : baseEnd_2088654 < baseStart_2088654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088657 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 2, 7]
def baseStart_2088657 : Nat := 118140960795 + 2088657 * 2 ^ 59
def prefixEnd_2088657 : Nat := 4983230072969 + 3 ^ 40 * 2088657 * 2
def baseEnd_2088657 : Nat := 357494987792646617860649

theorem tailTrace_2088657 : CollatzResearch.WordTrace tailWord_2088657 prefixEnd_2088657 357494987792646617860649 := by
  unfold tailWord_2088657
  simp only [CollatzResearch.WordTrace]
  refine ⟨76179579194159878061240225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50786386129439918707493483 76179579194159878061240225)
  ·
    refine ⟨57134684395619908545930169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76179579194159878061240225 57134684395619908545930169)
    ·
      refine ⟨42851013296714931409447627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57134684395619908545930169 42851013296714931409447627)
      ·
        refine ⟨64276519945072397114171441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42851013296714931409447627 64276519945072397114171441)
        ·
          refine ⟨48207389958804297835628581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64276519945072397114171441 48207389958804297835628581)
          ·
            refine ⟨9038885617275805844180359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48207389958804297835628581 9038885617275805844180359)
            ·
              refine ⟨13558328425913708766270539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9038885617275805844180359 13558328425913708766270539)
              ·
                refine ⟨20337492638870563149405809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13558328425913708766270539 20337492638870563149405809)
                ·
                  refine ⟨15253119479152922362054357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20337492638870563149405809 15253119479152922362054357)
                  ·
                    refine ⟨357494987792646617860649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15253119479152922362054357 357494987792646617860649)
                    ·
                      rfl

theorem cell23_2088657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_2088657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088657 prefixEnd_2088657 := by exact prefixLift 2088657
  have htrace : WordTrace (prefixWord ++ tailWord_2088657) baseStart_2088657 baseEnd_2088657 := by
    simpa [prefixWord, tailWord_2088657, baseEnd_2088657] using wordTrace_append hprefix tailTrace_2088657
  have hstable : (prefixWord ++ tailWord_2088657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088657).length < 2 ^ (prefixWord ++ tailWord_2088657).sum := by decide
  have hdescent : baseEnd_2088657 < baseStart_2088657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088668 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2088668 : Nat := 118140960795 + 2088668 * 2 ^ 59
def prefixEnd_2088668 : Nat := 4983230072969 + 3 ^ 40 * 2088668 * 2
def baseEnd_2088668 : Nat := 1072490611665139310544397

theorem tailTrace_2088668 : CollatzResearch.WordTrace tailWord_2088668 prefixEnd_2088668 1072490611665139310544397 := by
  unfold tailWord_2088668
  simp only [CollatzResearch.WordTrace]
  refine ⟨38089990198560013469945329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50786653598080017959927105 38089990198560013469945329)
  ·
    refine ⟨28567492648920010102458997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38089990198560013469945329 28567492648920010102458997)
    ·
      refine ⟨2678202435836250947105531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28567492648920010102458997 2678202435836250947105531)
      ·
        refine ⟨4017303653754376420658297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678202435836250947105531 4017303653754376420658297)
        ·
          refine ⟨3012977740315782315493723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4017303653754376420658297 3012977740315782315493723)
          ·
            refine ⟨4519466610473673473240585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012977740315782315493723 4519466610473673473240585)
            ·
              refine ⟨3389599957855255104930439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4519466610473673473240585 3389599957855255104930439)
              ·
                refine ⟨5084399936782882657395659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3389599957855255104930439 5084399936782882657395659)
                ·
                  refine ⟨7626599905174323986093489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5084399936782882657395659 7626599905174323986093489)
                  ·
                    refine ⟨5719949928880742989570117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7626599905174323986093489 5719949928880742989570117)
                    ·
                      refine ⟨1072490611665139310544397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5719949928880742989570117 1072490611665139310544397)
                      ·
                        rfl

theorem cell23_2088668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2088668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088668 prefixEnd_2088668 := by exact prefixLift 2088668
  have htrace : WordTrace (prefixWord ++ tailWord_2088668) baseStart_2088668 baseEnd_2088668 := by
    simpa [prefixWord, tailWord_2088668, baseEnd_2088668] using wordTrace_append hprefix tailTrace_2088668
  have hstable : (prefixWord ++ tailWord_2088668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088668).length < 2 ^ (prefixWord ++ tailWord_2088668).sum := by decide
  have hdescent : baseEnd_2088668 < baseStart_2088668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088671 : List Nat := [1, 1, 2, 3, 2, 2, 1, 5, 2, 1, 3]
def baseStart_2088671 : Nat := 118140960795 + 2088671 * 2 ^ 59
def prefixEnd_2088671 : Nat := 4983230072969 + 3 ^ 40 * 2088671 * 2
def baseEnd_2088671 : Nat := 1072492152107102798806883

theorem tailTrace_2088671 : CollatzResearch.WordTrace tailWord_2088671 prefixEnd_2088671 1072492152107102798806883 := by
  unfold tailWord_2088671
  simp only [CollatzResearch.WordTrace]
  refine ⟨76180089816109158452249867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50786726544072772301499911 76180089816109158452249867)
  ·
    refine ⟨114270134724163737678374801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76180089816109158452249867 114270134724163737678374801)
    ·
      refine ⟨85702601043122803258781101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114270134724163737678374801 85702601043122803258781101)
      ·
        refine ⟨32138475391171051222042913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85702601043122803258781101 32138475391171051222042913)
        ·
          refine ⟨24103856543378288416532185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32138475391171051222042913 24103856543378288416532185)
          ·
            refine ⟨18077892407533716312399139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24103856543378288416532185 18077892407533716312399139)
            ·
              refine ⟨27116838611300574468598709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18077892407533716312399139 27116838611300574468598709)
              ·
                refine ⟨2542203619809428856431129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27116838611300574468598709 2542203619809428856431129)
                ·
                  refine ⟨1906652714857071642323347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2542203619809428856431129 1906652714857071642323347)
                  ·
                    refine ⟨2859979072285607463485021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1906652714857071642323347 2859979072285607463485021)
                    ·
                      refine ⟨1072492152107102798806883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2859979072285607463485021 1072492152107102798806883)
                      ·
                        rfl

theorem cell23_2088671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_2088671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088671 prefixEnd_2088671 := by exact prefixLift 2088671
  have htrace : WordTrace (prefixWord ++ tailWord_2088671) baseStart_2088671 baseEnd_2088671 := by
    simpa [prefixWord, tailWord_2088671, baseEnd_2088671] using wordTrace_append hprefix tailTrace_2088671
  have hstable : (prefixWord ++ tailWord_2088671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088671).length < 2 ^ (prefixWord ++ tailWord_2088671).sum := by decide
  have hdescent : baseEnd_2088671 < baseStart_2088671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088681 : List Nat := [1, 2, 1, 1, 1, 2, 3, 6, 1, 3, 2]
def baseStart_2088681 : Nat := 118140960795 + 2088681 * 2 ^ 59
def prefixEnd_2088681 : Nat := 4983230072969 + 3 ^ 40 * 2088681 * 2
def baseEnd_2088681 : Nat := 1072497286913647759681837

theorem tailTrace_2088681 : CollatzResearch.WordTrace tailWord_2088681 prefixEnd_2088681 1072497286913647759681837 := by
  unfold tailWord_2088681
  simp only [CollatzResearch.WordTrace]
  refine ⟨76180454546072930160113897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50786969697381953440075931 76180454546072930160113897)
  ·
    refine ⟨57135340909554697620085423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76180454546072930160113897 57135340909554697620085423)
    ·
      refine ⟨85703011364332046430128135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57135340909554697620085423 85703011364332046430128135)
      ·
        refine ⟨128554517046498069645192203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85703011364332046430128135 128554517046498069645192203)
        ·
          refine ⟨192831775569747104467788305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128554517046498069645192203 192831775569747104467788305)
          ·
            refine ⟨144623831677310328350841229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192831775569747104467788305 144623831677310328350841229)
            ·
              refine ⟨54233936878991373131565461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144623831677310328350841229 54233936878991373131565461)
              ·
                refine ⟨2542215791202720615542131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54233936878991373131565461 2542215791202720615542131)
                ·
                  refine ⟨3813323686804080923313197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542215791202720615542131 3813323686804080923313197)
                  ·
                    refine ⟨1429996382551530346242449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3813323686804080923313197 1429996382551530346242449)
                    ·
                      refine ⟨1072497286913647759681837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1429996382551530346242449 1072497286913647759681837)
                      ·
                        rfl

theorem cell23_2088681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 3, 2].length) (baseStart_2088681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088681 prefixEnd_2088681 := by exact prefixLift 2088681
  have htrace : WordTrace (prefixWord ++ tailWord_2088681) baseStart_2088681 baseEnd_2088681 := by
    simpa [prefixWord, tailWord_2088681, baseEnd_2088681] using wordTrace_append hprefix tailTrace_2088681
  have hstable : (prefixWord ++ tailWord_2088681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088681).length < 2 ^ (prefixWord ++ tailWord_2088681).sum := by decide
  have hdescent : baseEnd_2088681 < baseStart_2088681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088687 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 1, 8]
def baseStart_2088687 : Nat := 118140960795 + 2088687 * 2 ^ 59
def prefixEnd_2088687 : Nat := 4983230072969 + 3 ^ 40 * 2088687 * 2
def baseEnd_2088687 : Nat := 357500122599191578735603

theorem tailTrace_2088687 : CollatzResearch.WordTrace tailWord_2088687 prefixEnd_2088687 357500122599191578735603 := by
  unfold tailWord_2088687
  simp only [CollatzResearch.WordTrace]
  refine ⟨76180673384051193184832315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50787115589367462123221543 76180673384051193184832315)
  ·
    refine ⟨114271010076076789777248473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76180673384051193184832315 114271010076076789777248473)
    ·
      refine ⟨85703257557057592332936355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114271010076076789777248473 85703257557057592332936355)
      ·
        refine ⟨128554886335586388499404533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85703257557057592332936355 128554886335586388499404533)
        ·
          refine ⟨12052020593961223921819175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128554886335586388499404533 12052020593961223921819175)
          ·
            refine ⟨18078030890941835882728763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12052020593961223921819175 18078030890941835882728763)
            ·
              refine ⟨27117046336412753824093145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18078030890941835882728763 27117046336412753824093145)
              ·
                refine ⟨20337784752309565368069859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27117046336412753824093145 20337784752309565368069859)
                ·
                  refine ⟨30506677128464348052104789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20337784752309565368069859 30506677128464348052104789)
                  ·
                    refine ⟨357500122599191578735603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30506677128464348052104789 357500122599191578735603)
                    ·
                      rfl

theorem cell23_2088687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_2088687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088687 prefixEnd_2088687 := by exact prefixLift 2088687
  have htrace : WordTrace (prefixWord ++ tailWord_2088687) baseStart_2088687 baseEnd_2088687 := by
    simpa [prefixWord, tailWord_2088687, baseEnd_2088687] using wordTrace_append hprefix tailTrace_2088687
  have hstable : (prefixWord ++ tailWord_2088687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088687).length < 2 ^ (prefixWord ++ tailWord_2088687).sum := by decide
  have hdescent : baseEnd_2088687 < baseStart_2088687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088692 : List Nat := [2, 6, 1, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_2088692 : Nat := 118140960795 + 2088692 * 2 ^ 59
def prefixEnd_2088692 : Nat := 4983230072969 + 3 ^ 40 * 2088692 * 2
def baseEnd_2088692 : Nat := 1072502935200847216644287

theorem tailTrace_2088692 : CollatzResearch.WordTrace tailWord_2088692 prefixEnd_2088692 1072502935200847216644287 := by
  unfold tailWord_2088692
  simp only [CollatzResearch.WordTrace]
  refine ⟨38090427874516539519382165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50787237166022052692509553 38090427874516539519382165)
  ·
    refine ⟨1785488806617962789971039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38090427874516539519382165 1785488806617962789971039)
    ·
      refine ⟨2678233209926944184956559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1785488806617962789971039 2678233209926944184956559)
      ·
        refine ⟨4017349814890416277434839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678233209926944184956559 4017349814890416277434839)
        ·
          refine ⟨6026024722335624416152259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4017349814890416277434839 6026024722335624416152259)
          ·
            refine ⟨9039037083503436624228389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6026024722335624416152259 9039037083503436624228389)
            ·
              refine ⟨1694819453156894367042823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9039037083503436624228389 1694819453156894367042823)
              ·
                refine ⟨2542229179735341550564235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694819453156894367042823 2542229179735341550564235)
                ·
                  refine ⟨3813343769603012325846353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542229179735341550564235 3813343769603012325846353)
                  ·
                    refine ⟨2860007827202259244384765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3813343769603012325846353 2860007827202259244384765)
                    ·
                      refine ⟨1072502935200847216644287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2860007827202259244384765 1072502935200847216644287)
                      ·
                        rfl

theorem cell23_2088692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_2088692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088692 prefixEnd_2088692 := by exact prefixLift 2088692
  have htrace : WordTrace (prefixWord ++ tailWord_2088692) baseStart_2088692 baseEnd_2088692 := by
    simpa [prefixWord, tailWord_2088692, baseEnd_2088692] using wordTrace_append hprefix tailTrace_2088692
  have hstable : (prefixWord ++ tailWord_2088692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088692).length < 2 ^ (prefixWord ++ tailWord_2088692).sum := by decide
  have hdescent : baseEnd_2088692 < baseStart_2088692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088722 : List Nat := [3, 2, 4, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_2088722 : Nat := 118140960795 + 2088722 * 2 ^ 59
def prefixEnd_2088722 : Nat := 4983230072969 + 3 ^ 40 * 2088722 * 2
def baseEnd_2088722 : Nat := 1072518339620482099269149

theorem tailTrace_2088722 : CollatzResearch.WordTrace tailWord_2088722 prefixEnd_2088722 1072518339620482099269149 := by
  unfold tailWord_2088722
  simp only [CollatzResearch.WordTrace]
  refine ⟨19045487484731098540589105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50787966625949596108237613 19045487484731098540589105)
  ·
    refine ⟨14284115613548323905441829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19045487484731098540589105 14284115613548323905441829)
    ·
      refine ⟨2678271677540310732270343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14284115613548323905441829 2678271677540310732270343)
      ·
        refine ⟨4017407516310466098405515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678271677540310732270343 4017407516310466098405515)
        ·
          refine ⟨6026111274465699147608273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4017407516310466098405515 6026111274465699147608273)
          ·
            refine ⟨4519583455849274360706205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6026111274465699147608273 4519583455849274360706205)
            ·
              refine ⟨1694843795943477885264827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4519583455849274360706205 1694843795943477885264827)
              ·
                refine ⟨2542265693915216827897241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694843795943477885264827 2542265693915216827897241)
                ·
                  refine ⟨1906699270436412620922931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2542265693915216827897241 1906699270436412620922931)
                  ·
                    refine ⟨2860048905654618931384397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1906699270436412620922931 2860048905654618931384397)
                    ·
                      refine ⟨1072518339620482099269149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2860048905654618931384397 1072518339620482099269149)
                      ·
                        rfl

theorem cell23_2088722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_2088722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088722 prefixEnd_2088722 := by exact prefixLift 2088722
  have htrace : WordTrace (prefixWord ++ tailWord_2088722) baseStart_2088722 baseEnd_2088722 := by
    simpa [prefixWord, tailWord_2088722, baseEnd_2088722] using wordTrace_append hprefix tailTrace_2088722
  have hstable : (prefixWord ++ tailWord_2088722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088722).length < 2 ^ (prefixWord ++ tailWord_2088722).sum := by decide
  have hdescent : baseEnd_2088722 < baseStart_2088722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088728 : List Nat := [2, 1, 2, 3, 1, 1, 2, 5, 2, 2, 2]
def baseStart_2088728 : Nat := 118140960795 + 2088728 * 2 ^ 59
def prefixEnd_2088728 : Nat := 4983230072969 + 3 ^ 40 * 2088728 * 2
def baseEnd_2088728 : Nat := 1072521420504409075794121

theorem tailTrace_2088728 : CollatzResearch.WordTrace tailWord_2088728 prefixEnd_2088728 1072521420504409075794121 := by
  unfold tailWord_2088728
  simp only [CollatzResearch.WordTrace]
  refine ⟨38091084388451328593537419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50788112517935104791383225 38091084388451328593537419)
  ·
    refine ⟨57136626582676992890306129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38091084388451328593537419 57136626582676992890306129)
    ·
      refine ⟨42852469937007744667729597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57136626582676992890306129 42852469937007744667729597)
      ·
        refine ⟨16069676226377904250398599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42852469937007744667729597 16069676226377904250398599)
        ·
          refine ⟨24104514339566856375597899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16069676226377904250398599 24104514339566856375597899)
          ·
            refine ⟨36156771509350284563396849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24104514339566856375597899 36156771509350284563396849)
            ·
              refine ⟨27117578632012713422547637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36156771509350284563396849 27117578632012713422547637)
              ·
                refine ⟨2542272996751191883363841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27117578632012713422547637 2542272996751191883363841)
                ·
                  refine ⟨1906704747563393912522881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2542272996751191883363841 1906704747563393912522881)
                  ·
                    refine ⟨1430028560672545434392161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1906704747563393912522881 1430028560672545434392161)
                    ·
                      refine ⟨1072521420504409075794121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1430028560672545434392161 1072521420504409075794121)
                      ·
                        rfl

theorem cell23_2088728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_2088728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088728 prefixEnd_2088728 := by exact prefixLift 2088728
  have htrace : WordTrace (prefixWord ++ tailWord_2088728) baseStart_2088728 baseEnd_2088728 := by
    simpa [prefixWord, tailWord_2088728, baseEnd_2088728] using wordTrace_append hprefix tailTrace_2088728
  have hstable : (prefixWord ++ tailWord_2088728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088728).length < 2 ^ (prefixWord ++ tailWord_2088728).sum := by decide
  have hdescent : baseEnd_2088728 < baseStart_2088728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088747 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 5, 7]
def baseStart_2088747 : Nat := 118140960795 + 2088747 * 2 ^ 59
def prefixEnd_2088747 : Nat := 4983230072969 + 3 ^ 40 * 2088747 * 2
def baseEnd_2088747 : Nat := 357510392212281500485511

theorem tailTrace_2088747 : CollatzResearch.WordTrace tailWord_2088747 prefixEnd_2088747 357510392212281500485511 := by
  unfold tailWord_2088747
  simp only [CollatzResearch.WordTrace]
  refine ⟨76182861763833823432016495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50788574509222548954677663 76182861763833823432016495)
  ·
    refine ⟨114274292645750735148024743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76182861763833823432016495 114274292645750735148024743)
    ·
      refine ⟨171411438968626102722037115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114274292645750735148024743 171411438968626102722037115)
      ·
        refine ⟨257117158452939154083055673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171411438968626102722037115 257117158452939154083055673)
        ·
          refine ⟨192837868839704365562291755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257117158452939154083055673 192837868839704365562291755)
          ·
            refine ⟨289256803259556548343437633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192837868839704365562291755 289256803259556548343437633)
            ·
              refine ⟨216942602444667411257578225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289256803259556548343437633 216942602444667411257578225)
              ·
                refine ⟨162706951833500558443183669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216942602444667411257578225 162706951833500558443183669)
                ·
                  refine ⟨15253776734390677354048469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162706951833500558443183669 15253776734390677354048469)
                  ·
                    refine ⟨357510392212281500485511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15253776734390677354048469 357510392212281500485511)
                    ·
                      rfl

theorem cell23_2088747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 7].length) (baseStart_2088747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088747 prefixEnd_2088747 := by exact prefixLift 2088747
  have htrace : WordTrace (prefixWord ++ tailWord_2088747) baseStart_2088747 baseEnd_2088747 := by
    simpa [prefixWord, tailWord_2088747, baseEnd_2088747] using wordTrace_append hprefix tailTrace_2088747
  have hstable : (prefixWord ++ tailWord_2088747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088747).length < 2 ^ (prefixWord ++ tailWord_2088747).sum := by decide
  have hdescent : baseEnd_2088747 < baseStart_2088747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088764 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 4, 5]
def baseStart_2088764 : Nat := 118140960795 + 2088764 * 2 ^ 59
def prefixEnd_2088764 : Nat := 4983230072969 + 3 ^ 40 * 2088764 * 2
def baseEnd_2088764 : Nat := 357513301935990311647985

theorem tailTrace_2088764 : CollatzResearch.WordTrace tailWord_2088764 prefixEnd_2088764 357513301935990311647985 := by
  unfold tailWord_2088764
  simp only [CollatzResearch.WordTrace]
  refine ⟨38091740902386117667692673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50788987869848156890256897 38091740902386117667692673)
  ·
    refine ⟨28568805676789588250769505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38091740902386117667692673 28568805676789588250769505)
    ·
      refine ⟨21426604257592191188077129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28568805676789588250769505 21426604257592191188077129)
      ·
        refine ⟨16069953193194143391057847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21426604257592191188077129 16069953193194143391057847)
        ·
          refine ⟨24104929789791215086586771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16069953193194143391057847 24104929789791215086586771)
          ·
            refine ⟨36157394684686822629880157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24104929789791215086586771 36157394684686822629880157)
            ·
              refine ⟨13559023006757558486205059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36157394684686822629880157 13559023006757558486205059)
              ·
                refine ⟨20338534510136337729307589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13559023006757558486205059 20338534510136337729307589)
                ·
                  refine ⟨3813475220650563324245173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20338534510136337729307589 3813475220650563324245173)
                  ·
                    refine ⟨357513301935990311647985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3813475220650563324245173 357513301935990311647985)
                    ·
                      rfl

theorem cell23_2088764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_2088764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088764 prefixEnd_2088764 := by exact prefixLift 2088764
  have htrace : WordTrace (prefixWord ++ tailWord_2088764) baseStart_2088764 baseEnd_2088764 := by
    simpa [prefixWord, tailWord_2088764, baseEnd_2088764] using wordTrace_append hprefix tailTrace_2088764
  have hstable : (prefixWord ++ tailWord_2088764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088764).length < 2 ^ (prefixWord ++ tailWord_2088764).sum := by decide
  have hdescent : baseEnd_2088764 < baseStart_2088764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088784 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 4]
def baseStart_2088784 : Nat := 118140960795 + 2088784 * 2 ^ 59
def prefixEnd_2088784 : Nat := 4983230072969 + 3 ^ 40 * 2088784 * 2
def baseEnd_2088784 : Nat := 1072550175421060856693863

theorem tailTrace_2088784 : CollatzResearch.WordTrace tailWord_2088784 prefixEnd_2088784 1072550175421060856693863 := by
  unfold tailWord_2088784
  simp only [CollatzResearch.WordTrace]
  refine ⟨38092105632349889375556703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50789474176466519167408937 38092105632349889375556703)
  ·
    refine ⟨57138158448524834063335055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38092105632349889375556703 57138158448524834063335055)
    ·
      refine ⟨85707237672787251095002583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57138158448524834063335055 85707237672787251095002583)
      ·
        refine ⟨128560856509180876642503875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85707237672787251095002583 128560856509180876642503875)
        ·
          refine ⟨192841284763771314963755813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128560856509180876642503875 192841284763771314963755813)
          ·
            refine ⟨36157740893207121555704215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192841284763771314963755813 36157740893207121555704215)
            ·
              refine ⟨54236611339810682333556323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36157740893207121555704215 54236611339810682333556323)
              ·
                refine ⟨81354917009716023500334485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54236611339810682333556323 81354917009716023500334485)
                ·
                  refine ⟨3813511734830438601578179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81354917009716023500334485 3813511734830438601578179)
                  ·
                    refine ⟨5720267602245657902367269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3813511734830438601578179 5720267602245657902367269)
                    ·
                      refine ⟨1072550175421060856693863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5720267602245657902367269 1072550175421060856693863)
                      ·
                        rfl

theorem cell23_2088784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_2088784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088784 prefixEnd_2088784 := by exact prefixLift 2088784
  have htrace : WordTrace (prefixWord ++ tailWord_2088784) baseStart_2088784 baseEnd_2088784 := by
    simpa [prefixWord, tailWord_2088784, baseEnd_2088784] using wordTrace_append hprefix tailTrace_2088784
  have hstable : (prefixWord ++ tailWord_2088784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088784).length < 2 ^ (prefixWord ++ tailWord_2088784).sum := by decide
  have hdescent : baseEnd_2088784 < baseStart_2088784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088801 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_2088801 : Nat := 118140960795 + 2088801 * 2 ^ 59
def prefixEnd_2088801 : Nat := 4983230072969 + 3 ^ 40 * 2088801 * 2
def baseEnd_2088801 : Nat := 1072558904592187290181285

theorem tailTrace_2088801 : CollatzResearch.WordTrace tailWord_2088801 prefixEnd_2088801 1072558904592187290181285 := by
  unfold tailWord_2088801
  simp only [CollatzResearch.WordTrace]
  refine ⟨76184831305638190654482257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50789887537092127102988171 76184831305638190654482257)
  ·
    refine ⟨57138623479228642990861693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76184831305638190654482257 57138623479228642990861693)
    ·
      refine ⟨21426983804710741121573135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57138623479228642990861693 21426983804710741121573135)
      ·
        refine ⟨32140475707066111682359703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21426983804710741121573135 32140475707066111682359703)
        ·
          refine ⟨48210713560599167523539555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32140475707066111682359703 48210713560599167523539555)
          ·
            refine ⟨72316070340898751285309333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48210713560599167523539555 72316070340898751285309333)
            ·
              refine ⟨3389815797229628966498875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72316070340898751285309333 3389815797229628966498875)
              ·
                refine ⟨5084723695844443449748313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3389815797229628966498875 5084723695844443449748313)
                ·
                  refine ⟨3813542771883332587311235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5084723695844443449748313 3813542771883332587311235)
                  ·
                    refine ⟨5720314157824998880966853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3813542771883332587311235 5720314157824998880966853)
                    ·
                      refine ⟨1072558904592187290181285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5720314157824998880966853 1072558904592187290181285)
                      ·
                        rfl

theorem cell23_2088801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_2088801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088801 prefixEnd_2088801 := by exact prefixLift 2088801
  have htrace : WordTrace (prefixWord ++ tailWord_2088801) baseStart_2088801 baseEnd_2088801 := by
    simpa [prefixWord, tailWord_2088801, baseEnd_2088801] using wordTrace_append hprefix tailTrace_2088801
  have hstable : (prefixWord ++ tailWord_2088801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088801).length < 2 ^ (prefixWord ++ tailWord_2088801).sum := by decide
  have hdescent : baseEnd_2088801 < baseStart_2088801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088864 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 5]
def baseStart_2088864 : Nat := 118140960795 + 2088864 * 2 ^ 59
def prefixEnd_2088864 : Nat := 4983230072969 + 3 ^ 40 * 2088864 * 2
def baseEnd_2088864 : Nat := 1072591253873420543693495

theorem tailTrace_2088864 : CollatzResearch.WordTrace tailWord_2088864 prefixEnd_2088864 1072591253873420543693495 := by
  unfold tailWord_2088864
  simp only [CollatzResearch.WordTrace]
  refine ⟨38093564552204976207012823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50791419402939968276017097 38093564552204976207012823)
  ·
    refine ⟨57140346828307464310519235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38093564552204976207012823 57140346828307464310519235)
    ·
      refine ⟨85710520242461196465778853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57140346828307464310519235 85710520242461196465778853)
      ·
        refine ⟨16070722545461474337333535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85710520242461196465778853 16070722545461474337333535)
        ·
          refine ⟨24106083818192211506000303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16070722545461474337333535 24106083818192211506000303)
          ·
            refine ⟨36159125727288317259000455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24106083818192211506000303 36159125727288317259000455)
            ·
              refine ⟨54238688590932475888500683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36159125727288317259000455 54238688590932475888500683)
              ·
                refine ⟨81358032886398713832751025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54238688590932475888500683 81358032886398713832751025)
                ·
                  refine ⟨61018524664799035374563269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81358032886398713832751025 61018524664799035374563269)
                  ·
                    refine ⟨11440973374649819132730613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61018524664799035374563269 11440973374649819132730613)
                    ·
                      refine ⟨1072591253873420543693495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11440973374649819132730613 1072591253873420543693495)
                      ·
                        rfl

theorem cell23_2088864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_2088864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088864 prefixEnd_2088864 := by exact prefixLift 2088864
  have htrace : WordTrace (prefixWord ++ tailWord_2088864) baseStart_2088864 baseEnd_2088864 := by
    simpa [prefixWord, tailWord_2088864, baseEnd_2088864] using wordTrace_append hprefix tailTrace_2088864
  have hstable : (prefixWord ++ tailWord_2088864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088864).length < 2 ^ (prefixWord ++ tailWord_2088864).sum := by decide
  have hdescent : baseEnd_2088864 < baseStart_2088864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088885 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_2088885 : Nat := 118140960795 + 2088885 * 2 ^ 59
def prefixEnd_2088885 : Nat := 4983230072969 + 3 ^ 40 * 2088885 * 2
def baseEnd_2088885 : Nat := 1072602036967164961530899

theorem tailTrace_2088885 : CollatzResearch.WordTrace tailWord_2088885 prefixEnd_2088885 1072602036967164961530899 := by
  unfold tailWord_2088885
  simp only [CollatzResearch.WordTrace]
  refine ⟨76187895037333873000540109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50791930024889248667026739 76187895037333873000540109)
  ·
    refine ⟨28570460639000202375202541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76187895037333873000540109 28570460639000202375202541)
    ·
      refine ⟨10713922739625075890700953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28570460639000202375202541 10713922739625075890700953)
      ·
        refine ⟨8035442054718806918025715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10713922739625075890700953 8035442054718806918025715)
        ·
          refine ⟨12053163082078210377038573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8035442054718806918025715 12053163082078210377038573)
          ·
            refine ⟨4519936155779328891389465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12053163082078210377038573 4519936155779328891389465)
            ·
              refine ⟨3389952116834496668542099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4519936155779328891389465 3389952116834496668542099)
              ·
                refine ⟨5084928175251745002813149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3389952116834496668542099 5084928175251745002813149)
                ·
                  refine ⟨1906848065719404376054931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5084928175251745002813149 1906848065719404376054931)
                  ·
                    refine ⟨2860272098579106564082397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1906848065719404376054931 2860272098579106564082397)
                    ·
                      refine ⟨1072602036967164961530899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2860272098579106564082397 1072602036967164961530899)
                      ·
                        rfl

theorem cell23_2088885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_2088885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088885 prefixEnd_2088885 := by exact prefixLift 2088885
  have htrace : WordTrace (prefixWord ++ tailWord_2088885) baseStart_2088885 baseEnd_2088885 := by
    simpa [prefixWord, tailWord_2088885, baseEnd_2088885] using wordTrace_append hprefix tailTrace_2088885
  have hstable : (prefixWord ++ tailWord_2088885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088885).length < 2 ^ (prefixWord ++ tailWord_2088885).sum := by decide
  have hdescent : baseEnd_2088885 < baseStart_2088885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088891 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 2, 6, 2]
def baseStart_2088891 : Nat := 118140960795 + 2088891 * 2 ^ 59
def prefixEnd_2088891 : Nat := 4983230072969 + 3 ^ 40 * 2088891 * 2
def baseEnd_2088891 : Nat := 1072605117851091938055871

theorem tailTrace_2088891 : CollatzResearch.WordTrace tailWord_2088891 prefixEnd_2088891 1072605117851091938055871 := by
  unfold tailWord_2088891
  simp only [CollatzResearch.WordTrace]
  refine ⟨76188113875312136025258527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50792075916874757350172351 76188113875312136025258527)
  ·
    refine ⟨114282170812968204037887791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76188113875312136025258527 114282170812968204037887791)
    ·
      refine ⟨171423256219452306056831687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114282170812968204037887791 171423256219452306056831687)
      ·
        refine ⟨257134884329178459085247531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171423256219452306056831687 257134884329178459085247531)
        ·
          refine ⟨385702326493767688627871297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257134884329178459085247531 385702326493767688627871297)
          ·
            refine ⟨289276744870325766470903473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385702326493767688627871297 289276744870325766470903473)
            ·
              refine ⟨216957558652744324853177605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289276744870325766470903473 216957558652744324853177605)
              ·
                refine ⟨40679542247389560909970801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216957558652744324853177605 40679542247389560909970801)
                ·
                  refine ⟨30509656685542170682478101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40679542247389560909970801 30509656685542170682478101)
                  ·
                    refine ⟨1430140157134789250741161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30509656685542170682478101 1430140157134789250741161)
                    ·
                      refine ⟨1072605117851091938055871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1430140157134789250741161 1072605117851091938055871)
                      ·
                        rfl

theorem cell23_2088891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 6, 2].length) (baseStart_2088891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088891 prefixEnd_2088891 := by exact prefixLift 2088891
  have htrace : WordTrace (prefixWord ++ tailWord_2088891) baseStart_2088891 baseEnd_2088891 := by
    simpa [prefixWord, tailWord_2088891, baseEnd_2088891] using wordTrace_append hprefix tailTrace_2088891
  have hstable : (prefixWord ++ tailWord_2088891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088891).length < 2 ^ (prefixWord ++ tailWord_2088891).sum := by decide
  have hdescent : baseEnd_2088891 < baseStart_2088891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088908 : List Nat := [2, 2, 1, 4, 1, 2, 1, 4, 1, 1, 4]
def baseStart_2088908 : Nat := 118140960795 + 2088908 * 2 ^ 59
def prefixEnd_2088908 : Nat := 4983230072969 + 3 ^ 40 * 2088908 * 2
def baseEnd_2088908 : Nat := 1072613847022218371543293

theorem tailTrace_2088908 : CollatzResearch.WordTrace tailWord_2088908 prefixEnd_2088908 1072613847022218371543293 := by
  unfold tailWord_2088908
  simp only [CollatzResearch.WordTrace]
  refine ⟨38094366958125273964313689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50792489277500365285751585 38094366958125273964313689)
  ·
    refine ⟨28570775218593955473235267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38094366958125273964313689 28570775218593955473235267)
    ·
      refine ⟨42856162827890933209852901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28570775218593955473235267 42856162827890933209852901)
      ·
        refine ⟨8035530530229549976847419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42856162827890933209852901 8035530530229549976847419)
        ·
          refine ⟨12053295795344324965271129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8035530530229549976847419 12053295795344324965271129)
          ·
            refine ⟨9039971846508243723953347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12053295795344324965271129 9039971846508243723953347)
            ·
              refine ⟨13559957769762365585930021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9039971846508243723953347 13559957769762365585930021)
              ·
                refine ⟨2542492081830443547361879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13559957769762365585930021 2542492081830443547361879)
                ·
                  refine ⟨3813738122745665321042819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542492081830443547361879 3813738122745665321042819)
                  ·
                    refine ⟨5720607184118497981564229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3813738122745665321042819 5720607184118497981564229)
                    ·
                      refine ⟨1072613847022218371543293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5720607184118497981564229 1072613847022218371543293)
                      ·
                        rfl

theorem cell23_2088908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_2088908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088908 prefixEnd_2088908 := by exact prefixLift 2088908
  have htrace : WordTrace (prefixWord ++ tailWord_2088908) baseStart_2088908 baseEnd_2088908 := by
    simpa [prefixWord, tailWord_2088908, baseEnd_2088908] using wordTrace_append hprefix tailTrace_2088908
  have hstable : (prefixWord ++ tailWord_2088908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088908).length < 2 ^ (prefixWord ++ tailWord_2088908).sum := by decide
  have hdescent : baseEnd_2088908 < baseStart_2088908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088931 : List Nat := [1, 1, 1, 6, 1, 4, 9]
def baseStart_2088931 : Nat := 118140960795 + 2088931 * 2 ^ 59
def prefixEnd_2088931 : Nat := 4983230072969 + 3 ^ 40 * 2088931 * 2
def baseEnd_2088931 : Nat := 13242292062682367673527

theorem tailTrace_2088931 : CollatzResearch.WordTrace tailWord_2088931 prefixEnd_2088931 13242292062682367673527 := by
  unfold tailWord_2088931
  simp only [CollatzResearch.WordTrace]
  refine ⟨76189572795167222856714647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50793048530111481904476431 76189572795167222856714647)
  ·
    refine ⟨114284359192750834285071971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76189572795167222856714647 114284359192750834285071971)
    ·
      refine ⟨171426538789126251427607957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114284359192750834285071971 171426538789126251427607957)
      ·
        refine ⟨8035619005740293035669123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171426538789126251427607957 8035619005740293035669123)
        ·
          refine ⟨12053428508610439553503685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8035619005740293035669123 12053428508610439553503685)
          ·
            refine ⟨2260017845364457416281941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12053428508610439553503685 2260017845364457416281941)
            ·
              refine ⟨13242292062682367673527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2260017845364457416281941 13242292062682367673527)
              ·
                rfl

theorem cell23_2088931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 9].length) (baseStart_2088931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088931 prefixEnd_2088931 := by exact prefixLift 2088931
  have htrace : WordTrace (prefixWord ++ tailWord_2088931) baseStart_2088931 baseEnd_2088931 := by
    simpa [prefixWord, tailWord_2088931, baseEnd_2088931] using wordTrace_append hprefix tailTrace_2088931
  have hstable : (prefixWord ++ tailWord_2088931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088931).length < 2 ^ (prefixWord ++ tailWord_2088931).sum := by decide
  have hdescent : baseEnd_2088931 < baseStart_2088931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088942 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_2088942 : Nat := 118140960795 + 2088942 * 2 ^ 59
def prefixEnd_2088942 : Nat := 4983230072969 + 3 ^ 40 * 2088942 * 2
def baseEnd_2088942 : Nat := 1072631305364471238518137

theorem tailTrace_2088942 : CollatzResearch.WordTrace tailWord_2088942 prefixEnd_2088942 1072631305364471238518137 := by
  unfold tailWord_2088942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9523746749765921466920635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50793315998751581156910053 9523746749765921466920635)
  ·
    refine ⟨14285620124648882200380953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9523746749765921466920635 14285620124648882200380953)
    ·
      refine ⟨10714215093486661650285715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14285620124648882200380953 10714215093486661650285715)
      ·
        refine ⟨16071322640229992475428573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10714215093486661650285715 16071322640229992475428573)
        ·
          refine ⟨6026745990086247178285715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16071322640229992475428573 6026745990086247178285715)
          ·
            refine ⟨9040118985129370767428573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6026745990086247178285715 9040118985129370767428573)
            ·
              refine ⟨3390044619423514037785715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9040118985129370767428573 3390044619423514037785715)
              ·
                refine ⟨5085066929135271056678573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390044619423514037785715 5085066929135271056678573)
                ·
                  refine ⟨1906900098425726646254465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5085066929135271056678573 1906900098425726646254465)
                  ·
                    refine ⟨1430175073819294984690849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1906900098425726646254465 1430175073819294984690849)
                    ·
                      refine ⟨1072631305364471238518137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1430175073819294984690849 1072631305364471238518137)
                      ·
                        rfl

theorem cell23_2088942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_2088942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088942 prefixEnd_2088942 := by exact prefixLift 2088942
  have htrace : WordTrace (prefixWord ++ tailWord_2088942) baseStart_2088942 baseEnd_2088942 := by
    simpa [prefixWord, tailWord_2088942, baseEnd_2088942] using wordTrace_append hprefix tailTrace_2088942
  have hstable : (prefixWord ++ tailWord_2088942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088942).length < 2 ^ (prefixWord ++ tailWord_2088942).sum := by decide
  have hdescent : baseEnd_2088942 < baseStart_2088942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088991 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 2, 6]
def baseStart_2088991 : Nat := 118140960795 + 2088991 * 2 ^ 59
def prefixEnd_2088991 : Nat := 4983230072969 + 3 ^ 40 * 2088991 * 2
def baseEnd_2088991 : Nat := 357552155305513848935137

theorem tailTrace_2088991 : CollatzResearch.WordTrace tailWord_2088991 prefixEnd_2088991 357552155305513848935137 := by
  unfold tailWord_2088991
  simp only [CollatzResearch.WordTrace]
  refine ⟨76191761174949853103898827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50794507449966568735932551 76191761174949853103898827)
  ·
    refine ⟨114287641762424779655848241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76191761174949853103898827 114287641762424779655848241)
    ·
      refine ⟨85715731321818584741886181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114287641762424779655848241 85715731321818584741886181)
      ·
        refine ⟨16071699622840984639103659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85715731321818584741886181 16071699622840984639103659)
        ·
          refine ⟨24107549434261476958655489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16071699622840984639103659 24107549434261476958655489)
          ·
            refine ⟨18080662075696107718991617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24107549434261476958655489 18080662075696107718991617)
            ·
              refine ⟨13560496556772080789243713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18080662075696107718991617 13560496556772080789243713)
              ·
                refine ⟨10170372417579060591932785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13560496556772080789243713 10170372417579060591932785)
                ·
                  refine ⟨7627779313184295443949589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10170372417579060591932785 7627779313184295443949589)
                  ·
                    refine ⟨357552155305513848935137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7627779313184295443949589 357552155305513848935137)
                    ·
                      rfl

theorem cell23_2088991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 6].length) (baseStart_2088991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088991 prefixEnd_2088991 := by exact prefixLift 2088991
  have htrace : WordTrace (prefixWord ++ tailWord_2088991) baseStart_2088991 baseEnd_2088991 := by
    simpa [prefixWord, tailWord_2088991, baseEnd_2088991] using wordTrace_append hprefix tailTrace_2088991
  have hstable : (prefixWord ++ tailWord_2088991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088991).length < 2 ^ (prefixWord ++ tailWord_2088991).sum := by decide
  have hdescent : baseEnd_2088991 < baseStart_2088991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088993 : List Nat := [1, 2, 3, 2, 5, 1, 2, 2, 1, 2, 2]
def baseStart_2088993 : Nat := 118140960795 + 2088993 * 2 ^ 59
def prefixEnd_2088993 : Nat := 4983230072969 + 3 ^ 40 * 2088993 * 2
def baseEnd_2088993 : Nat := 1072657492877850538980403

theorem tailTrace_2088993 : CollatzResearch.WordTrace tailWord_2088993 prefixEnd_2088993 1072657492877850538980403 := by
  unfold tailWord_2088993
  simp only [CollatzResearch.WordTrace]
  refine ⟨76191834120942607445471633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50794556080628404963647755 76191834120942607445471633)
  ·
    refine ⟨57143875590706955584103725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76191834120942607445471633 57143875590706955584103725)
    ·
      refine ⟨21428953346515108344038897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57143875590706955584103725 21428953346515108344038897)
      ·
        refine ⟨16071715009886331258029173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21428953346515108344038897 16071715009886331258029173)
        ·
          refine ⟨1506723282176843555440235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16071715009886331258029173 1506723282176843555440235)
          ·
            refine ⟨2260084923265265333160353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506723282176843555440235 2260084923265265333160353)
            ·
              refine ⟨1695063692448948999870265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2260084923265265333160353 1695063692448948999870265)
              ·
                refine ⟨1271297769336711749902699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1695063692448948999870265 1271297769336711749902699)
                ·
                  refine ⟨1906946654005067624854049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1271297769336711749902699 1906946654005067624854049)
                  ·
                    refine ⟨1430209990503800718640537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1906946654005067624854049 1430209990503800718640537)
                    ·
                      refine ⟨1072657492877850538980403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1430209990503800718640537 1072657492877850538980403)
                      ·
                        rfl

theorem cell23_2088993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_2088993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2088993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2088993 prefixEnd_2088993 := by exact prefixLift 2088993
  have htrace : WordTrace (prefixWord ++ tailWord_2088993) baseStart_2088993 baseEnd_2088993 := by
    simpa [prefixWord, tailWord_2088993, baseEnd_2088993] using wordTrace_append hprefix tailTrace_2088993
  have hstable : (prefixWord ++ tailWord_2088993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088993).length < 2 ^ (prefixWord ++ tailWord_2088993).sum := by decide
  have hdescent : baseEnd_2088993 < baseStart_2088993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089011 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 4]
def baseStart_2089011 : Nat := 118140960795 + 2089011 * 2 ^ 59
def prefixEnd_2089011 : Nat := 4983230072969 + 3 ^ 40 * 2089011 * 2
def baseEnd_2089011 : Nat := 1072666735529631468555319

theorem tailTrace_2089011 : CollatzResearch.WordTrace tailWord_2089011 prefixEnd_2089011 1072666735529631468555319 := by
  unfold tailWord_2089011
  simp only [CollatzResearch.WordTrace]
  refine ⟨76192490634877396519626887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50794993756584931013084591 76192490634877396519626887)
  ·
    refine ⟨114288735952316094779440331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76192490634877396519626887 114288735952316094779440331)
    ·
      refine ⟨171433103928474142169160497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114288735952316094779440331 171433103928474142169160497)
      ·
        refine ⟨128574827946355606626870373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171433103928474142169160497 128574827946355606626870373)
        ·
          refine ⟨24107780239941676242538195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128574827946355606626870373 24107780239941676242538195)
          ·
            refine ⟨36161670359912514363807293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24107780239941676242538195 36161670359912514363807293)
            ·
              refine ⟨13560626384967192886427735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36161670359912514363807293 13560626384967192886427735)
              ·
                refine ⟨20340939577450789329641603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13560626384967192886427735 20340939577450789329641603)
                ·
                  refine ⟨30511409366176183994462405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20340939577450789329641603 30511409366176183994462405)
                  ·
                    refine ⟨5720889256158034498961701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30511409366176183994462405 5720889256158034498961701)
                    ·
                      refine ⟨1072666735529631468555319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5720889256158034498961701 1072666735529631468555319)
                      ·
                        rfl

theorem cell23_2089011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_2089011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089011 prefixEnd_2089011 := by exact prefixLift 2089011
  have htrace : WordTrace (prefixWord ++ tailWord_2089011) baseStart_2089011 baseEnd_2089011 := by
    simpa [prefixWord, tailWord_2089011, baseEnd_2089011] using wordTrace_append hprefix tailTrace_2089011
  have hstable : (prefixWord ++ tailWord_2089011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089011).length < 2 ^ (prefixWord ++ tailWord_2089011).sum := by decide
  have hdescent : baseEnd_2089011 < baseStart_2089011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089048 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 2, 3, 3]
def baseStart_2089048 : Nat := 118140960795 + 2089048 * 2 ^ 59
def prefixEnd_2089048 : Nat := 4983230072969 + 3 ^ 40 * 2089048 * 2
def baseEnd_2089048 : Nat := 1072685734313847823792649

theorem tailTrace_2089048 : CollatzResearch.WordTrace tailWord_2089048 prefixEnd_2089048 1072685734313847823792649 := by
  unfold tailWord_2089048
  simp only [CollatzResearch.WordTrace]
  refine ⟨38096920067871675919361899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50795893423828901225815865 38096920067871675919361899)
  ·
    refine ⟨57145380101807513879042849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38096920067871675919361899 57145380101807513879042849)
    ·
      refine ⟨42859035076355635409282137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57145380101807513879042849 42859035076355635409282137)
      ·
        refine ⟨32144276307266726556961603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42859035076355635409282137 32144276307266726556961603)
        ·
          refine ⟨48216414460900089835442405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32144276307266726556961603 48216414460900089835442405)
          ·
            refine ⟨9040577711418766844145451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48216414460900089835442405 9040577711418766844145451)
            ·
              refine ⟨13560866567128150266218177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9040577711418766844145451 13560866567128150266218177)
              ·
                refine ⟨10170649925346112699663633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13560866567128150266218177 10170649925346112699663633)
                ·
                  refine ⟨7627987444009584524747725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10170649925346112699663633 7627987444009584524747725)
                  ·
                    refine ⟨2860495291503594196780397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7627987444009584524747725 2860495291503594196780397)
                    ·
                      refine ⟨1072685734313847823792649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2860495291503594196780397 1072685734313847823792649)
                      ·
                        rfl

theorem cell23_2089048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_2089048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089048 prefixEnd_2089048 := by exact prefixLift 2089048
  have htrace : WordTrace (prefixWord ++ tailWord_2089048) baseStart_2089048 baseEnd_2089048 := by
    simpa [prefixWord, tailWord_2089048, baseEnd_2089048] using wordTrace_append hprefix tailTrace_2089048
  have hstable : (prefixWord ++ tailWord_2089048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089048).length < 2 ^ (prefixWord ++ tailWord_2089048).sum := by decide
  have hdescent : baseEnd_2089048 < baseStart_2089048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089066 : List Nat := [3, 1, 3, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_2089066 : Nat := 118140960795 + 2089066 * 2 ^ 59
def prefixEnd_2089066 : Nat := 4983230072969 + 3 ^ 40 * 2089066 * 2
def baseEnd_2089066 : Nat := 1072694976965628753367567

theorem tailTrace_2089066 : CollatzResearch.WordTrace tailWord_2089066 prefixEnd_2089066 1072694976965628753367567 := by
  unfold tailWord_2089066
  simp only [CollatzResearch.WordTrace]
  refine ⟨19048624162419535228219763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50796331099785427275252701 19048624162419535228219763)
  ·
    refine ⟨28572936243629302842329645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19048624162419535228219763 28572936243629302842329645)
    ·
      refine ⟨10714851091360988565873617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28572936243629302842329645 10714851091360988565873617)
      ·
        refine ⟨8036138318520741424405213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10714851091360988565873617 8036138318520741424405213)
        ·
          refine ⟨3013551869445278034151955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8036138318520741424405213 3013551869445278034151955)
          ·
            refine ⟨4520327804167917051227933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3013551869445278034151955 4520327804167917051227933)
            ·
              refine ⟨1695122926562968894210475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4520327804167917051227933 1695122926562968894210475)
              ·
                refine ⟨2542684389844453341315713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695122926562968894210475 2542684389844453341315713)
                ·
                  refine ⟨1907013292383340005986785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2542684389844453341315713 1907013292383340005986785)
                  ·
                    refine ⟨1430259969287505004490089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1907013292383340005986785 1430259969287505004490089)
                    ·
                      refine ⟨1072694976965628753367567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1430259969287505004490089 1072694976965628753367567)
                      ·
                        rfl

theorem cell23_2089066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_2089066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089066 prefixEnd_2089066 := by exact prefixLift 2089066
  have htrace : WordTrace (prefixWord ++ tailWord_2089066) baseStart_2089066 baseEnd_2089066 := by
    simpa [prefixWord, tailWord_2089066, baseEnd_2089066] using wordTrace_append hprefix tailTrace_2089066
  have hstable : (prefixWord ++ tailWord_2089066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089066).length < 2 ^ (prefixWord ++ tailWord_2089066).sum := by decide
  have hdescent : baseEnd_2089066 < baseStart_2089066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089088 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 4]
def baseStart_2089088 : Nat := 118140960795 + 2089088 * 2 ^ 59
def prefixEnd_2089088 : Nat := 4983230072969 + 3 ^ 40 * 2089088 * 2
def baseEnd_2089088 : Nat := 1072706273540027667292465

theorem tailTrace_2089088 : CollatzResearch.WordTrace tailWord_2089088 prefixEnd_2089088 1072706273540027667292465 := by
  unfold tailWord_2089088
  simp only [CollatzResearch.WordTrace]
  refine ⟨38097649527799219335089959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50796866037065625780119945 38097649527799219335089959)
  ·
    refine ⟨57146474291698829002634939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38097649527799219335089959 57146474291698829002634939)
    ·
      refine ⟨85719711437548243503952409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57146474291698829002634939 85719711437548243503952409)
      ·
        refine ⟨64289783578161182627964307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85719711437548243503952409 64289783578161182627964307)
        ·
          refine ⟨96434675367241773941946461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64289783578161182627964307 96434675367241773941946461)
          ·
            refine ⟨36163003262715665228229923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96434675367241773941946461 36163003262715665228229923)
            ·
              refine ⟨54244504894073497842344885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36163003262715665228229923 54244504894073497842344885)
              ·
                refine ⟨5085422333819390422719833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54244504894073497842344885 5085422333819390422719833)
                ·
                  refine ⟨3814066750364542817039875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5085422333819390422719833 3814066750364542817039875)
                  ·
                    refine ⟨5721100125546814225559813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3814066750364542817039875 5721100125546814225559813)
                    ·
                      refine ⟨1072706273540027667292465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5721100125546814225559813 1072706273540027667292465)
                      ·
                        rfl

theorem cell23_2089088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_2089088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089088 prefixEnd_2089088 := by exact prefixLift 2089088
  have htrace : WordTrace (prefixWord ++ tailWord_2089088) baseStart_2089088 baseEnd_2089088 := by
    simpa [prefixWord, tailWord_2089088, baseEnd_2089088] using wordTrace_append hprefix tailTrace_2089088
  have hstable : (prefixWord ++ tailWord_2089088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089088).length < 2 ^ (prefixWord ++ tailWord_2089088).sum := by decide
  have hdescent : baseEnd_2089088 < baseStart_2089088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089089 : List Nat := [1, 2, 4, 2, 4, 1, 1, 3, 5]
def baseStart_2089089 : Nat := 118140960795 + 2089089 * 2 ^ 59
def prefixEnd_2089089 : Nat := 4983230072969 + 3 ^ 40 * 2089089 * 2
def baseEnd_2089089 : Nat := 119189643002298018153329

theorem tailTrace_2089089 : CollatzResearch.WordTrace tailWord_2089089 prefixEnd_2089089 119189643002298018153329 := by
  unfold tailWord_2089089
  simp only [CollatzResearch.WordTrace]
  refine ⟨76195335528594815840966321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50796890352396543893977547 76195335528594815840966321)
  ·
    refine ⟨57146501646446111880724741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76195335528594815840966321 57146501646446111880724741)
    ·
      refine ⟨10714969058708645977635889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57146501646446111880724741 10714969058708645977635889)
      ·
        refine ⟨8036226794031484483226917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10714969058708645977635889 8036226794031484483226917)
        ·
          refine ⟨1506792523880903340605047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8036226794031484483226917 1506792523880903340605047)
          ·
            refine ⟨2260188785821355010907571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506792523880903340605047 2260188785821355010907571)
            ·
              refine ⟨3390283178732032516361357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260188785821355010907571 3390283178732032516361357)
              ·
                refine ⟨1271356192024512193635509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3390283178732032516361357 1271356192024512193635509)
                ·
                  refine ⟨119189643002298018153329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1271356192024512193635509 119189643002298018153329)
                  ·
                    rfl

theorem cell23_2089089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 5].length) (baseStart_2089089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089089 prefixEnd_2089089 := by exact prefixLift 2089089
  have htrace : WordTrace (prefixWord ++ tailWord_2089089) baseStart_2089089 baseEnd_2089089 := by
    simpa [prefixWord, tailWord_2089089, baseEnd_2089089] using wordTrace_append hprefix tailTrace_2089089
  have hstable : (prefixWord ++ tailWord_2089089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089089).length < 2 ^ (prefixWord ++ tailWord_2089089).sum := by decide
  have hdescent : baseEnd_2089089 < baseStart_2089089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089131 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 8]
def baseStart_2089131 : Nat := 118140960795 + 2089131 * 2 ^ 59
def prefixEnd_2089131 : Nat := 4983230072969 + 3 ^ 40 * 2089131 * 2
def baseEnd_2089131 : Nat := 1072728353208170999054767

theorem tailTrace_2089131 : CollatzResearch.WordTrace tailWord_2089131 prefixEnd_2089131 1072728353208170999054767 := by
  unfold tailWord_2089131
  simp only [CollatzResearch.WordTrace]
  refine ⟨76196867394442657013995247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50797911596295104675996831 76196867394442657013995247)
  ·
    refine ⟨114295301091663985520992871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76196867394442657013995247 114295301091663985520992871)
    ·
      refine ⟨171442951637495978281489307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114295301091663985520992871 171442951637495978281489307)
      ·
        refine ⟨257164427456243967422233961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171442951637495978281489307 257164427456243967422233961)
        ·
          refine ⟨192873320592182975566675471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257164427456243967422233961 192873320592182975566675471)
          ·
            refine ⟨289309980888274463350013207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192873320592182975566675471 289309980888274463350013207)
            ·
              refine ⟨433964971332411695025019811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289309980888274463350013207 433964971332411695025019811)
              ·
                refine ⟨650947456998617542537529717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433964971332411695025019811 650947456998617542537529717)
                ·
                  refine ⟨61026324093620394612893411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 650947456998617542537529717 61026324093620394612893411)
                  ·
                    refine ⟨91539486140430591919340117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61026324093620394612893411 91539486140430591919340117)
                    ·
                      refine ⟨1072728353208170999054767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 91539486140430591919340117 1072728353208170999054767)
                      ·
                        rfl

theorem cell23_2089131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_2089131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089131 prefixEnd_2089131 := by exact prefixLift 2089131
  have htrace : WordTrace (prefixWord ++ tailWord_2089131) baseStart_2089131 baseEnd_2089131 := by
    simpa [prefixWord, tailWord_2089131, baseEnd_2089131] using wordTrace_append hprefix tailTrace_2089131
  have hstable : (prefixWord ++ tailWord_2089131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089131).length < 2 ^ (prefixWord ++ tailWord_2089131).sum := by decide
  have hdescent : baseEnd_2089131 < baseStart_2089131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089166 : List Nat := [4, 1, 1, 1, 4, 3, 2, 2, 1, 4]
def baseStart_2089166 : Nat := 118140960795 + 2089166 * 2 ^ 59
def prefixEnd_2089166 : Nat := 4983230072969 + 3 ^ 40 * 2089166 * 2
def baseEnd_2089166 : Nat := 357582108343692787372369

theorem tailTrace_2089166 : CollatzResearch.WordTrace tailWord_2089166 prefixEnd_2089166 357582108343692787372369 := by
  unfold tailWord_2089166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9524767993664482248939919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50798762632877238661012901 9524767993664482248939919)
  ·
    refine ⟨14287151990496723373409879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9524767993664482248939919 14287151990496723373409879)
    ·
      refine ⟨21430727985745085060114819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14287151990496723373409879 21430727985745085060114819)
      ·
        refine ⟨32146091978617627590172229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21430727985745085060114819 32146091978617627590172229)
        ·
          refine ⟨6027392245990805173157293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32146091978617627590172229 6027392245990805173157293)
          ·
            refine ⟨2260272092246551939933985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6027392245990805173157293 2260272092246551939933985)
            ·
              refine ⟨1695204069184913954950489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2260272092246551939933985 1695204069184913954950489)
              ·
                refine ⟨1271403051888685466212867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1695204069184913954950489 1271403051888685466212867)
                ·
                  refine ⟨1907104577833028199319301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1271403051888685466212867 1907104577833028199319301)
                  ·
                    refine ⟨357582108343692787372369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1907104577833028199319301 357582108343692787372369)
                    ·
                      rfl

theorem cell23_2089166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_2089166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089166 prefixEnd_2089166 := by exact prefixLift 2089166
  have htrace : WordTrace (prefixWord ++ tailWord_2089166) baseStart_2089166 baseEnd_2089166 := by
    simpa [prefixWord, tailWord_2089166, baseEnd_2089166] using wordTrace_append hprefix tailTrace_2089166
  have hstable : (prefixWord ++ tailWord_2089166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089166).length < 2 ^ (prefixWord ++ tailWord_2089166).sum := by decide
  have hdescent : baseEnd_2089166 < baseStart_2089166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089195 : List Nat := [1, 1, 1, 1, 2, 5, 2, 4, 1, 1, 4]
def baseStart_2089195 : Nat := 118140960795 + 2089195 * 2 ^ 59
def prefixEnd_2089195 : Nat := 4983230072969 + 3 ^ 40 * 2089195 * 2
def baseEnd_2089195 : Nat := 1072761215970058748654473

theorem tailTrace_2089195 : CollatzResearch.WordTrace tailWord_2089195 prefixEnd_2089195 1072761215970058748654473 := by
  unfold tailWord_2089195
  simp only [CollatzResearch.WordTrace]
  refine ⟨76199201666210795944325039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50799467777473863962883359 76199201666210795944325039)
  ·
    refine ⟨114298802499316193916487559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76199201666210795944325039 114298802499316193916487559)
    ·
      refine ⟨171448203748974290874731339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114298802499316193916487559 171448203748974290874731339)
      ·
        refine ⟨257172305623461436312097009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171448203748974290874731339 257172305623461436312097009)
        ·
          refine ⟨192879229217596077234072757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257172305623461436312097009 192879229217596077234072757)
          ·
            refine ⟨18082427739149632240694321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192879229217596077234072757 18082427739149632240694321)
            ·
              refine ⟨13561820804362224180520741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18082427739149632240694321 13561820804362224180520741)
              ·
                refine ⟨2542841400817917033847639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13561820804362224180520741 2542841400817917033847639)
                ·
                  refine ⟨3814262101226875550771459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542841400817917033847639 3814262101226875550771459)
                  ·
                    refine ⟨5721393151840313326157189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3814262101226875550771459 5721393151840313326157189)
                    ·
                      refine ⟨1072761215970058748654473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5721393151840313326157189 1072761215970058748654473)
                      ·
                        rfl

theorem cell23_2089195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 1, 4].length) (baseStart_2089195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089195 prefixEnd_2089195 := by exact prefixLift 2089195
  have htrace : WordTrace (prefixWord ++ tailWord_2089195) baseStart_2089195 baseEnd_2089195 := by
    simpa [prefixWord, tailWord_2089195, baseEnd_2089195] using wordTrace_append hprefix tailTrace_2089195
  have hstable : (prefixWord ++ tailWord_2089195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089195).length < 2 ^ (prefixWord ++ tailWord_2089195).sum := by decide
  have hdescent : baseEnd_2089195 < baseStart_2089195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089199 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 2, 3, 2]
def baseStart_2089199 : Nat := 118140960795 + 2089199 * 2 ^ 59
def prefixEnd_2089199 : Nat := 4983230072969 + 3 ^ 40 * 2089199 * 2
def baseEnd_2089199 : Nat := 1072763269892676733004455

theorem tailTrace_2089199 : CollatzResearch.WordTrace tailWord_2089199 prefixEnd_2089199 1072763269892676733004455 := by
  unfold tailWord_2089199
  simp only [CollatzResearch.WordTrace]
  refine ⟨76199347558196304627470651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50799565038797536418313767 76199347558196304627470651)
  ·
    refine ⟨114299021337294456941205977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76199347558196304627470651 114299021337294456941205977)
    ·
      refine ⟨85724266002970842705904483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114299021337294456941205977 85724266002970842705904483)
      ·
        refine ⟨128586399004456264058856725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85724266002970842705904483 128586399004456264058856725)
        ·
          refine ⟨6027487453333887377758909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128586399004456264058856725 6027487453333887377758909)
          ·
            refine ⟨2260307795000207766659591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6027487453333887377758909 2260307795000207766659591)
            ·
              refine ⟨3390461692500311649989387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260307795000207766659591 3390461692500311649989387)
              ·
                refine ⟨5085692538750467474984081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390461692500311649989387 5085692538750467474984081)
                ·
                  refine ⟨3814269404062850606238061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5085692538750467474984081 3814269404062850606238061)
                  ·
                    refine ⟨1430351026523568977339273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3814269404062850606238061 1430351026523568977339273)
                    ·
                      refine ⟨1072763269892676733004455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1430351026523568977339273 1072763269892676733004455)
                      ·
                        rfl

theorem cell23_2089199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 3, 2].length) (baseStart_2089199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089199 prefixEnd_2089199 := by exact prefixLift 2089199
  have htrace : WordTrace (prefixWord ++ tailWord_2089199) baseStart_2089199 baseEnd_2089199 := by
    simpa [prefixWord, tailWord_2089199, baseEnd_2089199] using wordTrace_append hprefix tailTrace_2089199
  have hstable : (prefixWord ++ tailWord_2089199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089199).length < 2 ^ (prefixWord ++ tailWord_2089199).sum := by decide
  have hdescent : baseEnd_2089199 < baseStart_2089199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089212 : List Nat := [2, 2, 2, 1, 4, 2, 1, 3, 1, 1, 4]
def baseStart_2089212 : Nat := 118140960795 + 2089212 * 2 ^ 59
def prefixEnd_2089212 : Nat := 4983230072969 + 3 ^ 40 * 2089212 * 2
def baseEnd_2089212 : Nat := 1072769945141185182141895

theorem tailTrace_2089212 : CollatzResearch.WordTrace tailWord_2089212 prefixEnd_2089212 1072769945141185182141895 := by
  unfold tailWord_2089212
  simp only [CollatzResearch.WordTrace]
  refine ⟨38099910853574603923846945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50799881138099471898462593 38099910853574603923846945)
  ·
    refine ⟨28574933140180952942885209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38099910853574603923846945 28574933140180952942885209)
    ·
      refine ⟨21431199855135714707163907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28574933140180952942885209 21431199855135714707163907)
      ·
        refine ⟨32146799782703572060745861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21431199855135714707163907 32146799782703572060745861)
        ·
          refine ⟨6027524959256919761389849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32146799782703572060745861 6027524959256919761389849)
          ·
            refine ⟨4520643719442689821042387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6027524959256919761389849 4520643719442689821042387)
            ·
              refine ⟨6780965579164034731563581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4520643719442689821042387 6780965579164034731563581)
              ·
                refine ⟨2542862092186513024336343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6780965579164034731563581 2542862092186513024336343)
                ·
                  refine ⟨3814293138279769536504515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542862092186513024336343 3814293138279769536504515)
                  ·
                    refine ⟨5721439707419654304756773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3814293138279769536504515 5721439707419654304756773)
                    ·
                      refine ⟨1072769945141185182141895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5721439707419654304756773 1072769945141185182141895)
                      ·
                        rfl

theorem cell23_2089212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_2089212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089212 prefixEnd_2089212 := by exact prefixLift 2089212
  have htrace : WordTrace (prefixWord ++ tailWord_2089212) baseStart_2089212 baseEnd_2089212 := by
    simpa [prefixWord, tailWord_2089212, baseEnd_2089212] using wordTrace_append hprefix tailTrace_2089212
  have hstable : (prefixWord ++ tailWord_2089212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089212).length < 2 ^ (prefixWord ++ tailWord_2089212).sum := by decide
  have hdescent : baseEnd_2089212 < baseStart_2089212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089239 : List Nat := [1, 1, 3, 4, 1, 3, 3, 1, 2, 4]
def baseStart_2089239 : Nat := 118140960795 + 2089239 * 2 ^ 59
def prefixEnd_2089239 : Nat := 4983230072969 + 3 ^ 40 * 2089239 * 2
def baseEnd_2089239 : Nat := 357594603039618858834757

theorem tailTrace_2089239 : CollatzResearch.WordTrace tailWord_2089239 prefixEnd_2089239 357594603039618858834757 := by
  unfold tailWord_2089239
  simp only [CollatzResearch.WordTrace]
  refine ⟨76200806478051391458926771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50800537652034260972617847 76200806478051391458926771)
  ·
    refine ⟨114301209717077087188390157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76200806478051391458926771 114301209717077087188390157)
    ·
      refine ⟨42862953643903907695646309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114301209717077087188390157 42862953643903907695646309)
      ·
        refine ⟨8036803808231982692933683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42862953643903907695646309 8036803808231982692933683)
        ·
          refine ⟨12055205712347974039400525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8036803808231982692933683 12055205712347974039400525)
          ·
            refine ⟨4520702142130490264775197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12055205712347974039400525 4520702142130490264775197)
            ·
              refine ⟨1695263303298933849290699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4520702142130490264775197 1695263303298933849290699)
              ·
                refine ⟨2542894954948400773936049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695263303298933849290699 2542894954948400773936049)
                ·
                  refine ⟨1907171216211300580452037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2542894954948400773936049 1907171216211300580452037)
                  ·
                    refine ⟨357594603039618858834757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1907171216211300580452037 357594603039618858834757)
                    ·
                      rfl

theorem cell23_2089239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_2089239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089239 prefixEnd_2089239 := by exact prefixLift 2089239
  have htrace : WordTrace (prefixWord ++ tailWord_2089239) baseStart_2089239 baseEnd_2089239 := by
    simpa [prefixWord, tailWord_2089239, baseEnd_2089239] using wordTrace_append hprefix tailTrace_2089239
  have hstable : (prefixWord ++ tailWord_2089239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089239).length < 2 ^ (prefixWord ++ tailWord_2089239).sum := by decide
  have hdescent : baseEnd_2089239 < baseStart_2089239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089246 : List Nat := [4, 3, 2, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2089246 : Nat := 118140960795 + 2089246 * 2 ^ 59
def prefixEnd_2089246 : Nat := 4983230072969 + 3 ^ 40 * 2089246 * 2
def baseEnd_2089246 : Nat := 1072787403483438049116739

theorem tailTrace_2089246 : CollatzResearch.WordTrace tailWord_2089246 prefixEnd_2089246 1072787403483438049116739 := by
  unfold tailWord_2089246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9525132723628253956803949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50800707859350687769621061 9525132723628253956803949)
  ·
    refine ⟨3571924771360595233801481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9525132723628253956803949 3571924771360595233801481)
    ·
      refine ⟨2678943578520446425351111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3571924771360595233801481 2678943578520446425351111)
      ·
        refine ⟨4018415367780669638026667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678943578520446425351111 4018415367780669638026667)
        ·
          refine ⟨6027623051671004457040001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018415367780669638026667 6027623051671004457040001)
          ·
            refine ⟨4520717288753253342780001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6027623051671004457040001 4520717288753253342780001)
            ·
              refine ⟨3390537966564940007085001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4520717288753253342780001 3390537966564940007085001)
              ·
                refine ⟨2542903474923705005313751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3390537966564940007085001 2542903474923705005313751)
                ·
                  refine ⟨3814355212385557507970627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542903474923705005313751 3814355212385557507970627)
                  ·
                    refine ⟨5721532818578336261955941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3814355212385557507970627 5721532818578336261955941)
                    ·
                      refine ⟨1072787403483438049116739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5721532818578336261955941 1072787403483438049116739)
                      ·
                        rfl

theorem cell23_2089246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2089246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089246 prefixEnd_2089246 := by exact prefixLift 2089246
  have htrace : WordTrace (prefixWord ++ tailWord_2089246) baseStart_2089246 baseEnd_2089246 := by
    simpa [prefixWord, tailWord_2089246, baseEnd_2089246] using wordTrace_append hprefix tailTrace_2089246
  have hstable : (prefixWord ++ tailWord_2089246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089246).length < 2 ^ (prefixWord ++ tailWord_2089246).sum := by decide
  have hdescent : baseEnd_2089246 < baseStart_2089246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089252 : List Nat := [2, 3, 1, 3, 1, 4, 2, 7]
def baseStart_2089252 : Nat := 118140960795 + 2089252 * 2 ^ 59
def prefixEnd_2089252 : Nat := 4983230072969 + 3 ^ 40 * 2089252 * 2
def baseEnd_2089252 : Nat := 39732980902495000949693

theorem tailTrace_2089252 : CollatzResearch.WordTrace tailWord_2089252 prefixEnd_2089252 39732980902495000949693 := by
  unfold tailWord_2089252
  simp only [CollatzResearch.WordTrace]
  refine ⟨38100640313502147339575005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50800853751336196452766673 38100640313502147339575005)
  ·
    refine ⟨14287740117563305252340627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38100640313502147339575005 14287740117563305252340627)
    ·
      refine ⟨21431610176344957878510941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14287740117563305252340627 21431610176344957878510941)
      ·
        refine ⟨8036853816129359204441603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21431610176344957878510941 8036853816129359204441603)
        ·
          refine ⟨12055280724194038806662405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8036853816129359204441603 12055280724194038806662405)
          ·
            refine ⟨2260365135786382276249201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12055280724194038806662405 2260365135786382276249201)
            ·
              refine ⟨1695273851839786707186901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2260365135786382276249201 1695273851839786707186901)
              ·
                refine ⟨39732980902495000949693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1695273851839786707186901 39732980902495000949693)
                ·
                  rfl

theorem cell23_2089252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 7].length) (baseStart_2089252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089252 prefixEnd_2089252 := by exact prefixLift 2089252
  have htrace : WordTrace (prefixWord ++ tailWord_2089252) baseStart_2089252 baseEnd_2089252 := by
    simpa [prefixWord, tailWord_2089252, baseEnd_2089252] using wordTrace_append hprefix tailTrace_2089252
  have hstable : (prefixWord ++ tailWord_2089252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089252).length < 2 ^ (prefixWord ++ tailWord_2089252).sum := by decide
  have hdescent : baseEnd_2089252 < baseStart_2089252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089296 : List Nat := [2, 1, 1, 1, 1, 8, 2, 1, 2, 1, 3]
def baseStart_2089296 : Nat := 118140960795 + 2089296 * 2 ^ 59
def prefixEnd_2089296 : Nat := 4983230072969 + 3 ^ 40 * 2089296 * 2
def baseEnd_2089296 : Nat := 1072813077516162853491509

theorem tailTrace_2089296 : CollatzResearch.WordTrace tailWord_2089296 prefixEnd_2089296 1072813077516162853491509 := by
  unfold tailWord_2089296
  simp only [CollatzResearch.WordTrace]
  refine ⟨38101442719422445096875871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50801923625896593462501161 38101442719422445096875871)
  ·
    refine ⟨57152164079133667645313807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38101442719422445096875871 57152164079133667645313807)
    ·
      refine ⟨85728246118700501467970711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57152164079133667645313807 85728246118700501467970711)
      ·
        refine ⟨128592369178050752201956067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85728246118700501467970711 128592369178050752201956067)
        ·
          refine ⟨192888553767076128302934101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128592369178050752201956067 192888553767076128302934101)
          ·
            refine ⟨2260412739457923378550009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 192888553767076128302934101 2260412739457923378550009)
            ·
              refine ⟨1695309554593442533912507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2260412739457923378550009 1695309554593442533912507)
              ·
                refine ⟨2542964331890163800868761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695309554593442533912507 2542964331890163800868761)
                ·
                  refine ⟨1907223248917622850651571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2542964331890163800868761 1907223248917622850651571)
                  ·
                    refine ⟨2860834873376434275977357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1907223248917622850651571 2860834873376434275977357)
                    ·
                      refine ⟨1072813077516162853491509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2860834873376434275977357 1072813077516162853491509)
                      ·
                        rfl

theorem cell23_2089296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 2, 1, 3].length) (baseStart_2089296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089296 prefixEnd_2089296 := by exact prefixLift 2089296
  have htrace : WordTrace (prefixWord ++ tailWord_2089296) baseStart_2089296 baseEnd_2089296 := by
    simpa [prefixWord, tailWord_2089296, baseEnd_2089296] using wordTrace_append hprefix tailTrace_2089296
  have hstable : (prefixWord ++ tailWord_2089296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089296).length < 2 ^ (prefixWord ++ tailWord_2089296).sum := by decide
  have hdescent : baseEnd_2089296 < baseStart_2089296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089319 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_2089319 : Nat := 118140960795 + 2089319 * 2 ^ 59
def prefixEnd_2089319 : Nat := 4983230072969 + 3 ^ 40 * 2089319 * 2
def baseEnd_2089319 : Nat := 1072824887571216263503903

theorem tailTrace_2089319 : CollatzResearch.WordTrace tailWord_2089319 prefixEnd_2089319 1072824887571216263503903 := by
  unfold tailWord_2089319
  simp only [CollatzResearch.WordTrace]
  refine ⟨76203724317761565121839011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50802482878507710081226007 76203724317761565121839011)
  ·
    refine ⟨114305586476642347682758517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76203724317761565121839011 114305586476642347682758517)
    ·
      refine ⟨10716148732185220095258611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114305586476642347682758517 10716148732185220095258611)
      ·
        refine ⟨16074223098277830142887917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10716148732185220095258611 16074223098277830142887917)
        ·
          refine ⟨6027833661854186303582969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16074223098277830142887917 6027833661854186303582969)
          ·
            refine ⟨4520875246390639727687227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6027833661854186303582969 4520875246390639727687227)
            ·
              refine ⟨6781312869585959591530841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4520875246390639727687227 6781312869585959591530841)
              ·
                refine ⟨5085984652189469693648131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6781312869585959591530841 5085984652189469693648131)
                ·
                  refine ⟨7628976978284204540472197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5085984652189469693648131 7628976978284204540472197)
                  ·
                    refine ⟨1430433183428288351338537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7628976978284204540472197 1430433183428288351338537)
                    ·
                      refine ⟨1072824887571216263503903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1430433183428288351338537 1072824887571216263503903)
                      ·
                        rfl

theorem cell23_2089319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_2089319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089319 prefixEnd_2089319 := by exact prefixLift 2089319
  have htrace : WordTrace (prefixWord ++ tailWord_2089319) baseStart_2089319 baseEnd_2089319 := by
    simpa [prefixWord, tailWord_2089319, baseEnd_2089319] using wordTrace_append hprefix tailTrace_2089319
  have hstable : (prefixWord ++ tailWord_2089319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089319).length < 2 ^ (prefixWord ++ tailWord_2089319).sum := by decide
  have hdescent : baseEnd_2089319 < baseStart_2089319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089322 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2089322 : Nat := 118140960795 + 2089322 * 2 ^ 59
def prefixEnd_2089322 : Nat := 4983230072969 + 3 ^ 40 * 2089322 * 2
def baseEnd_2089322 : Nat := 1072826428013179751766389

theorem tailTrace_2089322 : CollatzResearch.WordTrace tailWord_2089322 prefixEnd_2089322 1072826428013179751766389 := by
  unfold tailWord_2089322
  simp only [CollatzResearch.WordTrace]
  refine ⟨19050958434187674158549555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50802555824500464422798813 19050958434187674158549555)
  ·
    refine ⟨28576437651281511237824333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19050958434187674158549555 28576437651281511237824333)
    ·
      refine ⟨10716164119230566714184125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28576437651281511237824333 10716164119230566714184125)
      ·
        refine ⟨4018561544711462517819047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10716164119230566714184125 4018561544711462517819047)
        ·
          refine ⟨6027842317067193776728571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018561544711462517819047 6027842317067193776728571)
          ·
            refine ⟨9041763475600790665092857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6027842317067193776728571 9041763475600790665092857)
            ·
              refine ⟨6781322606700592998819643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9041763475600790665092857 6781322606700592998819643)
              ·
                refine ⟨10171983910050889498229465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781322606700592998819643 10171983910050889498229465)
                ·
                  refine ⟨7628987932538167123672099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10171983910050889498229465 7628987932538167123672099)
                  ·
                    refine ⟨11443481898807250685508149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7628987932538167123672099 11443481898807250685508149)
                    ·
                      refine ⟨1072826428013179751766389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11443481898807250685508149 1072826428013179751766389)
                      ·
                        rfl

theorem cell23_2089322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2089322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089322 prefixEnd_2089322 := by exact prefixLift 2089322
  have htrace : WordTrace (prefixWord ++ tailWord_2089322) baseStart_2089322 baseEnd_2089322 := by
    simpa [prefixWord, tailWord_2089322, baseEnd_2089322] using wordTrace_append hprefix tailTrace_2089322
  have hstable : (prefixWord ++ tailWord_2089322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089322).length < 2 ^ (prefixWord ++ tailWord_2089322).sum := by decide
  have hdescent : baseEnd_2089322 < baseStart_2089322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089352 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_2089352 : Nat := 118140960795 + 2089352 * 2 ^ 59
def prefixEnd_2089352 : Nat := 4983230072969 + 3 ^ 40 * 2089352 * 2
def baseEnd_2089352 : Nat := 1072841832432814634391251

theorem tailTrace_2089352 : CollatzResearch.WordTrace tailWord_2089352 prefixEnd_2089352 1072841832432814634391251 := by
  unfold tailWord_2089352
  simp only [CollatzResearch.WordTrace]
  refine ⟨38102463963321005878895155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50803285284428007838526873 38102463963321005878895155)
  ·
    refine ⟨57153695944981508818342733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38102463963321005878895155 57153695944981508818342733)
    ·
      refine ⟨21432635979368065806878525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57153695944981508818342733 21432635979368065806878525)
      ·
        refine ⟨8037238492263024677579447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21432635979368065806878525 8037238492263024677579447)
        ·
          refine ⟨12055857738394537016369171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037238492263024677579447 12055857738394537016369171)
          ·
            refine ⟨18083786607591805524553757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12055857738394537016369171 18083786607591805524553757)
            ·
              refine ⟨6781419977846927071707659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18083786607591805524553757 6781419977846927071707659)
              ·
                refine ⟨10172129966770390607561489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781419977846927071707659 10172129966770390607561489)
                ·
                  refine ⟨7629097475077792955671117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10172129966770390607561489 7629097475077792955671117)
                  ·
                    refine ⟨2860911553154172358376669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7629097475077792955671117 2860911553154172358376669)
                    ·
                      refine ⟨1072841832432814634391251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2860911553154172358376669 1072841832432814634391251)
                      ·
                        rfl

theorem cell23_2089352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_2089352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089352 prefixEnd_2089352 := by exact prefixLift 2089352
  have htrace : WordTrace (prefixWord ++ tailWord_2089352) baseStart_2089352 baseEnd_2089352 := by
    simpa [prefixWord, tailWord_2089352, baseEnd_2089352] using wordTrace_append hprefix tailTrace_2089352
  have hstable : (prefixWord ++ tailWord_2089352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089352).length < 2 ^ (prefixWord ++ tailWord_2089352).sum := by decide
  have hdescent : baseEnd_2089352 < baseStart_2089352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089455 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 7]
def baseStart_2089455 : Nat := 118140960795 + 2089455 * 2 ^ 59
def prefixEnd_2089455 : Nat := 4983230072969 + 3 ^ 40 * 2089455 * 2
def baseEnd_2089455 : Nat := 1072894720940227731403277

theorem tailTrace_2089455 : CollatzResearch.WordTrace tailWord_2089455 prefixEnd_2089455 1072894720940227731403277 := by
  unfold tailWord_2089455
  simp only [CollatzResearch.WordTrace]
  refine ⟨76208684645268860348789819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50805789763512573565859879 76208684645268860348789819)
  ·
    refine ⟨114313026967903290523184729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76208684645268860348789819 114313026967903290523184729)
    ·
      refine ⟨85734770225927467892388547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114313026967903290523184729 85734770225927467892388547)
      ·
        refine ⟨128602155338891201838582821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85734770225927467892388547 128602155338891201838582821)
        ·
          refine ⟨24112904126042100344734279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128602155338891201838582821 24112904126042100344734279)
          ·
            refine ⟨36169356189063150517101419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24112904126042100344734279 36169356189063150517101419)
            ·
              refine ⟨54254034283594725775652129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36169356189063150517101419 54254034283594725775652129)
              ·
                refine ⟨40690525712696044331739097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54254034283594725775652129 40690525712696044331739097)
                ·
                  refine ⟨30517894284522033248804323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40690525712696044331739097 30517894284522033248804323)
                  ·
                    refine ⟨45776841426783049873206485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30517894284522033248804323 45776841426783049873206485)
                    ·
                      refine ⟨1072894720940227731403277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45776841426783049873206485 1072894720940227731403277)
                      ·
                        rfl

theorem cell23_2089455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_2089455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089455 prefixEnd_2089455 := by exact prefixLift 2089455
  have htrace : WordTrace (prefixWord ++ tailWord_2089455) baseStart_2089455 baseEnd_2089455 := by
    simpa [prefixWord, tailWord_2089455, baseEnd_2089455] using wordTrace_append hprefix tailTrace_2089455
  have hstable : (prefixWord ++ tailWord_2089455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089455).length < 2 ^ (prefixWord ++ tailWord_2089455).sum := by decide
  have hdescent : baseEnd_2089455 < baseStart_2089455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089469 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 4, 3, 2]
def baseStart_2089469 : Nat := 118140960795 + 2089469 * 2 ^ 59
def prefixEnd_2089469 : Nat := 4983230072969 + 3 ^ 40 * 2089469 * 2
def baseEnd_2089469 : Nat := 1072901909669390676628213

theorem tailTrace_2089469 : CollatzResearch.WordTrace tailWord_2089469 prefixEnd_2089469 1072901909669390676628213 := by
  unfold tailWord_2089469
  simp only [CollatzResearch.WordTrace]
  refine ⟨76209195267218140739799461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50806130178145427159866307 76209195267218140739799461)
  ·
    refine ⟨14289224112603401388712399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76209195267218140739799461 14289224112603401388712399)
    ·
      refine ⟨21433836168905102083068599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14289224112603401388712399 21433836168905102083068599)
      ·
        refine ⟨32150754253357653124602899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21433836168905102083068599 32150754253357653124602899)
        ·
          refine ⟨48226131380036479686904349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32150754253357653124602899 48226131380036479686904349)
          ·
            refine ⟨18084799267513679882589131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48226131380036479686904349 18084799267513679882589131)
            ·
              refine ⟨27127198901270519823883697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18084799267513679882589131 27127198901270519823883697)
              ·
                refine ⟨20345399175952889867912773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27127198901270519823883697 20345399175952889867912773)
                ·
                  refine ⟨3814762345491166850233645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20345399175952889867912773 3814762345491166850233645)
                  ·
                    refine ⟨1430535879559187568837617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3814762345491166850233645 1430535879559187568837617)
                    ·
                      refine ⟨1072901909669390676628213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1430535879559187568837617 1072901909669390676628213)
                      ·
                        rfl

theorem cell23_2089469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_2089469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089469 prefixEnd_2089469 := by exact prefixLift 2089469
  have htrace : WordTrace (prefixWord ++ tailWord_2089469) baseStart_2089469 baseEnd_2089469 := by
    simpa [prefixWord, tailWord_2089469, baseEnd_2089469] using wordTrace_append hprefix tailTrace_2089469
  have hstable : (prefixWord ++ tailWord_2089469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089469).length < 2 ^ (prefixWord ++ tailWord_2089469).sum := by decide
  have hdescent : baseEnd_2089469 < baseStart_2089469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089479 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 3, 5]
def baseStart_2089479 : Nat := 118140960795 + 2089479 * 2 ^ 59
def prefixEnd_2089479 : Nat := 4983230072969 + 3 ^ 40 * 2089479 * 2
def baseEnd_2089479 : Nat := 357635681491978545834389

theorem tailTrace_2089479 : CollatzResearch.WordTrace tailWord_2089479 prefixEnd_2089479 357635681491978545834389 := by
  unfold tailWord_2089479
  simp only [CollatzResearch.WordTrace]
  refine ⟨76209559997181912447663491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50806373331454608298442327 76209559997181912447663491)
  ·
    refine ⟨114314339995772868671495237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76209559997181912447663491 114314339995772868671495237)
    ·
      refine ⟨21433938749207412875905357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114314339995772868671495237 21433938749207412875905357)
      ·
        refine ⟨8037727030952779828464509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21433938749207412875905357 8037727030952779828464509)
        ·
          refine ⟨3014147636607292435674191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8037727030952779828464509 3014147636607292435674191)
          ·
            refine ⟨4521221454910938653511287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3014147636607292435674191 4521221454910938653511287)
            ·
              refine ⟨6781832182366407980266931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4521221454910938653511287 6781832182366407980266931)
              ·
                refine ⟨10172748273549611970400397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781832182366407980266931 10172748273549611970400397)
                ·
                  refine ⟨3814780602581104488900149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10172748273549611970400397 3814780602581104488900149)
                  ·
                    refine ⟨357635681491978545834389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3814780602581104488900149 357635681491978545834389)
                    ·
                      rfl

theorem cell23_2089479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_2089479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089479 prefixEnd_2089479 := by exact prefixLift 2089479
  have htrace : WordTrace (prefixWord ++ tailWord_2089479) baseStart_2089479 baseEnd_2089479 := by
    simpa [prefixWord, tailWord_2089479, baseEnd_2089479] using wordTrace_append hprefix tailTrace_2089479
  have hstable : (prefixWord ++ tailWord_2089479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089479).length < 2 ^ (prefixWord ++ tailWord_2089479).sum := by decide
  have hdescent : baseEnd_2089479 < baseStart_2089479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089486 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2]
def baseStart_2089486 : Nat := 118140960795 + 2089486 * 2 ^ 59
def prefixEnd_2089486 : Nat := 4983230072969 + 3 ^ 40 * 2089486 * 2
def baseEnd_2089486 : Nat := 1072910638840517110115635

theorem tailTrace_2089486 : CollatzResearch.WordTrace tailWord_2089486 prefixEnd_2089486 1072910638840517110115635 := by
  unfold tailWord_2089486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9526226913519569080396039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50806543538771035095445541 9526226913519569080396039)
  ·
    refine ⟨14289340370279353620594059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9526226913519569080396039 14289340370279353620594059)
    ·
      refine ⟨21434010555419030430891089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14289340370279353620594059 21434010555419030430891089)
      ·
        refine ⟨16075507916564272823168317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21434010555419030430891089 16075507916564272823168317)
        ·
          refine ⟨6028315468711602308688119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16075507916564272823168317 6028315468711602308688119)
          ·
            refine ⟨9042473203067403463032179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028315468711602308688119 9042473203067403463032179)
            ·
              refine ⟨13563709804601105194548269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042473203067403463032179 13563709804601105194548269)
              ·
                refine ⟨5086391176725414447955601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13563709804601105194548269 5086391176725414447955601)
                ·
                  refine ⟨3814793382544060835966701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5086391176725414447955601 3814793382544060835966701)
                  ·
                    refine ⟨1430547518454022813487513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3814793382544060835966701 1430547518454022813487513)
                    ·
                      refine ⟨1072910638840517110115635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1430547518454022813487513 1072910638840517110115635)
                      ·
                        rfl

theorem cell23_2089486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_2089486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089486 prefixEnd_2089486 := by exact prefixLift 2089486
  have htrace : WordTrace (prefixWord ++ tailWord_2089486) baseStart_2089486 baseEnd_2089486 := by
    simpa [prefixWord, tailWord_2089486, baseEnd_2089486] using wordTrace_append hprefix tailTrace_2089486
  have hstable : (prefixWord ++ tailWord_2089486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089486).length < 2 ^ (prefixWord ++ tailWord_2089486).sum := by decide
  have hdescent : baseEnd_2089486 < baseStart_2089486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089496 : List Nat := [2, 1, 2, 3, 3, 2, 3, 1, 1, 5]
def baseStart_2089496 : Nat := 118140960795 + 2089496 * 2 ^ 59
def prefixEnd_2089496 : Nat := 4983230072969 + 3 ^ 40 * 2089496 * 2
def baseEnd_2089496 : Nat := 357638591215687356996863

theorem tailTrace_2089496 : CollatzResearch.WordTrace tailWord_2089496 prefixEnd_2089496 357638591215687356996863 := by
  unfold tailWord_2089496
  simp only [CollatzResearch.WordTrace]
  refine ⟨38105090019060162175516171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50806786692080216234021561 38105090019060162175516171)
  ·
    refine ⟨57157635028590243263274257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38105090019060162175516171 57157635028590243263274257)
    ·
      refine ⟨42868226271442682447455693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57157635028590243263274257 42868226271442682447455693)
      ·
        refine ⟨16075584851791005917795885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42868226271442682447455693 16075584851791005917795885)
        ·
          refine ⟨6028344319421627219173457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16075584851791005917795885 6028344319421627219173457)
          ·
            refine ⟨4521258239566220414380093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6028344319421627219173457 4521258239566220414380093)
            ·
              refine ⟨1695471839837332655392535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4521258239566220414380093 1695471839837332655392535)
              ·
                refine ⟨2543207759755998983088803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695471839837332655392535 2543207759755998983088803)
                ·
                  refine ⟨3814811639633998474633205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543207759755998983088803 3814811639633998474633205)
                  ·
                    refine ⟨357638591215687356996863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3814811639633998474633205 357638591215687356996863)
                    ·
                      rfl

theorem cell23_2089496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_2089496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089496 prefixEnd_2089496 := by exact prefixLift 2089496
  have htrace : WordTrace (prefixWord ++ tailWord_2089496) baseStart_2089496 baseEnd_2089496 := by
    simpa [prefixWord, tailWord_2089496, baseEnd_2089496] using wordTrace_append hprefix tailTrace_2089496
  have hstable : (prefixWord ++ tailWord_2089496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089496).length < 2 ^ (prefixWord ++ tailWord_2089496).sum := by decide
  have hdescent : baseEnd_2089496 < baseStart_2089496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089509 : List Nat := [1, 3, 1, 2, 2, 1, 3, 4, 2, 4]
def baseStart_2089509 : Nat := 118140960795 + 2089509 * 2 ^ 59
def prefixEnd_2089509 : Nat := 4983230072969 + 3 ^ 40 * 2089509 * 2
def baseEnd_2089509 : Nat := 357640816298523506709343

theorem tailTrace_2089509 : CollatzResearch.WordTrace tailWord_2089509 prefixEnd_2089509 357640816298523506709343 := by
  unfold tailWord_2089509
  simp only [CollatzResearch.WordTrace]
  refine ⟨76210654187073227571255581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50807102791382151714170387 76210654187073227571255581)
  ·
    refine ⟨28578995320152460339220843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76210654187073227571255581 28578995320152460339220843)
    ·
      refine ⟨42868492980228690508831265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28578995320152460339220843 42868492980228690508831265)
      ·
        refine ⟨32151369735171517881623449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42868492980228690508831265 32151369735171517881623449)
        ·
          refine ⟨24113527301378638411217587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32151369735171517881623449 24113527301378638411217587)
          ·
            refine ⟨36170290952067957616826381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24113527301378638411217587 36170290952067957616826381)
            ·
              refine ⟨13563859107025484106309893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36170290952067957616826381 13563859107025484106309893)
              ·
                refine ⟨2543223582567278269933105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13563859107025484106309893 2543223582567278269933105)
                ·
                  refine ⟨1907417686925458702449829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2543223582567278269933105 1907417686925458702449829)
                  ·
                    refine ⟨357640816298523506709343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1907417686925458702449829 357640816298523506709343)
                    ·
                      rfl

theorem cell23_2089509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_2089509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089509 prefixEnd_2089509 := by exact prefixLift 2089509
  have htrace : WordTrace (prefixWord ++ tailWord_2089509) baseStart_2089509 baseEnd_2089509 := by
    simpa [prefixWord, tailWord_2089509, baseEnd_2089509] using wordTrace_append hprefix tailTrace_2089509
  have hstable : (prefixWord ++ tailWord_2089509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089509).length < 2 ^ (prefixWord ++ tailWord_2089509).sum := by decide
  have hdescent : baseEnd_2089509 < baseStart_2089509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089522 : List Nat := [3, 2, 1, 1, 2, 1, 5, 8]
def baseStart_2089522 : Nat := 118140960795 + 2089522 * 2 ^ 59
def prefixEnd_2089522 : Nat := 4983230072969 + 3 ^ 40 * 2089522 * 2
def baseEnd_2089522 : Nat := 39738115709039961824647

theorem tailTrace_2089522 : CollatzResearch.WordTrace tailWord_2089522 prefixEnd_2089522 39738115709039961824647 := by
  unfold tailWord_2089522
  simp only [CollatzResearch.WordTrace]
  refine ⟨19052782084006532697869705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50807418890684087194319213 19052782084006532697869705)
  ·
    refine ⟨14289586563004899523402279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19052782084006532697869705 14289586563004899523402279)
    ·
      refine ⟨21434379844507349285103419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14289586563004899523402279 21434379844507349285103419)
      ·
        refine ⟨32151569766761023927655129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21434379844507349285103419 32151569766761023927655129)
        ·
          refine ⟨24113677325070767945741347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32151569766761023927655129 24113677325070767945741347)
          ·
            refine ⟨36170515987606151918612021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24113677325070767945741347 36170515987606151918612021)
            ·
              refine ⟨3390985873838076742369877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36170515987606151918612021 3390985873838076742369877)
              ·
                refine ⟨39738115709039961824647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3390985873838076742369877 39738115709039961824647)
                ·
                  rfl

theorem cell23_2089522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 8].length) (baseStart_2089522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089522 prefixEnd_2089522 := by exact prefixLift 2089522
  have htrace : WordTrace (prefixWord ++ tailWord_2089522) baseStart_2089522 baseEnd_2089522 := by
    simpa [prefixWord, tailWord_2089522, baseEnd_2089522] using wordTrace_append hprefix tailTrace_2089522
  have hstable : (prefixWord ++ tailWord_2089522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089522).length < 2 ^ (prefixWord ++ tailWord_2089522).sum := by decide
  have hdescent : baseEnd_2089522 < baseStart_2089522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089526 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_2089526 : Nat := 118140960795 + 2089526 * 2 ^ 59
def prefixEnd_2089526 : Nat := 4983230072969 + 3 ^ 40 * 2089526 * 2
def baseEnd_2089526 : Nat := 357643726022232317871817

theorem tailTrace_2089526 : CollatzResearch.WordTrace tailWord_2089526 prefixEnd_2089526 357643726022232317871817 := by
  unfold tailWord_2089526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4763204639250727467164027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50807516152007759649749621 4763204639250727467164027)
  ·
    refine ⟨7144806958876091200746041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4763204639250727467164027 7144806958876091200746041)
    ·
      refine ⟨5358605219157068400559531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7144806958876091200746041 5358605219157068400559531)
      ·
        refine ⟨8037907828735602600839297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5358605219157068400559531 8037907828735602600839297)
        ·
          refine ⟨6028430871551701950629473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8037907828735602600839297 6028430871551701950629473)
          ·
            refine ⟨4521323153663776462972105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6028430871551701950629473 4521323153663776462972105)
            ·
              refine ⟨3390992365247832347229079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4521323153663776462972105 3390992365247832347229079)
              ·
                refine ⟨5086488547871748520843619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390992365247832347229079 5086488547871748520843619)
                ·
                  refine ⟨7629732821807622781265429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5086488547871748520843619 7629732821807622781265429)
                  ·
                    refine ⟨357643726022232317871817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7629732821807622781265429 357643726022232317871817)
                    ·
                      rfl

theorem cell23_2089526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_2089526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089526 prefixEnd_2089526 := by exact prefixLift 2089526
  have htrace : WordTrace (prefixWord ++ tailWord_2089526) baseStart_2089526 baseEnd_2089526 := by
    simpa [prefixWord, tailWord_2089526, baseEnd_2089526] using wordTrace_append hprefix tailTrace_2089526
  have hstable : (prefixWord ++ tailWord_2089526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089526).length < 2 ^ (prefixWord ++ tailWord_2089526).sum := by decide
  have hdescent : baseEnd_2089526 < baseStart_2089526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089529 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 1, 2, 4]
def baseStart_2089529 : Nat := 118140960795 + 2089529 * 2 ^ 59
def prefixEnd_2089529 : Nat := 4983230072969 + 3 ^ 40 * 2089529 * 2
def baseEnd_2089529 : Nat := 1072932718508660441877937

theorem tailTrace_2089529 : CollatzResearch.WordTrace tailWord_2089529 prefixEnd_2089529 1072932718508660441877937 := by
  unfold tailWord_2089529
  simp only [CollatzResearch.WordTrace]
  refine ⟨76211383647000770986983641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50807589098000513991322427 76211383647000770986983641)
  ·
    refine ⟨57158537735250578240237731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76211383647000770986983641 57158537735250578240237731)
    ·
      refine ⟨85737806602875867360356597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57158537735250578240237731 85737806602875867360356597)
      ·
        refine ⟨8037919369019612565033431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85737806602875867360356597 8037919369019612565033431)
        ·
          refine ⟨12056879053529418847550147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037919369019612565033431 12056879053529418847550147)
          ·
            refine ⟨18085318580294128271325221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12056879053529418847550147 18085318580294128271325221)
            ·
              refine ⟨3390997233805149050873479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18085318580294128271325221 3390997233805149050873479)
              ·
                refine ⟨5086495850707723576310219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390997233805149050873479 5086495850707723576310219)
                ·
                  refine ⟨7629743776061585364465329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5086495850707723576310219 7629743776061585364465329)
                  ·
                    refine ⟨5722307832046189023348997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7629743776061585364465329 5722307832046189023348997)
                    ·
                      refine ⟨1072932718508660441877937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5722307832046189023348997 1072932718508660441877937)
                      ·
                        rfl

theorem cell23_2089529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_2089529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089529 prefixEnd_2089529 := by exact prefixLift 2089529
  have htrace : WordTrace (prefixWord ++ tailWord_2089529) baseStart_2089529 baseEnd_2089529 := by
    simpa [prefixWord, tailWord_2089529, baseEnd_2089529] using wordTrace_append hprefix tailTrace_2089529
  have hstable : (prefixWord ++ tailWord_2089529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089529).length < 2 ^ (prefixWord ++ tailWord_2089529).sum := by decide
  have hdescent : baseEnd_2089529 < baseStart_2089529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089533 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 3, 2, 2]
def baseStart_2089533 : Nat := 118140960795 + 2089533 * 2 ^ 59
def prefixEnd_2089533 : Nat := 4983230072969 + 3 ^ 40 * 2089533 * 2
def baseEnd_2089533 : Nat := 1072934772431278426227919

theorem tailTrace_2089533 : CollatzResearch.WordTrace tailWord_2089533 prefixEnd_2089533 1072934772431278426227919 := by
  unfold tailWord_2089533
  simp only [CollatzResearch.WordTrace]
  refine ⟨76211529538986279670129253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50807686359324186446752835 76211529538986279670129253)
  ·
    refine ⟨14289661788559927438149235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76211529538986279670129253 14289661788559927438149235)
    ·
      refine ⟨21434492682839891157223853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14289661788559927438149235 21434492682839891157223853)
      ·
        refine ⟨8037934756064959183958945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21434492682839891157223853 8037934756064959183958945)
        ·
          refine ⟨6028451067048719387969209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8037934756064959183958945 6028451067048719387969209)
          ·
            refine ⟨4521338300286539540976907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6028451067048719387969209 4521338300286539540976907)
            ·
              refine ⟨6782007450429809311465361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4521338300286539540976907 6782007450429809311465361)
              ·
                refine ⟨5086505587822356983599021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6782007450429809311465361 5086505587822356983599021)
                ·
                  refine ⟨1907439595433383868849633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5086505587822356983599021 1907439595433383868849633)
                  ·
                    refine ⟨1430579696575037901637225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1907439595433383868849633 1430579696575037901637225)
                    ·
                      refine ⟨1072934772431278426227919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1430579696575037901637225 1072934772431278426227919)
                      ·
                        rfl

theorem cell23_2089533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_2089533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089533 prefixEnd_2089533 := by exact prefixLift 2089533
  have htrace : WordTrace (prefixWord ++ tailWord_2089533) baseStart_2089533 baseEnd_2089533 := by
    simpa [prefixWord, tailWord_2089533, baseEnd_2089533] using wordTrace_append hprefix tailTrace_2089533
  have hstable : (prefixWord ++ tailWord_2089533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089533).length < 2 ^ (prefixWord ++ tailWord_2089533).sum := by decide
  have hdescent : baseEnd_2089533 < baseStart_2089533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089553 : List Nat := [1, 2, 2, 1, 3, 5, 2, 1, 1, 2, 3]
def baseStart_2089553 : Nat := 118140960795 + 2089553 * 2 ^ 59
def prefixEnd_2089553 : Nat := 4983230072969 + 3 ^ 40 * 2089553 * 2
def baseEnd_2089553 : Nat := 1072945042044368347977827

theorem tailTrace_2089553 : CollatzResearch.WordTrace tailWord_2089553 prefixEnd_2089553 1072945042044368347977827 := by
  unfold tailWord_2089553
  simp only [CollatzResearch.WordTrace]
  refine ⟨76212258998913823085857313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50808172665942548723904875 76212258998913823085857313)
  ·
    refine ⟨57159194249185367314392985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76212258998913823085857313 57159194249185367314392985)
    ·
      refine ⟨42869395686889025485794739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57159194249185367314392985 42869395686889025485794739)
      ·
        refine ⟨64304093530333538228692109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42869395686889025485794739 64304093530333538228692109)
        ·
          refine ⟨24114035073875076835759541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64304093530333538228692109 24114035073875076835759541)
          ·
            refine ⟨2260690788175788453352457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24114035073875076835759541 2260690788175788453352457)
            ·
              refine ⟨1695518091131841340014343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2260690788175788453352457 1695518091131841340014343)
              ·
                refine ⟨2543277136697762010021515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695518091131841340014343 2543277136697762010021515)
                ·
                  refine ⟨3814915705046643015032273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543277136697762010021515 3814915705046643015032273)
                  ·
                    refine ⟨2861186778784982261274205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3814915705046643015032273 2861186778784982261274205)
                    ·
                      refine ⟨1072945042044368347977827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2861186778784982261274205 1072945042044368347977827)
                      ·
                        rfl

theorem cell23_2089553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 1, 2, 3].length) (baseStart_2089553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089553 prefixEnd_2089553 := by exact prefixLift 2089553
  have htrace : WordTrace (prefixWord ++ tailWord_2089553) baseStart_2089553 baseEnd_2089553 := by
    simpa [prefixWord, tailWord_2089553, baseEnd_2089553] using wordTrace_append hprefix tailTrace_2089553
  have hstable : (prefixWord ++ tailWord_2089553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089553).length < 2 ^ (prefixWord ++ tailWord_2089553).sum := by decide
  have hdescent : baseEnd_2089553 < baseStart_2089553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089592 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_2089592 : Nat := 118140960795 + 2089592 * 2 ^ 59
def prefixEnd_2089592 : Nat := 4983230072969 + 3 ^ 40 * 2089592 * 2
def baseEnd_2089592 : Nat := 1072965067789893695390147

theorem tailTrace_2089592 : CollatzResearch.WordTrace tailWord_2089592 prefixEnd_2089592 1072965067789893695390147 := by
  unfold tailWord_2089592
  simp only [CollatzResearch.WordTrace]
  refine ⟨38106840722886266373263515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50809120963848355164351353 38106840722886266373263515)
  ·
    refine ⟨57160261084329399559895273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38106840722886266373263515 57160261084329399559895273)
    ·
      refine ⟨42870195813247049669921455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57160261084329399559895273 42870195813247049669921455)
      ·
        refine ⟨64305293719870574504882183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42870195813247049669921455 64305293719870574504882183)
        ·
          refine ⟨96457940579805861757323275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64305293719870574504882183 96457940579805861757323275)
          ·
            refine ⟨144686910869708792635984913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96457940579805861757323275 144686910869708792635984913)
            ·
              refine ⟨108515183152281594476988685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144686910869708792635984913 108515183152281594476988685)
              ·
                refine ⟨40693193682105597928870757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108515183152281594476988685 40693193682105597928870757)
                ·
                  refine ⟨7629973815394799611663267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40693193682105597928870757 7629973815394799611663267)
                  ·
                    refine ⟨11444960723092199417494901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7629973815394799611663267 11444960723092199417494901)
                    ·
                      refine ⟨1072965067789893695390147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11444960723092199417494901 1072965067789893695390147)
                      ·
                        rfl

theorem cell23_2089592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_2089592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089592 prefixEnd_2089592 := by exact prefixLift 2089592
  have htrace : WordTrace (prefixWord ++ tailWord_2089592) baseStart_2089592 baseEnd_2089592 := by
    simpa [prefixWord, tailWord_2089592, baseEnd_2089592] using wordTrace_append hprefix tailTrace_2089592
  have hstable : (prefixWord ++ tailWord_2089592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089592).length < 2 ^ (prefixWord ++ tailWord_2089592).sum := by decide
  have hdescent : baseEnd_2089592 < baseStart_2089592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089593 : List Nat := [1, 2, 1, 3, 3, 3, 2, 2, 1, 3, 2]
def baseStart_2089593 : Nat := 118140960795 + 2089593 * 2 ^ 59
def prefixEnd_2089593 : Nat := 4983230072969 + 3 ^ 40 * 2089593 * 2
def baseEnd_2089593 : Nat := 1072965581270548191477643

theorem tailTrace_2089593 : CollatzResearch.WordTrace tailWord_2089593 prefixEnd_2089593 1072965581270548191477643 := by
  unfold tailWord_2089593
  simp only [CollatzResearch.WordTrace]
  refine ⟨76213717918768909917313433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50809145279179273278208955 76213717918768909917313433)
  ·
    refine ⟨57160288439076682437985075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76213717918768909917313433 57160288439076682437985075)
    ·
      refine ⟨85740432658615023656977613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57160288439076682437985075 85740432658615023656977613)
      ·
        refine ⟨32152662246980633871366605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85740432658615023656977613 32152662246980633871366605)
        ·
          refine ⟨12057248342617737701762477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32152662246980633871366605 12057248342617737701762477)
          ·
            refine ⟨4521468128481651638160929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12057248342617737701762477 4521468128481651638160929)
            ·
              refine ⟨3391101096361238728620697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4521468128481651638160929 3391101096361238728620697)
              ·
                refine ⟨2543325822270929046465523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3391101096361238728620697 2543325822270929046465523)
                ·
                  refine ⟨3814988733406393569698285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543325822270929046465523 3814988733406393569698285)
                  ·
                    refine ⟨1430620775027397588636857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3814988733406393569698285 1430620775027397588636857)
                    ·
                      refine ⟨1072965581270548191477643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1430620775027397588636857 1072965581270548191477643)
                      ·
                        rfl

theorem cell23_2089593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_2089593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089593 prefixEnd_2089593 := by exact prefixLift 2089593
  have htrace : WordTrace (prefixWord ++ tailWord_2089593) baseStart_2089593 baseEnd_2089593 := by
    simpa [prefixWord, tailWord_2089593, baseEnd_2089593] using wordTrace_append hprefix tailTrace_2089593
  have hstable : (prefixWord ++ tailWord_2089593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089593).length < 2 ^ (prefixWord ++ tailWord_2089593).sum := by decide
  have hdescent : baseEnd_2089593 < baseStart_2089593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089623 : List Nat := [1, 1, 3, 3, 2, 1, 2, 4, 2, 2, 2]
def baseStart_2089623 : Nat := 118140960795 + 2089623 * 2 ^ 59
def prefixEnd_2089623 : Nat := 4983230072969 + 3 ^ 40 * 2089623 * 2
def baseEnd_2089623 : Nat := 1072980985690183074102505

theorem tailTrace_2089623 : CollatzResearch.WordTrace tailWord_2089623 prefixEnd_2089623 1072980985690183074102505 := by
  unfold tailWord_2089623
  simp only [CollatzResearch.WordTrace]
  refine ⟨76214812108660225040905523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50809874739106816693937015 76214812108660225040905523)
  ·
    refine ⟨114322218162990337561358285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76214812108660225040905523 114322218162990337561358285)
    ·
      refine ⟨42870831811121376585509357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114322218162990337561358285 42870831811121376585509357)
      ·
        refine ⟨16076561929170516219566009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42870831811121376585509357 16076561929170516219566009)
        ·
          refine ⟨12057421446877887164674507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16076561929170516219566009 12057421446877887164674507)
          ·
            refine ⟨18086132170316830747011761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12057421446877887164674507 18086132170316830747011761)
            ·
              refine ⟨13564599127737623060258821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18086132170316830747011761 13564599127737623060258821)
              ·
                refine ⟨2543362336450804323798529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13564599127737623060258821 2543362336450804323798529)
                ·
                  refine ⟨1907521752338103242848897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2543362336450804323798529 1907521752338103242848897)
                  ·
                    refine ⟨1430641314253577432136673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1907521752338103242848897 1430641314253577432136673)
                    ·
                      refine ⟨1072980985690183074102505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1430641314253577432136673 1072980985690183074102505)
                      ·
                        rfl

theorem cell23_2089623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_2089623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089623 prefixEnd_2089623 := by exact prefixLift 2089623
  have htrace : WordTrace (prefixWord ++ tailWord_2089623) baseStart_2089623 baseEnd_2089623 := by
    simpa [prefixWord, tailWord_2089623, baseEnd_2089623] using wordTrace_append hprefix tailTrace_2089623
  have hstable : (prefixWord ++ tailWord_2089623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089623).length < 2 ^ (prefixWord ++ tailWord_2089623).sum := by decide
  have hdescent : baseEnd_2089623 < baseStart_2089623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089629 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 7]
def baseStart_2089629 : Nat := 118140960795 + 2089629 * 2 ^ 59
def prefixEnd_2089629 : Nat := 4983230072969 + 3 ^ 40 * 2089629 * 2
def baseEnd_2089629 : Nat := 119220451841567783403053

theorem tailTrace_2089629 : CollatzResearch.WordTrace tailWord_2089629 prefixEnd_2089629 119220451841567783403053 := by
  unfold tailWord_2089629
  simp only [CollatzResearch.WordTrace]
  refine ⟨76215030946638488065623941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50810020631092325377082627 76215030946638488065623941)
  ·
    refine ⟨14290318302494716512304489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76215030946638488065623941 14290318302494716512304489)
    ·
      refine ⟨10717738726871037384228367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14290318302494716512304489 10717738726871037384228367)
      ·
        refine ⟨16076608090306556076342551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10717738726871037384228367 16076608090306556076342551)
        ·
          refine ⟨24114912135459834114513827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16076608090306556076342551 24114912135459834114513827)
          ·
            refine ⟨36172368203189751171770741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24114912135459834114513827 36172368203189751171770741)
            ·
              refine ⟨3391159519049039172353507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36172368203189751171770741 3391159519049039172353507)
              ·
                refine ⟨5086739278573558758530261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3391159519049039172353507 5086739278573558758530261)
                ·
                  refine ⟨119220451841567783403053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5086739278573558758530261 119220451841567783403053)
                  ·
                    rfl

theorem cell23_2089629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_2089629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089629 prefixEnd_2089629 := by exact prefixLift 2089629
  have htrace : WordTrace (prefixWord ++ tailWord_2089629) baseStart_2089629 baseEnd_2089629 := by
    simpa [prefixWord, tailWord_2089629, baseEnd_2089629] using wordTrace_append hprefix tailTrace_2089629
  have hstable : (prefixWord ++ tailWord_2089629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089629).length < 2 ^ (prefixWord ++ tailWord_2089629).sum := by decide
  have hdescent : baseEnd_2089629 < baseStart_2089629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089676 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 2, 5]
def baseStart_2089676 : Nat := 118140960795 + 2089676 * 2 ^ 59
def prefixEnd_2089676 : Nat := 4983230072969 + 3 ^ 40 * 2089676 * 2
def baseEnd_2089676 : Nat := 357669400054957122246587

theorem tailTrace_2089676 : CollatzResearch.WordTrace tailWord_2089676 prefixEnd_2089676 357669400054957122246587 := by
  unfold tailWord_2089676
  simp only [CollatzResearch.WordTrace]
  refine ⟨38108372588734107546292441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50811163451645476728389921 38108372588734107546292441)
  ·
    refine ⟨28581279441550580659719331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38108372588734107546292441 28581279441550580659719331)
    ·
      refine ⟨42871919162325870989578997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28581279441550580659719331 42871919162325870989578997)
      ·
        refine ⟨4019242421468050405273031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42871919162325870989578997 4019242421468050405273031)
        ·
          refine ⟨6028863632202075607909547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4019242421468050405273031 6028863632202075607909547)
          ·
            refine ⟨9043295448303113411864321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028863632202075607909547 9043295448303113411864321)
            ·
              refine ⟨6782471586227335058898241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9043295448303113411864321 6782471586227335058898241)
              ·
                refine ⟨5086853689670501294173681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6782471586227335058898241 5086853689670501294173681)
                ·
                  refine ⟨3815140267252875970630261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5086853689670501294173681 3815140267252875970630261)
                  ·
                    refine ⟨357669400054957122246587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3815140267252875970630261 357669400054957122246587)
                    ·
                      rfl

theorem cell23_2089676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_2089676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089676 prefixEnd_2089676 := by exact prefixLift 2089676
  have htrace : WordTrace (prefixWord ++ tailWord_2089676) baseStart_2089676 baseEnd_2089676 := by
    simpa [prefixWord, tailWord_2089676, baseEnd_2089676] using wordTrace_append hprefix tailTrace_2089676
  have hstable : (prefixWord ++ tailWord_2089676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089676).length < 2 ^ (prefixWord ++ tailWord_2089676).sum := by decide
  have hdescent : baseEnd_2089676 < baseStart_2089676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089726 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_2089726 : Nat := 118140960795 + 2089726 * 2 ^ 59
def prefixEnd_2089726 : Nat := 4983230072969 + 3 ^ 40 * 2089726 * 2
def baseEnd_2089726 : Nat := 1073033874197596171114531

theorem tailTrace_2089726 : CollatzResearch.WordTrace tailWord_2089726 prefixEnd_2089726 1073033874197596171114531 := by
  unfold tailWord_2089726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9527321103410884203988129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50812379218191382421270021 9527321103410884203988129)
  ·
    refine ⟨7145490827558163152991097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9527321103410884203988129 7145490827558163152991097)
    ·
      refine ⟨5359118120668622364743323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7145490827558163152991097 5359118120668622364743323)
      ·
        refine ⟨8038677181002933547114985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5359118120668622364743323 8038677181002933547114985)
        ·
          refine ⟨6029007885752200160336239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8038677181002933547114985 6029007885752200160336239)
          ·
            refine ⟨9043511828628300240504359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6029007885752200160336239 9043511828628300240504359)
            ·
              refine ⟨13565267742942450360756539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9043511828628300240504359 13565267742942450360756539)
              ·
                refine ⟨20347901614413675541134809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13565267742942450360756539 20347901614413675541134809)
                ·
                  refine ⟨15260926210810256655851107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20347901614413675541134809 15260926210810256655851107)
                  ·
                    refine ⟨22891389316215384983776661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15260926210810256655851107 22891389316215384983776661)
                    ·
                      refine ⟨1073033874197596171114531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22891389316215384983776661 1073033874197596171114531)
                      ·
                        rfl

theorem cell23_2089726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_2089726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089726 prefixEnd_2089726 := by exact prefixLift 2089726
  have htrace : WordTrace (prefixWord ++ tailWord_2089726) baseStart_2089726 baseEnd_2089726 := by
    simpa [prefixWord, tailWord_2089726, baseEnd_2089726] using wordTrace_append hprefix tailTrace_2089726
  have hstable : (prefixWord ++ tailWord_2089726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089726).length < 2 ^ (prefixWord ++ tailWord_2089726).sum := by decide
  have hdescent : baseEnd_2089726 < baseStart_2089726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089736 : List Nat := [2, 1, 3, 2, 2, 2, 3, 2, 6]
def baseStart_2089736 : Nat := 118140960795 + 2089736 * 2 ^ 59
def prefixEnd_2089736 : Nat := 4983230072969 + 3 ^ 40 * 2089736 * 2
def baseEnd_2089736 : Nat := 119226556556015681332165

theorem tailTrace_2089736 : CollatzResearch.WordTrace tailWord_2089736 prefixEnd_2089736 119226556556015681332165 := by
  unfold tailWord_2089736
  simp only [CollatzResearch.WordTrace]
  refine ⟨38109466778625422669884531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50812622371500563559846041 38109466778625422669884531)
  ·
    refine ⟨57164200167938134004826797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38109466778625422669884531 57164200167938134004826797)
    ·
      refine ⟨21436575062976800251810049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57164200167938134004826797 21436575062976800251810049)
      ·
        refine ⟨16077431297232600188857537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21436575062976800251810049 16077431297232600188857537)
        ·
          refine ⟨12058073472924450141643153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16077431297232600188857537 12058073472924450141643153)
          ·
            refine ⟨9043555104693337606232365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12058073472924450141643153 9043555104693337606232365)
            ·
              refine ⟨3391333164260001602337137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9043555104693337606232365 3391333164260001602337137)
              ·
                refine ⟨2543499873195001201752853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3391333164260001602337137 2543499873195001201752853)
                ·
                  refine ⟨119226556556015681332165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2543499873195001201752853 119226556556015681332165)
                  ·
                    rfl

theorem cell23_2089736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 6].length) (baseStart_2089736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089736 prefixEnd_2089736 := by exact prefixLift 2089736
  have htrace : WordTrace (prefixWord ++ tailWord_2089736) baseStart_2089736 baseEnd_2089736 := by
    simpa [prefixWord, tailWord_2089736, baseEnd_2089736] using wordTrace_append hprefix tailTrace_2089736
  have hstable : (prefixWord ++ tailWord_2089736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089736).length < 2 ^ (prefixWord ++ tailWord_2089736).sum := by decide
  have hdescent : baseEnd_2089736 < baseStart_2089736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089813 : List Nat := [1, 3, 2, 2, 2, 1, 3, 3, 2, 4]
def baseStart_2089813 : Nat := 118140960795 + 2089813 * 2 ^ 59
def prefixEnd_2089813 : Nat := 4983230072969 + 3 ^ 40 * 2089813 * 2
def baseEnd_2089813 : Nat := 357692849004845776908877

theorem tailTrace_2089813 : CollatzResearch.WordTrace tailWord_2089813 prefixEnd_2089813 357692849004845776908877 := by
  unfold tailWord_2089813
  simp only [CollatzResearch.WordTrace]
  refine ⟨76221741977971887490322093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50814494651981258326881395 76221741977971887490322093)
  ·
    refine ⟨28583153241739457808870785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76221741977971887490322093 28583153241739457808870785)
    ·
      refine ⟨21437364931304593356653089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28583153241739457808870785 21437364931304593356653089)
      ·
        refine ⟨16078023698478445017489817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21437364931304593356653089 16078023698478445017489817)
        ·
          refine ⟨12058517773858833763117363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16078023698478445017489817 12058517773858833763117363)
          ·
            refine ⟨18087776660788250644676045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12058517773858833763117363 18087776660788250644676045)
            ·
              refine ⟨6782916247795593991753517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18087776660788250644676045 6782916247795593991753517)
              ·
                refine ⟨2543593592923347746907569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6782916247795593991753517 2543593592923347746907569)
                ·
                  refine ⟨1907695194692510810180677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2543593592923347746907569 1907695194692510810180677)
                  ·
                    refine ⟨357692849004845776908877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1907695194692510810180677 357692849004845776908877)
                    ·
                      rfl

theorem cell23_2089813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_2089813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089813 prefixEnd_2089813 := by exact prefixLift 2089813
  have htrace : WordTrace (prefixWord ++ tailWord_2089813) baseStart_2089813 baseEnd_2089813 := by
    simpa [prefixWord, tailWord_2089813, baseEnd_2089813] using wordTrace_append hprefix tailTrace_2089813
  have hstable : (prefixWord ++ tailWord_2089813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089813).length < 2 ^ (prefixWord ++ tailWord_2089813).sum := by decide
  have hdescent : baseEnd_2089813 < baseStart_2089813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089820 : List Nat := [2, 2, 4, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_2089820 : Nat := 118140960795 + 2089820 * 2 ^ 59
def prefixEnd_2089820 : Nat := 4983230072969 + 3 ^ 40 * 2089820 * 2
def baseEnd_2089820 : Nat := 1073082141379118803339099

theorem tailTrace_2089820 : CollatzResearch.WordTrace tailWord_2089820 prefixEnd_2089820 1073082141379118803339099 := by
  unfold tailWord_2089820
  simp only [CollatzResearch.WordTrace]
  refine ⟨38110998644473263842913457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50814664859297685123884609 38110998644473263842913457)
  ·
    refine ⟨28583248983354947882185093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38110998644473263842913457 28583248983354947882185093)
    ·
      refine ⟨5359359184379052727909705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28583248983354947882185093 5359359184379052727909705)
      ·
        refine ⟨4019519388284289545932279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5359359184379052727909705 4019519388284289545932279)
        ·
          refine ⟨6029279082426434318898419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4019519388284289545932279 6029279082426434318898419)
          ·
            refine ⟨9043918623639651478347629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6029279082426434318898419 9043918623639651478347629)
            ·
              refine ⟨3391469483864869304380361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9043918623639651478347629 3391469483864869304380361)
              ·
                refine ⟨2543602112898651978285271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3391469483864869304380361 2543602112898651978285271)
                ·
                  refine ⟨3815403169347977967427907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543602112898651978285271 3815403169347977967427907)
                  ·
                    refine ⟨5723104754021966951141861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3815403169347977967427907 5723104754021966951141861)
                    ·
                      refine ⟨1073082141379118803339099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5723104754021966951141861 1073082141379118803339099)
                      ·
                        rfl

theorem cell23_2089820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_2089820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089820 prefixEnd_2089820 := by exact prefixLift 2089820
  have htrace : WordTrace (prefixWord ++ tailWord_2089820) baseStart_2089820 baseEnd_2089820 := by
    simpa [prefixWord, tailWord_2089820, baseEnd_2089820] using wordTrace_append hprefix tailTrace_2089820
  have hstable : (prefixWord ++ tailWord_2089820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089820).length < 2 ^ (prefixWord ++ tailWord_2089820).sum := by decide
  have hdescent : baseEnd_2089820 < baseStart_2089820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089837 : List Nat := [1, 5, 1, 1, 1, 1, 1, 7, 1, 2, 2]
def baseStart_2089837 : Nat := 118140960795 + 2089837 * 2 ^ 59
def prefixEnd_2089837 : Nat := 4983230072969 + 3 ^ 40 * 2089837 * 2
def baseEnd_2089837 : Nat := 1073090870550245236826521

theorem tailTrace_2089837 : CollatzResearch.WordTrace tailWord_2089837 prefixEnd_2089837 1073090870550245236826521 := by
  unfold tailWord_2089837
  simp only [CollatzResearch.WordTrace]
  refine ⟨76222617329884939589195765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50815078219923293059463843 76222617329884939589195765)
  ·
    refine ⟨7145870374676713086487103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76222617329884939589195765 7145870374676713086487103)
    ·
      refine ⟨10718805562015069629730655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7145870374676713086487103 10718805562015069629730655)
      ·
        refine ⟨16078208343022604444595983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10718805562015069629730655 16078208343022604444595983)
        ·
          refine ⟨24117312514533906666893975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16078208343022604444595983 24117312514533906666893975)
          ·
            refine ⟨36175968771800860000340963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24117312514533906666893975 36175968771800860000340963)
            ·
              refine ⟨54263953157701290000511445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36175968771800860000340963 54263953157701290000511445)
              ·
                refine ⟨1271811402133623984386987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54263953157701290000511445 1271811402133623984386987)
                ·
                  refine ⟨1907717103200435976580481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1271811402133623984386987 1907717103200435976580481)
                  ·
                    refine ⟨1430787827400326982435361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1907717103200435976580481 1430787827400326982435361)
                    ·
                      refine ⟨1073090870550245236826521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1430787827400326982435361 1073090870550245236826521)
                      ·
                        rfl

theorem cell23_2089837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_2089837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089837 prefixEnd_2089837 := by exact prefixLift 2089837
  have htrace : WordTrace (prefixWord ++ tailWord_2089837) baseStart_2089837 baseEnd_2089837 := by
    simpa [prefixWord, tailWord_2089837, baseEnd_2089837] using wordTrace_append hprefix tailTrace_2089837
  have hstable : (prefixWord ++ tailWord_2089837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089837).length < 2 ^ (prefixWord ++ tailWord_2089837).sum := by decide
  have hdescent : baseEnd_2089837 < baseStart_2089837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089839 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 4, 7]
def baseStart_2089839 : Nat := 118140960795 + 2089839 * 2 ^ 59
def prefixEnd_2089839 : Nat := 4983230072969 + 3 ^ 40 * 2089839 * 2
def baseEnd_2089839 : Nat := 357697299170518076333837

theorem tailTrace_2089839 : CollatzResearch.WordTrace tailWord_2089839 prefixEnd_2089839 357697299170518076333837 := by
  unfold tailWord_2089839
  simp only [CollatzResearch.WordTrace]
  refine ⟨76222690275877693930768571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50815126850585129287179047 76222690275877693930768571)
  ·
    refine ⟨114334035413816540896152857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76222690275877693930768571 114334035413816540896152857)
    ·
      refine ⟨85750526560362405672114643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114334035413816540896152857 85750526560362405672114643)
      ·
        refine ⟨128625789840543608508171965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85750526560362405672114643 128625789840543608508171965)
        ·
          refine ⟨48234671190203853190564487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128625789840543608508171965 48234671190203853190564487)
          ·
            refine ⟨72352006785305779785846731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48234671190203853190564487 72352006785305779785846731)
            ·
              refine ⟨108528010177958669678770097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72352006785305779785846731 108528010177958669678770097)
              ·
                refine ⟨81396007633469002259077573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108528010177958669678770097 81396007633469002259077573)
                ·
                  refine ⟨15261751431275437923577045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81396007633469002259077573 15261751431275437923577045)
                  ·
                    refine ⟨357697299170518076333837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15261751431275437923577045 357697299170518076333837)
                    ·
                      rfl

theorem cell23_2089839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_2089839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089839 prefixEnd_2089839 := by exact prefixLift 2089839
  have htrace : WordTrace (prefixWord ++ tailWord_2089839) baseStart_2089839 baseEnd_2089839 := by
    simpa [prefixWord, tailWord_2089839, baseEnd_2089839] using wordTrace_append hprefix tailTrace_2089839
  have hstable : (prefixWord ++ tailWord_2089839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089839).length < 2 ^ (prefixWord ++ tailWord_2089839).sum := by decide
  have hdescent : baseEnd_2089839 < baseStart_2089839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089853 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 4, 1, 3]
def baseStart_2089853 : Nat := 118140960795 + 2089853 * 2 ^ 59
def prefixEnd_2089853 : Nat := 4983230072969 + 3 ^ 40 * 2089853 * 2
def baseEnd_2089853 : Nat := 1073099086240717174226447

theorem tailTrace_2089853 : CollatzResearch.WordTrace tailWord_2089853 prefixEnd_2089853 1073099086240717174226447 := by
  unfold tailWord_2089853
  simp only [CollatzResearch.WordTrace]
  refine ⟨76223200897826974321778213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50815467265217982881185475 76223200897826974321778213)
  ·
    refine ⟨14291850168342557685333415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76223200897826974321778213 14291850168342557685333415)
    ·
      refine ⟨21437775252513836528000123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14291850168342557685333415 21437775252513836528000123)
      ·
        refine ⟨32156662878770754792000185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21437775252513836528000123 32156662878770754792000185)
        ·
          refine ⟨24117497159078066094000139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32156662878770754792000185 24117497159078066094000139)
          ·
            refine ⟨36176245738617099141000209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24117497159078066094000139 36176245738617099141000209)
            ·
              refine ⟨27132184303962824355750157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36176245738617099141000209 27132184303962824355750157)
              ·
                refine ⟨10174569113986059133406309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27132184303962824355750157 10174569113986059133406309)
                ·
                  refine ⟨1907731708872386087513683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10174569113986059133406309 1907731708872386087513683)
                  ·
                    refine ⟨2861597563308579131270525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1907731708872386087513683 2861597563308579131270525)
                    ·
                      refine ⟨1073099086240717174226447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2861597563308579131270525 1073099086240717174226447)
                      ·
                        rfl

theorem cell23_2089853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_2089853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089853 prefixEnd_2089853 := by exact prefixLift 2089853
  have htrace : WordTrace (prefixWord ++ tailWord_2089853) baseStart_2089853 baseEnd_2089853 := by
    simpa [prefixWord, tailWord_2089853, baseEnd_2089853] using wordTrace_append hprefix tailTrace_2089853
  have hstable : (prefixWord ++ tailWord_2089853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089853).length < 2 ^ (prefixWord ++ tailWord_2089853).sum := by decide
  have hdescent : baseEnd_2089853 < baseStart_2089853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089953 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 1, 7, 2]
def baseStart_2089953 : Nat := 118140960795 + 2089953 * 2 ^ 59
def prefixEnd_2089953 : Nat := 4983230072969 + 3 ^ 40 * 2089953 * 2
def baseEnd_2089953 : Nat := 1073150434306166782975987

theorem tailTrace_2089953 : CollatzResearch.WordTrace tailWord_2089953 prefixEnd_2089953 1073150434306166782975987 := by
  unfold tailWord_2089953
  simp only [CollatzResearch.WordTrace]
  refine ⟨76226848197464691400418513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50817898798309794266945675 76226848197464691400418513)
  ·
    refine ⟨57170136148098518550313885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76226848197464691400418513 57170136148098518550313885)
    ·
      refine ⟨21438801055536944456367707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57170136148098518550313885 21438801055536944456367707)
      ·
        refine ⟨32158201583305416684551561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21438801055536944456367707 32158201583305416684551561)
        ·
          refine ⟨24118651187479062513413671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32158201583305416684551561 24118651187479062513413671)
          ·
            refine ⟨36177976781218593770120507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24118651187479062513413671 36177976781218593770120507)
            ·
              refine ⟨54266965171827890655180761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36177976781218593770120507 54266965171827890655180761)
              ·
                refine ⟨40700223878870917991385571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54266965171827890655180761 40700223878870917991385571)
                ·
                  refine ⟨61050335818306376987078357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40700223878870917991385571 61050335818306376987078357)
                  ·
                    refine ⟨1430867245741555710634649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61050335818306376987078357 1430867245741555710634649)
                    ·
                      refine ⟨1073150434306166782975987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1430867245741555710634649 1073150434306166782975987)
                      ·
                        rfl

theorem cell23_2089953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_2089953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089953 prefixEnd_2089953 := by exact prefixLift 2089953
  have htrace : WordTrace (prefixWord ++ tailWord_2089953) baseStart_2089953 baseEnd_2089953 := by
    simpa [prefixWord, tailWord_2089953, baseEnd_2089953] using wordTrace_append hprefix tailTrace_2089953
  have hstable : (prefixWord ++ tailWord_2089953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089953).length < 2 ^ (prefixWord ++ tailWord_2089953).sum := by decide
  have hdescent : baseEnd_2089953 < baseStart_2089953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089972 : List Nat := [2, 6, 2, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_2089972 : Nat := 118140960795 + 2089972 * 2 ^ 59
def prefixEnd_2089972 : Nat := 4983230072969 + 3 ^ 40 * 2089972 * 2
def baseEnd_2089972 : Nat := 1073160190438602208638401

theorem tailTrace_2089972 : CollatzResearch.WordTrace tailWord_2089972 prefixEnd_2089972 1073160190438602208638401 := by
  unfold tailWord_2089972
  simp only [CollatzResearch.WordTrace]
  refine ⟨38113770592197928822680085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50818360789597238430240113 38113770592197928822680085)
  ·
    refine ⟨1786582996509277913563129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38113770592197928822680085 1786582996509277913563129)
    ·
      refine ⟨1339937247381958435172347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1786582996509277913563129 1339937247381958435172347)
      ·
        refine ⟨2009905871072937652758521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1339937247381958435172347 2009905871072937652758521)
        ·
          refine ⟨1507429403304703239568891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2009905871072937652758521 1507429403304703239568891)
          ·
            refine ⟨2261144104957054859353337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507429403304703239568891 2261144104957054859353337)
            ·
              refine ⟨1695858078717791144515003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2261144104957054859353337 1695858078717791144515003)
              ·
                refine ⟨2543787118076686716772505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695858078717791144515003 2543787118076686716772505)
                ·
                  refine ⟨1907840338557515037579379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2543787118076686716772505 1907840338557515037579379)
                  ·
                    refine ⟨2861760507836272556369069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1907840338557515037579379 2861760507836272556369069)
                    ·
                      refine ⟨1073160190438602208638401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2861760507836272556369069 1073160190438602208638401)
                      ·
                        rfl

theorem cell23_2089972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_2089972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089972 prefixEnd_2089972 := by exact prefixLift 2089972
  have htrace : WordTrace (prefixWord ++ tailWord_2089972) baseStart_2089972 baseEnd_2089972 := by
    simpa [prefixWord, tailWord_2089972, baseEnd_2089972] using wordTrace_append hprefix tailTrace_2089972
  have hstable : (prefixWord ++ tailWord_2089972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089972).length < 2 ^ (prefixWord ++ tailWord_2089972).sum := by decide
  have hdescent : baseEnd_2089972 < baseStart_2089972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089993 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 3, 4]
def baseStart_2089993 : Nat := 118140960795 + 2089993 * 2 ^ 59
def prefixEnd_2089993 : Nat := 4983230072969 + 3 ^ 40 * 2089993 * 2
def baseEnd_2089993 : Nat := 357723657844115542158601

theorem tailTrace_2089993 : CollatzResearch.WordTrace tailWord_2089993 prefixEnd_2089993 357723657844115542158601 := by
  unfold tailWord_2089993
  simp only [CollatzResearch.WordTrace]
  refine ⟨76228307117319778231874633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50818871411546518821249755 76228307117319778231874633)
  ·
    refine ⟨57171230337989833673905975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76228307117319778231874633 57171230337989833673905975)
    ·
      refine ⟨85756845506984750510858963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57171230337989833673905975 85756845506984750510858963)
      ·
        refine ⟨128635268260477125766288445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85756845506984750510858963 128635268260477125766288445)
        ·
          refine ⟨48238225597678922162358167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128635268260477125766288445 48238225597678922162358167)
          ·
            refine ⟨72357338396518383243537251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48238225597678922162358167 72357338396518383243537251)
            ·
              refine ⟨108536007594777574865305877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72357338396518383243537251 108536007594777574865305877)
              ·
                refine ⟨5087625356005198821811213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108536007594777574865305877 5087625356005198821811213)
                ·
                  refine ⟨1907859508501949558179205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5087625356005198821811213 1907859508501949558179205)
                  ·
                    refine ⟨357723657844115542158601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1907859508501949558179205 357723657844115542158601)
                    ·
                      rfl

theorem cell23_2089993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 4].length) (baseStart_2089993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2089993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2089993 prefixEnd_2089993 := by exact prefixLift 2089993
  have htrace : WordTrace (prefixWord ++ tailWord_2089993) baseStart_2089993 baseEnd_2089993 := by
    simpa [prefixWord, tailWord_2089993, baseEnd_2089993] using wordTrace_append hprefix tailTrace_2089993
  have hstable : (prefixWord ++ tailWord_2089993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089993).length < 2 ^ (prefixWord ++ tailWord_2089993).sum := by decide
  have hdescent : baseEnd_2089993 < baseStart_2089993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090053 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 3, 5]
def baseStart_2090053 : Nat := 118140960795 + 2090053 * 2 ^ 59
def prefixEnd_2090053 : Nat := 4983230072969 + 3 ^ 40 * 2090053 * 2
def baseEnd_2090053 : Nat := 357733927457205463908509

theorem tailTrace_2090053 : CollatzResearch.WordTrace tailWord_2090053 prefixEnd_2090053 357733927457205463908509 := by
  unfold tailWord_2090053
  simp only [CollatzResearch.WordTrace]
  refine ⟨76230495497102408479058813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50820330331401605652705875 76230495497102408479058813)
  ·
    refine ⟨28586435811413403179647055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76230495497102408479058813 28586435811413403179647055)
    ·
      refine ⟨42879653717120104769470583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28586435811413403179647055 42879653717120104769470583)
      ·
        refine ⟨64319480575680157154205875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42879653717120104769470583 64319480575680157154205875)
        ·
          refine ⟨96479220863520235731308813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64319480575680157154205875 96479220863520235731308813)
          ·
            refine ⟨36179707823820088399240805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96479220863520235731308813 36179707823820088399240805)
            ·
              refine ⟨6783695216966266574857651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36179707823820088399240805 6783695216966266574857651)
              ·
                refine ⟨10175542825449399862286477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6783695216966266574857651 10175542825449399862286477)
                ·
                  refine ⟨3815828559543524948357429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10175542825449399862286477 3815828559543524948357429)
                  ·
                    refine ⟨357733927457205463908509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3815828559543524948357429 357733927457205463908509)
                    ·
                      rfl

theorem cell23_2090053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_2090053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090053 prefixEnd_2090053 := by exact prefixLift 2090053
  have htrace : WordTrace (prefixWord ++ tailWord_2090053) baseStart_2090053 baseEnd_2090053 := by
    simpa [prefixWord, tailWord_2090053, baseEnd_2090053] using wordTrace_append hprefix tailTrace_2090053
  have hstable : (prefixWord ++ tailWord_2090053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090053).length < 2 ^ (prefixWord ++ tailWord_2090053).sum := by decide
  have hdescent : baseEnd_2090053 < baseStart_2090053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090054 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_2090054 : Nat := 118140960795 + 2090054 * 2 ^ 59
def prefixEnd_2090054 : Nat := 4983230072969 + 3 ^ 40 * 2090054 * 2
def baseEnd_2090054 : Nat := 1073202295852270887813023

theorem tailTrace_2090054 : CollatzResearch.WordTrace tailWord_2090054 prefixEnd_2090054 1073202295852270887813023 := by
  unfold tailWord_2090054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2382204124065587051557663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50820354646732523766563477 2382204124065587051557663)
  ·
    refine ⟨3573306186098380577336495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2382204124065587051557663 3573306186098380577336495)
    ·
      refine ⟨5359959279147570866004743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3573306186098380577336495 5359959279147570866004743)
      ·
        refine ⟨8039938918721356299007115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5359959279147570866004743 8039938918721356299007115)
        ·
          refine ⟨12059908378082034448510673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8039938918721356299007115 12059908378082034448510673)
          ·
            refine ⟨9044931283561525836383005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12059908378082034448510673 9044931283561525836383005)
            ·
              refine ⟨3391849231335572188643627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9044931283561525836383005 3391849231335572188643627)
              ·
                refine ⟨5087773847003358282965441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3391849231335572188643627 5087773847003358282965441)
                ·
                  refine ⟨3815830385252518712224081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5087773847003358282965441 3815830385252518712224081)
                  ·
                    refine ⟨2861872788939389034168061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3815830385252518712224081 2861872788939389034168061)
                    ·
                      refine ⟨1073202295852270887813023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2861872788939389034168061 1073202295852270887813023)
                      ·
                        rfl

theorem cell23_2090054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_2090054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090054 prefixEnd_2090054 := by exact prefixLift 2090054
  have htrace : WordTrace (prefixWord ++ tailWord_2090054) baseStart_2090054 baseEnd_2090054 := by
    simpa [prefixWord, tailWord_2090054, baseEnd_2090054] using wordTrace_append hprefix tailTrace_2090054
  have hstable : (prefixWord ++ tailWord_2090054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090054).length < 2 ^ (prefixWord ++ tailWord_2090054).sum := by decide
  have hdescent : baseEnd_2090054 < baseStart_2090054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090067 : List Nat := [1, 1, 1, 2, 1, 1, 2, 9, 1, 1, 3]
def baseStart_2090067 : Nat := 118140960795 + 2090067 * 2 ^ 59
def prefixEnd_2090067 : Nat := 4983230072969 + 3 ^ 40 * 2090067 * 2
def baseEnd_2090067 : Nat := 1073208971100779336950463

theorem tailTrace_2090067 : CollatzResearch.WordTrace tailWord_2090067 prefixEnd_2090067 1073208971100779336950463 := by
  unfold tailWord_2090067
  simp only [CollatzResearch.WordTrace]
  refine ⟨76231006119051688870068455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50820670746034459246712303 76231006119051688870068455)
  ·
    refine ⟨114346509178577533305102683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76231006119051688870068455 114346509178577533305102683)
    ·
      refine ⟨171519763767866299957654025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114346509178577533305102683 171519763767866299957654025)
      ·
        refine ⟨128639822825899724968240519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171519763767866299957654025 128639822825899724968240519)
        ·
          refine ⟨192959734238849587452360779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128639822825899724968240519 192959734238849587452360779)
          ·
            refine ⟨289439601358274381178541169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192959734238849587452360779 289439601358274381178541169)
            ·
              refine ⟨217079701018705785883905877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289439601358274381178541169 217079701018705785883905877)
              ·
                refine ⟨1271951373156479214163511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 217079701018705785883905877 1271951373156479214163511)
                ·
                  refine ⟨1907927059734718821245267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1271951373156479214163511 1907927059734718821245267)
                  ·
                    refine ⟨2861890589602078231867901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1907927059734718821245267 2861890589602078231867901)
                    ·
                      refine ⟨1073208971100779336950463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2861890589602078231867901 1073208971100779336950463)
                      ·
                        rfl

theorem cell23_2090067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 1, 1, 3].length) (baseStart_2090067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090067 prefixEnd_2090067 := by exact prefixLift 2090067
  have htrace : WordTrace (prefixWord ++ tailWord_2090067) baseStart_2090067 baseEnd_2090067 := by
    simpa [prefixWord, tailWord_2090067, baseEnd_2090067] using wordTrace_append hprefix tailTrace_2090067
  have hstable : (prefixWord ++ tailWord_2090067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090067).length < 2 ^ (prefixWord ++ tailWord_2090067).sum := by decide
  have hdescent : baseEnd_2090067 < baseStart_2090067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090073 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 5, 1, 4]
def baseStart_2090073 : Nat := 118140960795 + 2090073 * 2 ^ 59
def prefixEnd_2090073 : Nat := 4983230072969 + 3 ^ 40 * 2090073 * 2
def baseEnd_2090073 : Nat := 1073212051984706313475435

theorem tailTrace_2090073 : CollatzResearch.WordTrace tailWord_2090073 prefixEnd_2090073 1073212051984706313475435 := by
  unfold tailWord_2090073
  simp only [CollatzResearch.WordTrace]
  refine ⟨76231224957029951894786873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50820816638019967929857915 76231224957029951894786873)
  ·
    refine ⟨57173418717772463921090155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76231224957029951894786873 57173418717772463921090155)
    ·
      refine ⟨85760128076658695881635233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57173418717772463921090155 85760128076658695881635233)
      ·
        refine ⟨64320096057494021911226425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85760128076658695881635233 64320096057494021911226425)
        ·
          refine ⟨48240072043120516433419819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64320096057494021911226425 48240072043120516433419819)
          ·
            refine ⟨72360108064680774650129729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48240072043120516433419819 72360108064680774650129729)
            ·
              refine ⟨54270081048510580987597297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72360108064680774650129729 54270081048510580987597297)
              ·
                refine ⟨40702560786382935740697973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54270081048510580987597297 40702560786382935740697973)
                ·
                  refine ⟨3815865073723400225690435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40702560786382935740697973 3815865073723400225690435)
                  ·
                    refine ⟨5723797610585100338535653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3815865073723400225690435 5723797610585100338535653)
                    ·
                      refine ⟨1073212051984706313475435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5723797610585100338535653 1073212051984706313475435)
                      ·
                        rfl

theorem cell23_2090073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_2090073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090073 prefixEnd_2090073 := by exact prefixLift 2090073
  have htrace : WordTrace (prefixWord ++ tailWord_2090073) baseStart_2090073 baseEnd_2090073 := by
    simpa [prefixWord, tailWord_2090073, baseEnd_2090073] using wordTrace_append hprefix tailTrace_2090073
  have hstable : (prefixWord ++ tailWord_2090073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090073).length < 2 ^ (prefixWord ++ tailWord_2090073).sum := by decide
  have hdescent : baseEnd_2090073 < baseStart_2090073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090103 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_2090103 : Nat := 118140960795 + 2090103 * 2 ^ 59
def prefixEnd_2090103 : Nat := 4983230072969 + 3 ^ 40 * 2090103 * 2
def baseEnd_2090103 : Nat := 1073227456404341196100297

theorem tailTrace_2090103 : CollatzResearch.WordTrace tailWord_2090103 prefixEnd_2090103 1073227456404341196100297 := by
  unfold tailWord_2090103
  simp only [CollatzResearch.WordTrace]
  refine ⟨76232319146921267018378963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50821546097947511345585975 76232319146921267018378963)
  ·
    refine ⟨114348478720381900527568445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76232319146921267018378963 114348478720381900527568445)
    ·
      refine ⟨42880679520143212697838167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114348478720381900527568445 42880679520143212697838167)
      ·
        refine ⟨64321019280214819046757251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42880679520143212697838167 64321019280214819046757251)
        ·
          refine ⟨96481528920322228570135877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64321019280214819046757251 96481528920322228570135877)
          ·
            refine ⟨18090286672560417856900477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96481528920322228570135877 18090286672560417856900477)
            ·
              refine ⟨6783857502210156696337679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18090286672560417856900477 6783857502210156696337679)
              ·
                refine ⟨10175786253315235044506519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6783857502210156696337679 10175786253315235044506519)
                ·
                  refine ⟨15263679379972852566759779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10175786253315235044506519 15263679379972852566759779)
                  ·
                    refine ⟨22895519069959278850139669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15263679379972852566759779 22895519069959278850139669)
                    ·
                      refine ⟨1073227456404341196100297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22895519069959278850139669 1073227456404341196100297)
                      ·
                        rfl

theorem cell23_2090103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_2090103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090103 prefixEnd_2090103 := by exact prefixLift 2090103
  have htrace : WordTrace (prefixWord ++ tailWord_2090103) baseStart_2090103 baseEnd_2090103 := by
    simpa [prefixWord, tailWord_2090103, baseEnd_2090103] using wordTrace_append hprefix tailTrace_2090103
  have hstable : (prefixWord ++ tailWord_2090103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090103).length < 2 ^ (prefixWord ++ tailWord_2090103).sum := by decide
  have hdescent : baseEnd_2090103 < baseStart_2090103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090130 : List Nat := [3, 2, 3, 1, 1, 4, 9]
def baseStart_2090130 : Nat := 118140960795 + 2090130 * 2 ^ 59
def prefixEnd_2090130 : Nat := 4983230072969 + 3 ^ 40 * 2090130 * 2
def baseEnd_2090130 : Nat := 13249892844222377660033

theorem tailTrace_2090130 : CollatzResearch.WordTrace tailWord_2090130 prefixEnd_2090130 13249892844222377660033 := by
  unfold tailWord_2090130
  simp only [CollatzResearch.WordTrace]
  refine ⟨19058325979455862657402961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50822202611882300419741229 19058325979455862657402961)
  ·
    refine ⟨14293744484591896993052221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19058325979455862657402961 14293744484591896993052221)
    ·
      refine ⟨5360154181721961372394583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14293744484591896993052221 5360154181721961372394583)
      ·
        refine ⟨8040231272582942058591875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5360154181721961372394583 8040231272582942058591875)
        ·
          refine ⟨12060346908874413087887813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8040231272582942058591875 12060346908874413087887813)
          ·
            refine ⟨2261315045413952453978965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12060346908874413087887813 2261315045413952453978965)
            ·
              refine ⟨13249892844222377660033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2261315045413952453978965 13249892844222377660033)
              ·
                rfl

theorem cell23_2090130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 9].length) (baseStart_2090130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090130 prefixEnd_2090130 := by exact prefixLift 2090130
  have htrace : WordTrace (prefixWord ++ tailWord_2090130) baseStart_2090130 baseEnd_2090130 := by
    simpa [prefixWord, tailWord_2090130, baseEnd_2090130] using wordTrace_append hprefix tailTrace_2090130
  have hstable : (prefixWord ++ tailWord_2090130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090130).length < 2 ^ (prefixWord ++ tailWord_2090130).sum := by decide
  have hdescent : baseEnd_2090130 < baseStart_2090130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090151 : List Nat := [1, 1, 6, 2, 1, 3, 2, 1, 2, 4]
def baseStart_2090151 : Nat := 118140960795 + 2090151 * 2 ^ 59
def prefixEnd_2090151 : Nat := 4983230072969 + 3 ^ 40 * 2090151 * 2
def baseEnd_2090151 : Nat := 357750701158585669433359

theorem tailTrace_2090151 : CollatzResearch.WordTrace tailWord_2090151 prefixEnd_2090151 357750701158585669433359 := by
  unfold tailWord_2090151
  simp only [CollatzResearch.WordTrace]
  refine ⟨76234069850747371216126307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50822713233831580810750871 76234069850747371216126307)
  ·
    refine ⟨114351104776121056824189461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76234069850747371216126307 114351104776121056824189461)
    ·
      refine ⟨5360208036380674538633881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 114351104776121056824189461 5360208036380674538633881)
      ·
        refine ⟨4020156027285505903975411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5360208036380674538633881 4020156027285505903975411)
        ·
          refine ⟨6030234040928258855963117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4020156027285505903975411 6030234040928258855963117)
          ·
            refine ⟨2261337765348097070986169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6030234040928258855963117 2261337765348097070986169)
            ·
              refine ⟨1696003324011072803239627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2261337765348097070986169 1696003324011072803239627)
              ·
                refine ⟨2544004986016609204859441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1696003324011072803239627 2544004986016609204859441)
                ·
                  refine ⟨1908003739512456903644581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2544004986016609204859441 1908003739512456903644581)
                  ·
                    refine ⟨357750701158585669433359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1908003739512456903644581 357750701158585669433359)
                    ·
                      rfl

theorem cell23_2090151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_2090151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090151 prefixEnd_2090151 := by exact prefixLift 2090151
  have htrace : WordTrace (prefixWord ++ tailWord_2090151) baseStart_2090151 baseEnd_2090151 := by
    simpa [prefixWord, tailWord_2090151, baseEnd_2090151] using wordTrace_append hprefix tailTrace_2090151
  have hstable : (prefixWord ++ tailWord_2090151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090151).length < 2 ^ (prefixWord ++ tailWord_2090151).sum := by decide
  have hdescent : baseEnd_2090151 < baseStart_2090151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090167 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 3, 3, 2]
def baseStart_2090167 : Nat := 118140960795 + 2090167 * 2 ^ 59
def prefixEnd_2090167 : Nat := 4983230072969 + 3 ^ 40 * 2090167 * 2
def baseEnd_2090167 : Nat := 1073260319166228945700003

theorem tailTrace_2090167 : CollatzResearch.WordTrace tailWord_2090167 prefixEnd_2090167 1073260319166228945700003 := by
  unfold tailWord_2090167
  simp only [CollatzResearch.WordTrace]
  refine ⟨76234653418689405948708755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50823102279126270632472503 76234653418689405948708755)
  ·
    refine ⟨114351980128034108923063133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76234653418689405948708755 114351980128034108923063133)
    ·
      refine ⟨42881992548012790846148675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114351980128034108923063133 42881992548012790846148675)
      ·
        refine ⟨64322988822019186269223013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42881992548012790846148675 64322988822019186269223013)
        ·
          refine ⟨12060560404128597425479315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64322988822019186269223013 12060560404128597425479315)
          ·
            refine ⟨18090840606192896138218973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12060560404128597425479315 18090840606192896138218973)
            ·
              refine ⟨6784065227322336051832115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18090840606192896138218973 6784065227322336051832115)
              ·
                refine ⟨10176097840983504077748173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6784065227322336051832115 10176097840983504077748173)
                ·
                  refine ⟨3816036690368814029155565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10176097840983504077748173 3816036690368814029155565)
                  ·
                    refine ⟨1431013758888305260933337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3816036690368814029155565 1431013758888305260933337)
                    ·
                      refine ⟨1073260319166228945700003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1431013758888305260933337 1073260319166228945700003)
                      ·
                        rfl

theorem cell23_2090167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 3, 2].length) (baseStart_2090167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090167 prefixEnd_2090167 := by exact prefixLift 2090167
  have htrace : WordTrace (prefixWord ++ tailWord_2090167) baseStart_2090167 baseEnd_2090167 := by
    simpa [prefixWord, tailWord_2090167, baseEnd_2090167] using wordTrace_append hprefix tailTrace_2090167
  have hstable : (prefixWord ++ tailWord_2090167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090167).length < 2 ^ (prefixWord ++ tailWord_2090167).sum := by decide
  have hdescent : baseEnd_2090167 < baseStart_2090167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090178 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_2090178 : Nat := 118140960795 + 2090178 * 2 ^ 59
def prefixEnd_2090178 : Nat := 4983230072969 + 3 ^ 40 * 2090178 * 2
def baseEnd_2090178 : Nat := 1073265967453428402662453

theorem tailTrace_2090178 : CollatzResearch.WordTrace tailWord_2090178 prefixEnd_2090178 1073265967453428402662453 := by
  unfold tailWord_2090178
  simp only [CollatzResearch.WordTrace]
  refine ⟨19058763655412388706839797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50823369747766369884906125 19058763655412388706839797)
  ·
    refine ⟨1786759092694911441266231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19058763655412388706839797 1786759092694911441266231)
    ·
      refine ⟨2680138639042367161899347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1786759092694911441266231 2680138639042367161899347)
      ·
        refine ⟨4020207958563550742849021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2680138639042367161899347 4020207958563550742849021)
        ·
          refine ⟨1507577984461331528568383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4020207958563550742849021 1507577984461331528568383)
          ·
            refine ⟨2261366976691997292852575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507577984461331528568383 2261366976691997292852575)
            ·
              refine ⟨3392050465037995939278863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2261366976691997292852575 3392050465037995939278863)
              ·
                refine ⟨5088075697556993908918295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3392050465037995939278863 5088075697556993908918295)
                ·
                  refine ⟨7632113546335490863377443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5088075697556993908918295 7632113546335490863377443)
                  ·
                    refine ⟨11448170319503236295066165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7632113546335490863377443 11448170319503236295066165)
                    ·
                      refine ⟨1073265967453428402662453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11448170319503236295066165 1073265967453428402662453)
                      ·
                        rfl

theorem cell23_2090178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_2090178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090178 prefixEnd_2090178 := by exact prefixLift 2090178
  have htrace : WordTrace (prefixWord ++ tailWord_2090178) baseStart_2090178 baseEnd_2090178 := by
    simpa [prefixWord, tailWord_2090178, baseEnd_2090178] using wordTrace_append hprefix tailTrace_2090178
  have hstable : (prefixWord ++ tailWord_2090178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090178).length < 2 ^ (prefixWord ++ tailWord_2090178).sum := by decide
  have hdescent : baseEnd_2090178 < baseStart_2090178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090193 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_2090193 : Nat := 118140960795 + 2090193 * 2 ^ 59
def prefixEnd_2090193 : Nat := 4983230072969 + 3 ^ 40 * 2090193 * 2
def baseEnd_2090193 : Nat := 1073273669663245843974883

theorem tailTrace_2090193 : CollatzResearch.WordTrace tailWord_2090193 prefixEnd_2090193 1073273669663245843974883 := by
  unfold tailWord_2090193
  simp only [CollatzResearch.WordTrace]
  refine ⟨76235601716595212389155233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50823734477730141592770155 76235601716595212389155233)
  ·
    refine ⟨57176701287446409291866425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76235601716595212389155233 57176701287446409291866425)
    ·
      refine ⟨42882525965584806968899819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57176701287446409291866425 42882525965584806968899819)
      ·
        refine ⟨64323788948377210453349729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42882525965584806968899819 64323788948377210453349729)
        ·
          refine ⟨48242841711282907840012297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64323788948377210453349729 48242841711282907840012297)
          ·
            refine ⟨36182131283462180880009223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48242841711282907840012297 36182131283462180880009223)
            ·
              refine ⟨54273196925193271320013835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36182131283462180880009223 54273196925193271320013835)
              ·
                refine ⟨81409795387789906980020753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54273196925193271320013835 81409795387789906980020753)
                ·
                  refine ⟨61057346540842430235015565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81409795387789906980020753 61057346540842430235015565)
                  ·
                    refine ⟨22896504952815911338130837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61057346540842430235015565 22896504952815911338130837)
                    ·
                      refine ⟨1073273669663245843974883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22896504952815911338130837 1073273669663245843974883)
                      ·
                        rfl

theorem cell23_2090193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_2090193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090193 prefixEnd_2090193 := by exact prefixLift 2090193
  have htrace : WordTrace (prefixWord ++ tailWord_2090193) baseStart_2090193 baseEnd_2090193 := by
    simpa [prefixWord, tailWord_2090193, baseEnd_2090193] using wordTrace_append hprefix tailTrace_2090193
  have hstable : (prefixWord ++ tailWord_2090193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090193).length < 2 ^ (prefixWord ++ tailWord_2090193).sum := by decide
  have hdescent : baseEnd_2090193 < baseStart_2090193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090220 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 7]
def baseStart_2090220 : Nat := 118140960795 + 2090220 * 2 ^ 59
def prefixEnd_2090220 : Nat := 4983230072969 + 3 ^ 40 * 2090220 * 2
def baseEnd_2090220 : Nat := 119254170404546359815251

theorem tailTrace_2090220 : CollatzResearch.WordTrace tailWord_2090220 prefixEnd_2090220 119254170404546359815251 := by
  unfold tailWord_2090220
  simp only [CollatzResearch.WordTrace]
  refine ⟨38118293243748698000194057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50824390991664930666925409 38118293243748698000194057)
  ·
    refine ⟨28588719932811523500145543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38118293243748698000194057 28588719932811523500145543)
    ·
      refine ⟨42883079899217285250218315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28588719932811523500145543 42883079899217285250218315)
      ·
        refine ⟨64324619848825927875327473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42883079899217285250218315 64324619848825927875327473)
        ·
          refine ⟨48243464886619445906495605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64324619848825927875327473 48243464886619445906495605)
          ·
            refine ⟨4522824833120573053733963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48243464886619445906495605 4522824833120573053733963)
            ·
              refine ⟨6784237249680859580600945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4522824833120573053733963 6784237249680859580600945)
              ·
                refine ⟨5088177937260644685450709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6784237249680859580600945 5088177937260644685450709)
                ·
                  refine ⟨119254170404546359815251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5088177937260644685450709 119254170404546359815251)
                  ·
                    rfl

theorem cell23_2090220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_2090220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090220 prefixEnd_2090220 := by exact prefixLift 2090220
  have htrace : WordTrace (prefixWord ++ tailWord_2090220) baseStart_2090220 baseEnd_2090220 := by
    simpa [prefixWord, tailWord_2090220, baseEnd_2090220] using wordTrace_append hprefix tailTrace_2090220
  have hstable : (prefixWord ++ tailWord_2090220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090220).length < 2 ^ (prefixWord ++ tailWord_2090220).sum := by decide
  have hdescent : baseEnd_2090220 < baseStart_2090220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090230 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2090230 : Nat := 118140960795 + 2090230 * 2 ^ 59
def prefixEnd_2090230 : Nat := 4983230072969 + 3 ^ 40 * 2090230 * 2
def baseEnd_2090230 : Nat := 1073292668447462199212213

theorem tailTrace_2090230 : CollatzResearch.WordTrace tailWord_2090230 prefixEnd_2090230 1073292668447462199212213 := by
  unfold tailWord_2090230
  simp only [CollatzResearch.WordTrace]
  refine ⟨4764809451091322981765759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50824634144974111805501429 4764809451091322981765759)
  ·
    refine ⟨7147214176636984472648639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4764809451091322981765759 7147214176636984472648639)
    ·
      refine ⟨10720821264955476708972959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7147214176636984472648639 10720821264955476708972959)
      ·
        refine ⟨16081231897433215063459439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10720821264955476708972959 16081231897433215063459439)
        ·
          refine ⟨24121847846149822595189159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16081231897433215063459439 24121847846149822595189159)
          ·
            refine ⟨36182771769224733892783739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24121847846149822595189159 36182771769224733892783739)
            ·
              refine ⟨54274157653837100839175609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36182771769224733892783739 54274157653837100839175609)
              ·
                refine ⟨40705618240377825629381707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54274157653837100839175609 40705618240377825629381707)
                ·
                  refine ⟨61058427360566738444072561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40705618240377825629381707 61058427360566738444072561)
                  ·
                    refine ⟨45793820520425053833054421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61058427360566738444072561 45793820520425053833054421)
                    ·
                      refine ⟨1073292668447462199212213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45793820520425053833054421 1073292668447462199212213)
                      ·
                        rfl

theorem cell23_2090230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2090230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090230 prefixEnd_2090230 := by exact prefixLift 2090230
  have htrace : WordTrace (prefixWord ++ tailWord_2090230) baseStart_2090230 baseEnd_2090230 := by
    simpa [prefixWord, tailWord_2090230, baseEnd_2090230] using wordTrace_append hprefix tailTrace_2090230
  have hstable : (prefixWord ++ tailWord_2090230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090230).length < 2 ^ (prefixWord ++ tailWord_2090230).sum := by decide
  have hdescent : baseEnd_2090230 < baseStart_2090230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090248 : List Nat := [2, 1, 3, 2, 4, 2, 1, 2, 2, 2, 2]
def baseStart_2090248 : Nat := 118140960795 + 2090248 * 2 ^ 59
def prefixEnd_2090248 : Nat := 4983230072969 + 3 ^ 40 * 2090248 * 2
def baseEnd_2090248 : Nat := 1073301911099243128787131

theorem tailTrace_2090248 : CollatzResearch.WordTrace tailWord_2090248 prefixEnd_2090248 1073301911099243128787131 := by
  unfold tailWord_2090248
  simp only [CollatzResearch.WordTrace]
  refine ⟨38118803865697978391203699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50825071820930637854938265 38118803865697978391203699)
  ·
    refine ⟨57178205798546967586805549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38118803865697978391203699 57178205798546967586805549)
    ·
      refine ⟨21441827174455112845052081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57178205798546967586805549 21441827174455112845052081)
      ·
        refine ⟨16081370380841334633789061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21441827174455112845052081 16081370380841334633789061)
        ·
          refine ⟨3015256946407750243835449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16081370380841334633789061 3015256946407750243835449)
          ·
            refine ⟨2261442709805812682876587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3015256946407750243835449 2261442709805812682876587)
            ·
              refine ⟨3392164064708719024314881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2261442709805812682876587 3392164064708719024314881)
              ·
                refine ⟨2544123048531539268236161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3392164064708719024314881 2544123048531539268236161)
                ·
                  refine ⟨1908092286398654451177121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2544123048531539268236161 1908092286398654451177121)
                  ·
                    refine ⟨1431069214798990838382841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1908092286398654451177121 1431069214798990838382841)
                    ·
                      refine ⟨1073301911099243128787131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1431069214798990838382841 1073301911099243128787131)
                      ·
                        rfl

theorem cell23_2090248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_2090248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090248 prefixEnd_2090248 := by exact prefixLift 2090248
  have htrace : WordTrace (prefixWord ++ tailWord_2090248) baseStart_2090248 baseEnd_2090248 := by
    simpa [prefixWord, tailWord_2090248, baseEnd_2090248] using wordTrace_append hprefix tailTrace_2090248
  have hstable : (prefixWord ++ tailWord_2090248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090248).length < 2 ^ (prefixWord ++ tailWord_2090248).sum := by decide
  have hdescent : baseEnd_2090248 < baseStart_2090248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090250 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 4, 5]
def baseStart_2090250 : Nat := 118140960795 + 2090250 * 2 ^ 59
def prefixEnd_2090250 : Nat := 4983230072969 + 3 ^ 40 * 2090250 * 2
def baseEnd_2090250 : Nat := 357767646020184040320707

theorem tailTrace_2090250 : CollatzResearch.WordTrace tailWord_2090250 prefixEnd_2090250 357767646020184040320707 := by
  unfold tailWord_2090250
  simp only [CollatzResearch.WordTrace]
  refine ⟨19059420169347177780995051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50825120451592474082653469 19059420169347177780995051)
  ·
    refine ⟨28589130254020766671492577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19059420169347177780995051 28589130254020766671492577)
    ·
      refine ⟨21441847690515575003619433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28589130254020766671492577 21441847690515575003619433)
      ·
        refine ⟨16081385767886681252714575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21441847690515575003619433 16081385767886681252714575)
        ·
          refine ⟨24122078651830021879071863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16081385767886681252714575 24122078651830021879071863)
          ·
            refine ⟨36183117977745032818607795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24122078651830021879071863 36183117977745032818607795)
            ·
              refine ⟨54274676966617549227911693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36183117977745032818607795 54274676966617549227911693)
              ·
                refine ⟨20353003862481580960466885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54274676966617549227911693 20353003862481580960466885)
                ·
                  refine ⟨3816188224215296430087541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20353003862481580960466885 3816188224215296430087541)
                  ·
                    refine ⟨357767646020184040320707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3816188224215296430087541 357767646020184040320707)
                    ·
                      rfl

theorem cell23_2090250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_2090250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090250 prefixEnd_2090250 := by exact prefixLift 2090250
  have htrace : WordTrace (prefixWord ++ tailWord_2090250) baseStart_2090250 baseEnd_2090250 := by
    simpa [prefixWord, tailWord_2090250, baseEnd_2090250] using wordTrace_append hprefix tailTrace_2090250
  have hstable : (prefixWord ++ tailWord_2090250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090250).length < 2 ^ (prefixWord ++ tailWord_2090250).sum := by decide
  have hdescent : baseEnd_2090250 < baseStart_2090250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090314 : List Nat := [3, 1, 2, 1, 1, 1, 1, 8, 1, 4]
def baseStart_2090314 : Nat := 118140960795 + 2090314 * 2 ^ 59
def prefixEnd_2090314 : Nat := 4983230072969 + 3 ^ 40 * 2090314 * 2
def baseEnd_2090314 : Nat := 357778600274146623520609

theorem tailTrace_2090314 : CollatzResearch.WordTrace tailWord_2090314 prefixEnd_2090314 357778600274146623520609 := by
  unfold tailWord_2090314
  simp only [CollatzResearch.WordTrace]
  refine ⟨19060003737289212513577499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50826676632771233369539997 19060003737289212513577499)
  ·
    refine ⟨28590005605933818770366249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19060003737289212513577499 28590005605933818770366249)
    ·
      refine ⟨21442504204450364077774687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28590005605933818770366249 21442504204450364077774687)
      ·
        refine ⟨32163756306675546116662031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21442504204450364077774687 32163756306675546116662031)
        ·
          refine ⟨48245634460013319174993047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32163756306675546116662031 48245634460013319174993047)
          ·
            refine ⟨72368451690019978762489571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48245634460013319174993047 72368451690019978762489571)
            ·
              refine ⟨108552677535029968143734357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72368451690019978762489571 108552677535029968143734357)
              ·
                refine ⟨1272101689863632439184387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 108552677535029968143734357 1272101689863632439184387)
                ·
                  refine ⟨1908152534795448658776581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272101689863632439184387 1908152534795448658776581)
                  ·
                    refine ⟨357778600274146623520609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1908152534795448658776581 357778600274146623520609)
                    ·
                      rfl

theorem cell23_2090314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_2090314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090314 prefixEnd_2090314 := by exact prefixLift 2090314
  have htrace : WordTrace (prefixWord ++ tailWord_2090314) baseStart_2090314 baseEnd_2090314 := by
    simpa [prefixWord, tailWord_2090314, baseEnd_2090314] using wordTrace_append hprefix tailTrace_2090314
  have hstable : (prefixWord ++ tailWord_2090314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090314).length < 2 ^ (prefixWord ++ tailWord_2090314).sum := by decide
  have hdescent : baseEnd_2090314 < baseStart_2090314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090327 : List Nat := [1, 1, 3, 2, 3, 3, 1, 3, 6]
def baseStart_2090327 : Nat := 118140960795 + 2090327 * 2 ^ 59
def prefixEnd_2090327 : Nat := 4983230072969 + 3 ^ 40 * 2090327 * 2
def baseEnd_2090327 : Nat := 119260275118994257744363

theorem tailTrace_2090327 : CollatzResearch.WordTrace tailWord_2090327 prefixEnd_2090327 119260275118994257744363 := by
  unfold tailWord_2090327
  simp only [CollatzResearch.WordTrace]
  refine ⟨76240489098109753274533235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50826992732073168849688823 76240489098109753274533235)
  ·
    refine ⟨114360733647164629911799853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76240489098109753274533235 114360733647164629911799853)
    ·
      refine ⟨42885275117686736216924945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114360733647164629911799853 42885275117686736216924945)
      ·
        refine ⟨32163956338265052162693709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42885275117686736216924945 32163956338265052162693709)
        ·
          refine ⟨12061483626849394561010141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32163956338265052162693709 12061483626849394561010141)
          ·
            refine ⟨4523056360068522960378803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12061483626849394561010141 4523056360068522960378803)
            ·
              refine ⟨6784584540102784440568205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523056360068522960378803 6784584540102784440568205)
              ·
                refine ⟨2544219202538544165213077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6784584540102784440568205 2544219202538544165213077)
                ·
                  refine ⟨119260275118994257744363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2544219202538544165213077 119260275118994257744363)
                  ·
                    rfl

theorem cell23_2090327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 6].length) (baseStart_2090327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090327 prefixEnd_2090327 := by exact prefixLift 2090327
  have htrace : WordTrace (prefixWord ++ tailWord_2090327) baseStart_2090327 baseEnd_2090327 := by
    simpa [prefixWord, tailWord_2090327, baseEnd_2090327] using wordTrace_append hprefix tailTrace_2090327
  have hstable : (prefixWord ++ tailWord_2090327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090327).length < 2 ^ (prefixWord ++ tailWord_2090327).sum := by decide
  have hdescent : baseEnd_2090327 < baseStart_2090327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090330 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_2090330 : Nat := 118140960795 + 2090330 * 2 ^ 59
def prefixEnd_2090330 : Nat := 4983230072969 + 3 ^ 40 * 2090330 * 2
def baseEnd_2090330 : Nat := 1073344016512911807961753

theorem tailTrace_2090330 : CollatzResearch.WordTrace tailWord_2090330 prefixEnd_2090330 1073344016512911807961753 := by
  unfold tailWord_2090330
  simp only [CollatzResearch.WordTrace]
  refine ⟨19060149629274721196723111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50827065678065923191261629 19060149629274721196723111)
  ·
    refine ⟨28590224443912081795084667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19060149629274721196723111 28590224443912081795084667)
    ·
      refine ⟨42885336665868122692627001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28590224443912081795084667 42885336665868122692627001)
      ·
        refine ⟨32164002499401092019470251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42885336665868122692627001 32164002499401092019470251)
        ·
          refine ⟨48246003749101638029205377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32164002499401092019470251 48246003749101638029205377)
          ·
            refine ⟨36184502811826228521904033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48246003749101638029205377 36184502811826228521904033)
            ·
              refine ⟨27138377108869671391428025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36184502811826228521904033 27138377108869671391428025)
              ·
                refine ⟨20353782831652253543571019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27138377108869671391428025 20353782831652253543571019)
                ·
                  refine ⟨30530674247478380315356529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20353782831652253543571019 30530674247478380315356529)
                  ·
                    refine ⟨22898005685608785236517397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30530674247478380315356529 22898005685608785236517397)
                    ·
                      refine ⟨1073344016512911807961753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22898005685608785236517397 1073344016512911807961753)
                      ·
                        rfl

theorem cell23_2090330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_2090330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090330 prefixEnd_2090330 := by exact prefixLift 2090330
  have htrace : WordTrace (prefixWord ++ tailWord_2090330) baseStart_2090330 baseEnd_2090330 := by
    simpa [prefixWord, tailWord_2090330, baseEnd_2090330] using wordTrace_append hprefix tailTrace_2090330
  have hstable : (prefixWord ++ tailWord_2090330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090330).length < 2 ^ (prefixWord ++ tailWord_2090330).sum := by decide
  have hdescent : baseEnd_2090330 < baseStart_2090330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090364 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 2, 3, 2]
def baseStart_2090364 : Nat := 118140960795 + 2090364 * 2 ^ 59
def prefixEnd_2090364 : Nat := 4983230072969 + 3 ^ 40 * 2090364 * 2
def baseEnd_2090364 : Nat := 1073361474855164674936597

theorem tailTrace_2090364 : CollatzResearch.WordTrace tailWord_2090364 prefixEnd_2090364 1073361474855164674936597 := by
  unfold tailWord_2090364
  simp only [CollatzResearch.WordTrace]
  refine ⟨38120919299487854296815073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50827892399317139062420097 38120919299487854296815073)
  ·
    refine ⟨28590689474615890722611305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38120919299487854296815073 28590689474615890722611305)
    ·
      refine ⟨21443017105961918041958479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28590689474615890722611305 21443017105961918041958479)
      ·
        refine ⟨32164525658942877062937719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21443017105961918041958479 32164525658942877062937719)
        ·
          refine ⟨48246788488414315594406579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32164525658942877062937719 48246788488414315594406579)
          ·
            refine ⟨72370182732621473391609869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48246788488414315594406579 72370182732621473391609869)
            ·
              refine ⟨27138818524733052521853701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72370182732621473391609869 27138818524733052521853701)
              ·
                refine ⟨5088528473387447347847569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27138818524733052521853701 5088528473387447347847569)
                ·
                  refine ⟨3816396355040585510885677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5088528473387447347847569 3816396355040585510885677)
                  ·
                    refine ⟨1431148633140219566582129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3816396355040585510885677 1431148633140219566582129)
                    ·
                      refine ⟨1073361474855164674936597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1431148633140219566582129 1073361474855164674936597)
                      ·
                        rfl

theorem cell23_2090364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_2090364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090364 prefixEnd_2090364 := by exact prefixLift 2090364
  have htrace : WordTrace (prefixWord ++ tailWord_2090364) baseStart_2090364 baseEnd_2090364 := by
    simpa [prefixWord, tailWord_2090364, baseEnd_2090364] using wordTrace_append hprefix tailTrace_2090364
  have hstable : (prefixWord ++ tailWord_2090364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090364).length < 2 ^ (prefixWord ++ tailWord_2090364).sum := by decide
  have hdescent : baseEnd_2090364 < baseStart_2090364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090394 : List Nat := [3, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4]
def baseStart_2090394 : Nat := 118140960795 + 2090394 * 2 ^ 59
def prefixEnd_2090394 : Nat := 4983230072969 + 3 ^ 40 * 2090394 * 2
def baseEnd_2090394 : Nat := 1073376879274799557561459

theorem tailTrace_2090394 : CollatzResearch.WordTrace tailWord_2090394 prefixEnd_2090394 1073376879274799557561459 := by
  unfold tailWord_2090394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19060733197216755929305559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50828621859244682478148157 19060733197216755929305559)
  ·
    refine ⟨28591099795825133893958339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19060733197216755929305559 28591099795825133893958339)
    ·
      refine ⟨42886649693737700840937509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28591099795825133893958339 42886649693737700840937509)
      ·
        refine ⟨8041246817575818907675783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42886649693737700840937509 8041246817575818907675783)
        ·
          refine ⟨12061870226363728361513675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8041246817575818907675783 12061870226363728361513675)
          ·
            refine ⟨18092805339545592542270513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12061870226363728361513675 18092805339545592542270513)
            ·
              refine ⟨13569604004659194406702885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18092805339545592542270513 13569604004659194406702885)
              ·
                refine ⟨2544300750873598951256791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13569604004659194406702885 2544300750873598951256791)
                ·
                  refine ⟨3816451126310398426885187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544300750873598951256791 3816451126310398426885187)
                  ·
                    refine ⟨5724676689465597640327781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3816451126310398426885187 5724676689465597640327781)
                    ·
                      refine ⟨1073376879274799557561459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5724676689465597640327781 1073376879274799557561459)
                      ·
                        rfl

theorem cell23_2090394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_2090394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090394 prefixEnd_2090394 := by exact prefixLift 2090394
  have htrace : WordTrace (prefixWord ++ tailWord_2090394) baseStart_2090394 baseEnd_2090394 := by
    simpa [prefixWord, tailWord_2090394, baseEnd_2090394] using wordTrace_append hprefix tailTrace_2090394
  have hstable : (prefixWord ++ tailWord_2090394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090394).length < 2 ^ (prefixWord ++ tailWord_2090394).sum := by decide
  have hdescent : baseEnd_2090394 < baseStart_2090394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090398 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_2090398 : Nat := 118140960795 + 2090398 * 2 ^ 59
def prefixEnd_2090398 : Nat := 4983230072969 + 3 ^ 40 * 2090398 * 2
def baseEnd_2090398 : Nat := 1073378933197417541911441

theorem tailTrace_2090398 : CollatzResearch.WordTrace tailWord_2090398 prefixEnd_2090398 1073378933197417541911441 := by
  unfold tailWord_2090398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9530384835106566550045981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50828719120568354933578565 9530384835106566550045981)
  ·
    refine ⟨3573894313164962456267243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9530384835106566550045981 3573894313164962456267243)
    ·
      refine ⟨5360841469747443684400865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3573894313164962456267243 5360841469747443684400865)
      ·
        refine ⟨4020631102310582763300649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5360841469747443684400865 4020631102310582763300649)
        ·
          refine ⟨3015473326732937072475487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4020631102310582763300649 3015473326732937072475487)
          ·
            refine ⟨4523209990099405608713231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015473326732937072475487 4523209990099405608713231)
            ·
              refine ⟨6784814985149108413069847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523209990099405608713231 6784814985149108413069847)
              ·
                refine ⟨10177222477723662619604771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6784814985149108413069847 10177222477723662619604771)
                ·
                  refine ⟨15265833716585493929407157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10177222477723662619604771 15265833716585493929407157)
                  ·
                    refine ⟨1431171910929890055881921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15265833716585493929407157 1431171910929890055881921)
                    ·
                      refine ⟨1073378933197417541911441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1431171910929890055881921 1073378933197417541911441)
                      ·
                        rfl

theorem cell23_2090398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_2090398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090398 prefixEnd_2090398 := by exact prefixLift 2090398
  have htrace : WordTrace (prefixWord ++ tailWord_2090398) baseStart_2090398 baseEnd_2090398 := by
    simpa [prefixWord, tailWord_2090398, baseEnd_2090398] using wordTrace_append hprefix tailTrace_2090398
  have hstable : (prefixWord ++ tailWord_2090398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090398).length < 2 ^ (prefixWord ++ tailWord_2090398).sum := by decide
  have hdescent : baseEnd_2090398 < baseStart_2090398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090421 : List Nat := [1, 3, 3, 2, 2, 1, 3, 2, 2, 4]
def baseStart_2090421 : Nat := 118140960795 + 2090421 * 2 ^ 59
def prefixEnd_2090421 : Nat := 4983230072969 + 3 ^ 40 * 2090421 * 2
def baseEnd_2090421 : Nat := 357796914417490317307945

theorem tailTrace_2090421 : CollatzResearch.WordTrace tailWord_2090421 prefixEnd_2090421 357796914417490317307945 := by
  unfold tailWord_2090421
  simp only [CollatzResearch.WordTrace]
  refine ⟨76243917559769207328455117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50829278373179471552303411 76243917559769207328455117)
  ·
    refine ⟨28591469084913452748170669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76243917559769207328455117 28591469084913452748170669)
    ·
      refine ⟨10721800906842544780564001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28591469084913452748170669 10721800906842544780564001)
      ·
        refine ⟨8041350680131908585423001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10721800906842544780564001 8041350680131908585423001)
        ·
          refine ⟨6031013010098931439067251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8041350680131908585423001 6031013010098931439067251)
          ·
            refine ⟨9046519515148397158600877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6031013010098931439067251 9046519515148397158600877)
            ·
              refine ⟨3392444818180648934475329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9046519515148397158600877 3392444818180648934475329)
              ·
                refine ⟨2544333613635486700856497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3392444818180648934475329 2544333613635486700856497)
                ·
                  refine ⟨1908250210226615025642373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2544333613635486700856497 1908250210226615025642373)
                  ·
                    refine ⟨357796914417490317307945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1908250210226615025642373 357796914417490317307945)
                    ·
                      rfl

theorem cell23_2090421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_2090421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090421 prefixEnd_2090421 := by exact prefixLift 2090421
  have htrace : WordTrace (prefixWord ++ tailWord_2090421) baseStart_2090421 baseEnd_2090421 := by
    simpa [prefixWord, tailWord_2090421, baseEnd_2090421] using wordTrace_append hprefix tailTrace_2090421
  have hstable : (prefixWord ++ tailWord_2090421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090421).length < 2 ^ (prefixWord ++ tailWord_2090421).sum := by decide
  have hdescent : baseEnd_2090421 < baseStart_2090421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090457 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 2, 2, 5]
def baseStart_2090457 : Nat := 118140960795 + 2090457 * 2 ^ 59
def prefixEnd_2090457 : Nat := 4983230072969 + 3 ^ 40 * 2090457 * 2
def baseEnd_2090457 : Nat := 1073409228556032811073669

theorem tailTrace_2090457 : CollatzResearch.WordTrace tailWord_2090457 prefixEnd_2090457 1073409228556032811073669 := by
  unfold tailWord_2090457
  simp only [CollatzResearch.WordTrace]
  refine ⟨76245230587638785476765625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50830153725092523651177083 76245230587638785476765625)
  ·
    refine ⟨57183922940729089107574219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76245230587638785476765625 57183922940729089107574219)
    ·
      refine ⟨85775884411093633661361329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57183922940729089107574219 85775884411093633661361329)
      ·
        refine ⟨64331913308320225246020997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85775884411093633661361329 64331913308320225246020997)
        ·
          refine ⟨12062233745310042233628937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64331913308320225246020997 12062233745310042233628937)
          ·
            refine ⟨9046675308982531675221703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12062233745310042233628937 9046675308982531675221703)
            ·
              refine ⟨13570012963473797512832555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046675308982531675221703 13570012963473797512832555)
              ·
                refine ⟨20355019445210696269248833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13570012963473797512832555 20355019445210696269248833)
                ·
                  refine ⟨15266264583908022201936625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20355019445210696269248833 15266264583908022201936625)
                  ·
                    refine ⟨11449698437931016651452469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15266264583908022201936625 11449698437931016651452469)
                    ·
                      refine ⟨1073409228556032811073669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11449698437931016651452469 1073409228556032811073669)
                      ·
                        rfl

theorem cell23_2090457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_2090457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090457 prefixEnd_2090457 := by exact prefixLift 2090457
  have htrace : WordTrace (prefixWord ++ tailWord_2090457) baseStart_2090457 baseEnd_2090457 := by
    simpa [prefixWord, tailWord_2090457, baseEnd_2090457] using wordTrace_append hprefix tailTrace_2090457
  have hstable : (prefixWord ++ tailWord_2090457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090457).length < 2 ^ (prefixWord ++ tailWord_2090457).sum := by decide
  have hdescent : baseEnd_2090457 < baseStart_2090457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090461 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_2090461 : Nat := 118140960795 + 2090461 * 2 ^ 59
def prefixEnd_2090461 : Nat := 4983230072969 + 3 ^ 40 * 2090461 * 2
def baseEnd_2090461 : Nat := 1073411282478650795423651

theorem tailTrace_2090461 : CollatzResearch.WordTrace tailWord_2090461 prefixEnd_2090461 1073411282478650795423651 := by
  unfold tailWord_2090461
  simp only [CollatzResearch.WordTrace]
  refine ⟨76245376479624294159911237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50830250986416196106607491 76245376479624294159911237)
  ·
    refine ⟨14296008089929555154983357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76245376479624294159911237 14296008089929555154983357)
    ·
      refine ⟨5361003033723583183118759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14296008089929555154983357 5361003033723583183118759)
      ·
        refine ⟨8041504550585374774678139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361003033723583183118759 8041504550585374774678139)
        ·
          refine ⟨12062256825878062162017209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8041504550585374774678139 12062256825878062162017209)
          ·
            refine ⟨9046692619408546621512907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12062256825878062162017209 9046692619408546621512907)
            ·
              refine ⟨13570038929112819932269361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046692619408546621512907 13570038929112819932269361)
              ·
                refine ⟨10177529196834614949202021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13570038929112819932269361 10177529196834614949202021)
                ·
                  refine ⟨1908286724406490302975379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10177529196834614949202021 1908286724406490302975379)
                  ·
                    refine ⟨2862430086609735454463069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1908286724406490302975379 2862430086609735454463069)
                    ·
                      refine ⟨1073411282478650795423651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2862430086609735454463069 1073411282478650795423651)
                      ·
                        rfl

theorem cell23_2090461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_2090461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090461 prefixEnd_2090461 := by exact prefixLift 2090461
  have htrace : WordTrace (prefixWord ++ tailWord_2090461) baseStart_2090461 baseEnd_2090461 := by
    simpa [prefixWord, tailWord_2090461, baseEnd_2090461] using wordTrace_append hprefix tailTrace_2090461
  have hstable : (prefixWord ++ tailWord_2090461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090461).length < 2 ^ (prefixWord ++ tailWord_2090461).sum := by decide
  have hdescent : baseEnd_2090461 < baseStart_2090461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090561 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_2090561 : Nat := 118140960795 + 2090561 * 2 ^ 59
def prefixEnd_2090561 : Nat := 4983230072969 + 3 ^ 40 * 2090561 * 2
def baseEnd_2090561 : Nat := 1073462630544100404173191

theorem tailTrace_2090561 : CollatzResearch.WordTrace tailWord_2090561 prefixEnd_2090561 1073462630544100404173191 := by
  unfold tailWord_2090561
  simp only [CollatzResearch.WordTrace]
  refine ⟨76249023779262011238551537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50832682519508007492367691 76249023779262011238551537)
  ·
    refine ⟨57186767834446508428913653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76249023779262011238551537 57186767834446508428913653)
    ·
      refine ⟨5361259484479360165210655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57186767834446508428913653 5361259484479360165210655)
      ·
        refine ⟨8041889226719040247815983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361259484479360165210655 8041889226719040247815983)
        ·
          refine ⟨12062833840078560371723975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8041889226719040247815983 12062833840078560371723975)
          ·
            refine ⟨18094250760117840557585963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12062833840078560371723975 18094250760117840557585963)
            ·
              refine ⟨27141376140176760836378945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18094250760117840557585963 27141376140176760836378945)
              ·
                refine ⟨20356032105132570627284209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27141376140176760836378945 20356032105132570627284209)
                ·
                  refine ⟨15267024078849427970463157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20356032105132570627284209 15267024078849427970463157)
                  ·
                    refine ⟨1431283507392133872230921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15267024078849427970463157 1431283507392133872230921)
                    ·
                      refine ⟨1073462630544100404173191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1431283507392133872230921 1073462630544100404173191)
                      ·
                        rfl

theorem cell23_2090561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_2090561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090561 prefixEnd_2090561 := by exact prefixLift 2090561
  have htrace : WordTrace (prefixWord ++ tailWord_2090561) baseStart_2090561 baseEnd_2090561 := by
    simpa [prefixWord, tailWord_2090561, baseEnd_2090561] using wordTrace_append hprefix tailTrace_2090561
  have hstable : (prefixWord ++ tailWord_2090561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090561).length < 2 ^ (prefixWord ++ tailWord_2090561).sum := by decide
  have hdescent : baseEnd_2090561 < baseStart_2090561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090584 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 7, 4]
def baseStart_2090584 : Nat := 118140960795 + 2090584 * 2 ^ 59
def prefixEnd_2090584 : Nat := 4983230072969 + 3 ^ 40 * 2090584 * 2
def baseEnd_2090584 : Nat := 357824813533051271395195

theorem tailTrace_2090584 : CollatzResearch.WordTrace tailWord_2090584 prefixEnd_2090584 357824813533051271395195 := by
  unfold tailWord_2090584
  simp only [CollatzResearch.WordTrace]
  refine ⟨38124931329089343083319403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50833241772119124111092537 38124931329089343083319403)
  ·
    refine ⟨57187396993634014624979105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38124931329089343083319403 57187396993634014624979105)
    ·
      refine ⟨42890547745225510968734329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57187396993634014624979105 42890547745225510968734329)
      ·
        refine ⟨32167910808919133226550747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42890547745225510968734329 32167910808919133226550747)
        ·
          refine ⟨48251866213378699839826121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32167910808919133226550747 48251866213378699839826121)
          ·
            refine ⟨36188899660034024879869591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48251866213378699839826121 36188899660034024879869591)
            ·
              refine ⟨54283349490051037319804387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36188899660034024879869591 54283349490051037319804387)
              ·
                refine ⟨81425024235076555979706581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54283349490051037319804387 81425024235076555979706581)
                ·
                  refine ⟨1908399005509606780774373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 81425024235076555979706581 1908399005509606780774373)
                  ·
                    refine ⟨357824813533051271395195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1908399005509606780774373 357824813533051271395195)
                    ·
                      rfl

theorem cell23_2090584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_2090584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090584 prefixEnd_2090584 := by exact prefixLift 2090584
  have htrace : WordTrace (prefixWord ++ tailWord_2090584) baseStart_2090584 baseEnd_2090584 := by
    simpa [prefixWord, tailWord_2090584, baseEnd_2090584] using wordTrace_append hprefix tailTrace_2090584
  have hstable : (prefixWord ++ tailWord_2090584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090584).length < 2 ^ (prefixWord ++ tailWord_2090584).sum := by decide
  have hdescent : baseEnd_2090584 < baseStart_2090584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090624 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 3]
def baseStart_2090624 : Nat := 118140960795 + 2090624 * 2 ^ 59
def prefixEnd_2090624 : Nat := 4983230072969 + 3 ^ 40 * 2090624 * 2
def baseEnd_2090624 : Nat := 1073494979825333657685401

theorem tailTrace_2090624 : CollatzResearch.WordTrace tailWord_2090624 prefixEnd_2090624 1073494979825333657685401 := by
  unfold tailWord_2090624
  simp only [CollatzResearch.WordTrace]
  refine ⟨38125660789016886499047463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50834214385355848665396617 38125660789016886499047463)
  ·
    refine ⟨57188491183525329748571195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38125660789016886499047463 57188491183525329748571195)
    ·
      refine ⟨85782736775287994622856793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57188491183525329748571195 85782736775287994622856793)
      ·
        refine ⟨64337052581465995967142595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85782736775287994622856793 64337052581465995967142595)
        ·
          refine ⟨96505578872198993950713893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64337052581465995967142595 96505578872198993950713893)
          ·
            refine ⟨18094796038537311365758855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96505578872198993950713893 18094796038537311365758855)
            ·
              refine ⟨27142194057805967048638283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18094796038537311365758855 27142194057805967048638283)
              ·
                refine ⟨40713291086708950572957425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27142194057805967048638283 40713291086708950572957425)
                ·
                  refine ⟨30534968315031712929718069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40713291086708950572957425 30534968315031712929718069)
                  ·
                    refine ⟨2862653279534223087161069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30534968315031712929718069 2862653279534223087161069)
                    ·
                      refine ⟨1073494979825333657685401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2862653279534223087161069 1073494979825333657685401)
                      ·
                        rfl

theorem cell23_2090624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_2090624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090624 prefixEnd_2090624 := by exact prefixLift 2090624
  have htrace : WordTrace (prefixWord ++ tailWord_2090624) baseStart_2090624 baseEnd_2090624 := by
    simpa [prefixWord, tailWord_2090624, baseEnd_2090624] using wordTrace_append hprefix tailTrace_2090624
  have hstable : (prefixWord ++ tailWord_2090624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090624).length < 2 ^ (prefixWord ++ tailWord_2090624).sum := by decide
  have hdescent : baseEnd_2090624 < baseStart_2090624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090652 : List Nat := [2, 2, 3, 2, 3, 1, 3, 2, 1, 4]
def baseStart_2090652 : Nat := 118140960795 + 2090652 * 2 ^ 59
def prefixEnd_2090652 : Nat := 4983230072969 + 3 ^ 40 * 2090652 * 2
def baseEnd_2090652 : Nat := 357836452427886516045091

theorem tailTrace_2090652 : CollatzResearch.WordTrace tailWord_2090652 prefixEnd_2090652 357836452427886516045091 := by
  unfold tailWord_2090652
  simp only [CollatzResearch.WordTrace]
  refine ⟨38126171410966166890057105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50834895214621555853409473 38126171410966166890057105)
  ·
    refine ⟨28594628558224625167542829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38126171410966166890057105 28594628558224625167542829)
    ·
      refine ⟨10722985709334234437828561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28594628558224625167542829 10722985709334234437828561)
      ·
        refine ⟨8042239282000675828371421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10722985709334234437828561 8042239282000675828371421)
        ·
          refine ⟨3015839730750253435639283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8042239282000675828371421 3015839730750253435639283)
          ·
            refine ⟨4523759596125380153458925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015839730750253435639283 4523759596125380153458925)
            ·
              refine ⟨1696409848547017557547097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4523759596125380153458925 1696409848547017557547097)
              ·
                refine ⟨1272307386410263168160323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1696409848547017557547097 1272307386410263168160323)
                ·
                  refine ⟨1908461079615394752240485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272307386410263168160323 1908461079615394752240485)
                  ·
                    refine ⟨357836452427886516045091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1908461079615394752240485 357836452427886516045091)
                    ·
                      rfl

theorem cell23_2090652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_2090652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090652 prefixEnd_2090652 := by exact prefixLift 2090652
  have htrace : WordTrace (prefixWord ++ tailWord_2090652) baseStart_2090652 baseEnd_2090652 := by
    simpa [prefixWord, tailWord_2090652, baseEnd_2090652] using wordTrace_append hprefix tailTrace_2090652
  have hstable : (prefixWord ++ tailWord_2090652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090652).length < 2 ^ (prefixWord ++ tailWord_2090652).sum := by decide
  have hdescent : baseEnd_2090652 < baseStart_2090652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090681 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 2, 6, 2]
def baseStart_2090681 : Nat := 118140960795 + 2090681 * 2 ^ 59
def prefixEnd_2090681 : Nat := 4983230072969 + 3 ^ 40 * 2090681 * 2
def baseEnd_2090681 : Nat := 1073524248222639934672639

theorem tailTrace_2090681 : CollatzResearch.WordTrace tailWord_2090681 prefixEnd_2090681 1073524248222639934672639 := by
  unfold tailWord_2090681
  simp only [CollatzResearch.WordTrace]
  refine ⟨76253400538827271732919897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50835600359218181155279931 76253400538827271732919897)
  ·
    refine ⟨57190050404120453799689923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76253400538827271732919897 57190050404120453799689923)
    ·
      refine ⟨85785075606180680699534885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57190050404120453799689923 85785075606180680699534885)
      ·
        refine ⟨16084701676158877631162791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85785075606180680699534885 16084701676158877631162791)
        ·
          refine ⟨24127052514238316446744187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16084701676158877631162791 24127052514238316446744187)
          ·
            refine ⟨36190578771357474670116281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24127052514238316446744187 36190578771357474670116281)
            ·
              refine ⟨27142934078518106002587211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36190578771357474670116281 27142934078518106002587211)
              ·
                refine ⟨40714401117777159003880817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27142934078518106002587211 40714401117777159003880817)
                ·
                  refine ⟨30535800838332869252910613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40714401117777159003880817 30535800838332869252910613)
                  ·
                    refine ⟨1431365664296853246230185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30535800838332869252910613 1431365664296853246230185)
                    ·
                      refine ⟨1073524248222639934672639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1431365664296853246230185 1073524248222639934672639)
                      ·
                        rfl

theorem cell23_2090681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_2090681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090681 prefixEnd_2090681 := by exact prefixLift 2090681
  have htrace : WordTrace (prefixWord ++ tailWord_2090681) baseStart_2090681 baseEnd_2090681 := by
    simpa [prefixWord, tailWord_2090681, baseEnd_2090681] using wordTrace_append hprefix tailTrace_2090681
  have hstable : (prefixWord ++ tailWord_2090681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090681).length < 2 ^ (prefixWord ++ tailWord_2090681).sum := by decide
  have hdescent : baseEnd_2090681 < baseStart_2090681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090728 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_2090728 : Nat := 118140960795 + 2090728 * 2 ^ 59
def prefixEnd_2090728 : Nat := 4983230072969 + 3 ^ 40 * 2090728 * 2
def baseEnd_2090728 : Nat := 1073548381813401250784923

theorem tailTrace_2090728 : CollatzResearch.WordTrace tailWord_2090728 prefixEnd_2090728 1073548381813401250784923 := by
  unfold tailWord_2090728
  simp only [CollatzResearch.WordTrace]
  refine ⟨38127557384828499379940419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50836743179771332506587225 38127557384828499379940419)
  ·
    refine ⟨57191336077242749069910629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38127557384828499379940419 57191336077242749069910629)
    ·
      refine ⟨10723375514483015450608243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57191336077242749069910629 10723375514483015450608243)
      ·
        refine ⟨16085063271724523175912365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10723375514483015450608243 16085063271724523175912365)
        ·
          refine ⟨6031898726896696190967137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16085063271724523175912365 6031898726896696190967137)
          ·
            refine ⟨4523924045172522143225353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6031898726896696190967137 4523924045172522143225353)
            ·
              refine ⟨3392943033879391607419015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4523924045172522143225353 3392943033879391607419015)
              ·
                refine ⟨5089414550819087411128523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3392943033879391607419015 5089414550819087411128523)
                ·
                  refine ⟨7634121826228631116692785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5089414550819087411128523 7634121826228631116692785)
                  ·
                    refine ⟨5725591369671473337519589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7634121826228631116692785 5725591369671473337519589)
                    ·
                      refine ⟨1073548381813401250784923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5725591369671473337519589 1073548381813401250784923)
                      ·
                        rfl

theorem cell23_2090728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_2090728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090728 prefixEnd_2090728 := by exact prefixLift 2090728
  have htrace : WordTrace (prefixWord ++ tailWord_2090728) baseStart_2090728 baseEnd_2090728 := by
    simpa [prefixWord, tailWord_2090728, baseEnd_2090728] using wordTrace_append hprefix tailTrace_2090728
  have hstable : (prefixWord ++ tailWord_2090728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090728).length < 2 ^ (prefixWord ++ tailWord_2090728).sum := by decide
  have hdescent : baseEnd_2090728 < baseStart_2090728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090731 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 3]
def baseStart_2090731 : Nat := 118140960795 + 2090731 * 2 ^ 59
def prefixEnd_2090731 : Nat := 4983230072969 + 3 ^ 40 * 2090731 * 2
def baseEnd_2090731 : Nat := 1073549922255364739047409

theorem tailTrace_2090731 : CollatzResearch.WordTrace tailWord_2090731 prefixEnd_2090731 1073549922255364739047409 := by
  unfold tailWord_2090731
  simp only [CollatzResearch.WordTrace]
  refine ⟨76255224188646130272240047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50836816125764086848160031 76255224188646130272240047)
  ·
    refine ⟨114382836282969195408360071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76255224188646130272240047 114382836282969195408360071)
    ·
      refine ⟨171574254424453793112540107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114382836282969195408360071 171574254424453793112540107)
      ·
        refine ⟨257361381636680689668810161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171574254424453793112540107 257361381636680689668810161)
        ·
          refine ⟨193021036227510517251607621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257361381636680689668810161 193021036227510517251607621)
          ·
            refine ⟨36191444292658221984676429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193021036227510517251607621 36191444292658221984676429)
            ·
              refine ⟨13571791609746833244253661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36191444292658221984676429 13571791609746833244253661)
              ·
                refine ⟨5089421853655062466595123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13571791609746833244253661 5089421853655062466595123)
                ·
                  refine ⟨7634132780482593699892685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5089421853655062466595123 7634132780482593699892685)
                  ·
                    refine ⟨2862799792680972637459757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7634132780482593699892685 2862799792680972637459757)
                    ·
                      refine ⟨1073549922255364739047409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2862799792680972637459757 1073549922255364739047409)
                      ·
                        rfl

theorem cell23_2090731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 3].length) (baseStart_2090731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090731 prefixEnd_2090731 := by exact prefixLift 2090731
  have htrace : WordTrace (prefixWord ++ tailWord_2090731) baseStart_2090731 baseEnd_2090731 := by
    simpa [prefixWord, tailWord_2090731, baseEnd_2090731] using wordTrace_append hprefix tailTrace_2090731
  have hstable : (prefixWord ++ tailWord_2090731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090731).length < 2 ^ (prefixWord ++ tailWord_2090731).sum := by decide
  have hdescent : baseEnd_2090731 < baseStart_2090731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090748 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 4, 1, 3]
def baseStart_2090748 : Nat := 118140960795 + 2090748 * 2 ^ 59
def prefixEnd_2090748 : Nat := 4983230072969 + 3 ^ 40 * 2090748 * 2
def baseEnd_2090748 : Nat := 1073558651426491172534831

theorem tailTrace_2090748 : CollatzResearch.WordTrace tailWord_2090748 prefixEnd_2090748 1073558651426491172534831 := by
  unfold tailWord_2090748
  simp only [CollatzResearch.WordTrace]
  refine ⟨38127922114792271087804449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50837229486389694783739265 38127922114792271087804449)
  ·
    refine ⟨28595941586094203315853337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38127922114792271087804449 28595941586094203315853337)
    ·
      refine ⟨21446956189570652486890003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28595941586094203315853337 21446956189570652486890003)
      ·
        refine ⟨32170434284355978730335005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21446956189570652486890003 32170434284355978730335005)
        ·
          refine ⟨12063912856633492023875627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32170434284355978730335005 12063912856633492023875627)
          ·
            refine ⟨18095869284950238035813441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12063912856633492023875627 18095869284950238035813441)
            ·
              refine ⟨13571901963712678526860081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18095869284950238035813441 13571901963712678526860081)
              ·
                refine ⟨10178926472784508895145061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13571901963712678526860081 10178926472784508895145061)
                ·
                  refine ⟨1908548713647095417839699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10178926472784508895145061 1908548713647095417839699)
                  ·
                    refine ⟨2862823070470643126759549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1908548713647095417839699 2862823070470643126759549)
                    ·
                      refine ⟨1073558651426491172534831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2862823070470643126759549 1073558651426491172534831)
                      ·
                        rfl

theorem cell23_2090748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_2090748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090748 prefixEnd_2090748 := by exact prefixLift 2090748
  have htrace : WordTrace (prefixWord ++ tailWord_2090748) baseStart_2090748 baseEnd_2090748 := by
    simpa [prefixWord, tailWord_2090748, baseEnd_2090748] using wordTrace_append hprefix tailTrace_2090748
  have hstable : (prefixWord ++ tailWord_2090748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090748).length < 2 ^ (prefixWord ++ tailWord_2090748).sum := by decide
  have hdescent : baseEnd_2090748 < baseStart_2090748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090792 : List Nat := [2, 1, 5, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_2090792 : Nat := 118140960795 + 2090792 * 2 ^ 59
def prefixEnd_2090792 : Nat := 4983230072969 + 3 ^ 40 * 2090792 * 2
def baseEnd_2090792 : Nat := 1073581244575289000384629

theorem tailTrace_2090792 : CollatzResearch.WordTrace tailWord_2090792 prefixEnd_2090792 1073581244575289000384629 := by
  unfold tailWord_2090792
  simp only [CollatzResearch.WordTrace]
  refine ⟨38128724520712568845105315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50838299360950091793473753 38128724520712568845105315)
  ·
    refine ⟨57193086781068853267657973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38128724520712568845105315 57193086781068853267657973)
    ·
      refine ⟨5361851885725204993842935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57193086781068853267657973 5361851885725204993842935)
      ·
        refine ⟨8042777828587807490764403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361851885725204993842935 8042777828587807490764403)
        ·
          refine ⟨12064166742881711236146605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8042777828587807490764403 12064166742881711236146605)
          ·
            refine ⟨4524062528580641713554977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12064166742881711236146605 4524062528580641713554977)
            ·
              refine ⟨3393046896435481285166233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4524062528580641713554977 3393046896435481285166233)
              ·
                refine ⟨2544785172326610963874675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3393046896435481285166233 2544785172326610963874675)
                ·
                  refine ⟨3817177758489916445812013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544785172326610963874675 3817177758489916445812013)
                  ·
                    refine ⟨1431441659433718667179505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817177758489916445812013 1431441659433718667179505)
                    ·
                      refine ⟨1073581244575289000384629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1431441659433718667179505 1073581244575289000384629)
                      ·
                        rfl

theorem cell23_2090792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_2090792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090792 prefixEnd_2090792 := by exact prefixLift 2090792
  have htrace : WordTrace (prefixWord ++ tailWord_2090792) baseStart_2090792 baseEnd_2090792 := by
    simpa [prefixWord, tailWord_2090792, baseEnd_2090792] using wordTrace_append hprefix tailTrace_2090792
  have hstable : (prefixWord ++ tailWord_2090792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090792).length < 2 ^ (prefixWord ++ tailWord_2090792).sum := by decide
  have hdescent : baseEnd_2090792 < baseStart_2090792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090841 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 4, 5]
def baseStart_2090841 : Nat := 118140960795 + 2090841 * 2 ^ 59
def prefixEnd_2090841 : Nat := 4983230072969 + 3 ^ 40 * 2090841 * 2
def baseEnd_2090841 : Nat := 357868801709119769557301

theorem tailTrace_2090841 : CollatzResearch.WordTrace tailWord_2090841 prefixEnd_2090841 357868801709119769557301 := by
  unfold tailWord_2090841
  simp only [CollatzResearch.WordTrace]
  refine ⟨76259236218247619058744377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50839490812165079372496251 76259236218247619058744377)
  ·
    refine ⟨57194427163685714294058283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76259236218247619058744377 57194427163685714294058283)
    ·
      refine ⟨85791640745528571441087425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57194427163685714294058283 85791640745528571441087425)
      ·
        refine ⟨64343730559146428580815569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85791640745528571441087425 64343730559146428580815569)
        ·
          refine ⟨48257797919359821435611677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64343730559146428580815569 48257797919359821435611677)
          ·
            refine ⟨18096674219759933038354379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48257797919359821435611677 18096674219759933038354379)
            ·
              refine ⟨27145011329639899557531569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18096674219759933038354379 27145011329639899557531569)
              ·
                refine ⟨20358758497229924668148677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27145011329639899557531569 20358758497229924668148677)
                ·
                  refine ⟨3817267218230610875277877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20358758497229924668148677 3817267218230610875277877)
                  ·
                    refine ⟨357868801709119769557301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3817267218230610875277877 357868801709119769557301)
                    ·
                      rfl

theorem cell23_2090841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 5].length) (baseStart_2090841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090841 prefixEnd_2090841 := by exact prefixLift 2090841
  have htrace : WordTrace (prefixWord ++ tailWord_2090841) baseStart_2090841 baseEnd_2090841 := by
    simpa [prefixWord, tailWord_2090841, baseEnd_2090841] using wordTrace_append hprefix tailTrace_2090841
  have hstable : (prefixWord ++ tailWord_2090841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090841).length < 2 ^ (prefixWord ++ tailWord_2090841).sum := by decide
  have hdescent : baseEnd_2090841 < baseStart_2090841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090891 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 4]
def baseStart_2090891 : Nat := 118140960795 + 2090891 * 2 ^ 59
def prefixEnd_2090891 : Nat := 4983230072969 + 3 ^ 40 * 2090891 * 2
def baseEnd_2090891 : Nat := 1073632079160084113046673

theorem tailTrace_2090891 : CollatzResearch.WordTrace tailWord_2090891 prefixEnd_2090891 1073632079160084113046673 := by
  unfold tailWord_2090891
  simp only [CollatzResearch.WordTrace]
  refine ⟨76261059868066477598064527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50840706578710985065376351 76261059868066477598064527)
  ·
    refine ⟨114391589802099716397096791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76261059868066477598064527 114391589802099716397096791)
    ·
      refine ⟨171587384703149574595645187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114391589802099716397096791 171587384703149574595645187)
      ·
        refine ⟨257381077054724361893467781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171587384703149574595645187 257381077054724361893467781)
        ·
          refine ⟨48258951947760817855025209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257381077054724361893467781 48258951947760817855025209)
          ·
            refine ⟨36194213960820613391268907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48258951947760817855025209 36194213960820613391268907)
            ·
              refine ⟨54291320941230920086903361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36194213960820613391268907 54291320941230920086903361)
              ·
                refine ⟨40718490705923190065177521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54291320941230920086903361 40718490705923190065177521)
                ·
                  refine ⟨30538868029442392548883141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40718490705923190065177521 30538868029442392548883141)
                  ·
                    refine ⟨5726037755520448602915589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30538868029442392548883141 5726037755520448602915589)
                    ·
                      refine ⟨1073632079160084113046673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5726037755520448602915589 1073632079160084113046673)
                      ·
                        rfl

theorem cell23_2090891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 4].length) (baseStart_2090891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090891 prefixEnd_2090891 := by exact prefixLift 2090891
  have htrace : WordTrace (prefixWord ++ tailWord_2090891) baseStart_2090891 baseEnd_2090891 := by
    simpa [prefixWord, tailWord_2090891, baseEnd_2090891] using wordTrace_append hprefix tailTrace_2090891
  have hstable : (prefixWord ++ tailWord_2090891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090891).length < 2 ^ (prefixWord ++ tailWord_2090891).sum := by decide
  have hdescent : baseEnd_2090891 < baseStart_2090891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090965 : List Nat := [1, 3, 2, 3, 2, 1, 1, 4, 1, 5]
def baseStart_2090965 : Nat := 118140960795 + 2090965 * 2 ^ 59
def prefixEnd_2090965 : Nat := 4983230072969 + 3 ^ 40 * 2090965 * 2
def baseEnd_2090965 : Nat := 357890025576172274507111

theorem tailTrace_2090965 : CollatzResearch.WordTrace tailWord_2090965 prefixEnd_2090965 357890025576172274507111 := by
  unfold tailWord_2090965
  simp only [CollatzResearch.WordTrace]
  refine ⟨76263758869798388236258349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50842505913198925490838899 76263758869798388236258349)
  ·
    refine ⟨28598909576174395588596881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76263758869798388236258349 28598909576174395588596881)
    ·
      refine ⟨21449182182130796691447661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28598909576174395588596881 21449182182130796691447661)
      ·
        refine ⟨8043443318299048759292873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21449182182130796691447661 8043443318299048759292873)
        ·
          refine ⟨6032582488724286569469655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8043443318299048759292873 6032582488724286569469655)
          ·
            refine ⟨9048873733086429854204483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6032582488724286569469655 9048873733086429854204483)
            ·
              refine ⟨13573310599629644781306725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9048873733086429854204483 13573310599629644781306725)
              ·
                refine ⟨2544995737430558396495011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13573310599629644781306725 2544995737430558396495011)
                ·
                  refine ⟨3817493606145837594742517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544995737430558396495011 3817493606145837594742517)
                  ·
                    refine ⟨357890025576172274507111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3817493606145837594742517 357890025576172274507111)
                    ·
                      rfl

theorem cell23_2090965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_2090965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090965 prefixEnd_2090965 := by exact prefixLift 2090965
  have htrace : WordTrace (prefixWord ++ tailWord_2090965) baseStart_2090965 baseEnd_2090965 := by
    simpa [prefixWord, tailWord_2090965, baseEnd_2090965] using wordTrace_append hprefix tailTrace_2090965
  have hstable : (prefixWord ++ tailWord_2090965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090965).length < 2 ^ (prefixWord ++ tailWord_2090965).sum := by decide
  have hdescent : baseEnd_2090965 < baseStart_2090965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090979 : List Nat := [1, 1, 1, 6, 1, 2, 3, 3, 1, 1, 3]
def baseStart_2090979 : Nat := 118140960795 + 2090979 * 2 ^ 59
def prefixEnd_2090979 : Nat := 4983230072969 + 3 ^ 40 * 2090979 * 2
def baseEnd_2090979 : Nat := 1073677265457679768746269

theorem tailTrace_2090979 : CollatzResearch.WordTrace tailWord_2090979 prefixEnd_2090979 1073677265457679768746269 := by
  unfold tailWord_2090979
  simp only [CollatzResearch.WordTrace]
  refine ⟨76264269491747668627267991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50842846327831779084845327 76264269491747668627267991)
  ·
    refine ⟨114396404237621502940901987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76264269491747668627267991 114396404237621502940901987)
    ·
      refine ⟨171594606356432254411352981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114396404237621502940901987 171594606356432254411352981)
      ·
        refine ⟨8043497172957761925532171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171594606356432254411352981 8043497172957761925532171)
        ·
          refine ⟨12065245759436642888298257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8043497172957761925532171 12065245759436642888298257)
          ·
            refine ⟨9048934319577482166223693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12065245759436642888298257 9048934319577482166223693)
            ·
              refine ⟨3393350369841555812333885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9048934319577482166223693 3393350369841555812333885)
              ·
                refine ⟨1272506388690583429625207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3393350369841555812333885 1272506388690583429625207)
                ·
                  refine ⟨1908759583035875144437811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272506388690583429625207 1908759583035875144437811)
                  ·
                    refine ⟨2863139374553812716656717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1908759583035875144437811 2863139374553812716656717)
                    ·
                      refine ⟨1073677265457679768746269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2863139374553812716656717 1073677265457679768746269)
                      ·
                        rfl

theorem cell23_2090979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_2090979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2090979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2090979 prefixEnd_2090979 := by exact prefixLift 2090979
  have htrace : WordTrace (prefixWord ++ tailWord_2090979) baseStart_2090979 baseEnd_2090979 := by
    simpa [prefixWord, tailWord_2090979, baseEnd_2090979] using wordTrace_append hprefix tailTrace_2090979
  have hstable : (prefixWord ++ tailWord_2090979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090979).length < 2 ^ (prefixWord ++ tailWord_2090979).sum := by decide
  have hdescent : baseEnd_2090979 < baseStart_2090979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091035 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 4, 1, 3]
def baseStart_2091035 : Nat := 118140960795 + 2091035 * 2 ^ 59
def prefixEnd_2091035 : Nat := 4983230072969 + 3 ^ 40 * 2091035 * 2
def baseEnd_2091035 : Nat := 1073706020374331549646011

theorem tailTrace_2091035 : CollatzResearch.WordTrace tailWord_2091035 prefixEnd_2091035 1073706020374331549646011 := by
  unfold tailWord_2091035
  simp only [CollatzResearch.WordTrace]
  refine ⟨76266311979544790191306559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50844207986363193460871039 76266311979544790191306559)
  ·
    refine ⟨114399467969317185286959839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76266311979544790191306559 114399467969317185286959839)
    ·
      refine ⟨171599201953975777930439759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114399467969317185286959839 171599201953975777930439759)
      ·
        refine ⟨257398802930963666895659639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171599201953975777930439759 257398802930963666895659639)
        ·
          refine ⟨386098204396445500343489459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257398802930963666895659639 386098204396445500343489459)
          ·
            refine ⟨579147306594668250515234189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386098204396445500343489459 579147306594668250515234189)
            ·
              refine ⟨217180239973000593943212821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 579147306594668250515234189 217180239973000593943212821)
              ·
                refine ⟨10180323748734402841088101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 217180239973000593943212821 10180323748734402841088101)
                ·
                  refine ⟨1908810702887700532704019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10180323748734402841088101 1908810702887700532704019)
                  ·
                    refine ⟨2863216054331550799056029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1908810702887700532704019 2863216054331550799056029)
                    ·
                      refine ⟨1073706020374331549646011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2863216054331550799056029 1073706020374331549646011)
                      ·
                        rfl

theorem cell23_2091035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 1, 3].length) (baseStart_2091035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091035 prefixEnd_2091035 := by exact prefixLift 2091035
  have htrace : WordTrace (prefixWord ++ tailWord_2091035) baseStart_2091035 baseEnd_2091035 := by
    simpa [prefixWord, tailWord_2091035, baseEnd_2091035] using wordTrace_append hprefix tailTrace_2091035
  have hstable : (prefixWord ++ tailWord_2091035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091035).length < 2 ^ (prefixWord ++ tailWord_2091035).sum := by decide
  have hdescent : baseEnd_2091035 < baseStart_2091035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091085 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_2091085 : Nat := 118140960795 + 2091085 * 2 ^ 59
def prefixEnd_2091085 : Nat := 4983230072969 + 3 ^ 40 * 2091085 * 2
def baseEnd_2091085 : Nat := 357910564802352118006927

theorem tailTrace_2091085 : CollatzResearch.WordTrace tailWord_2091085 prefixEnd_2091085 357910564802352118006927 := by
  unfold tailWord_2091085
  simp only [CollatzResearch.WordTrace]
  refine ⟨76268135629363648730626709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50845423752909099153751139 76268135629363648730626709)
  ·
    refine ⟨3575068857626421034248127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76268135629363648730626709 3575068857626421034248127)
    ·
      refine ⟨5362603286439631551372191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3575068857626421034248127 5362603286439631551372191)
      ·
        refine ⟨8043904929659447327058287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5362603286439631551372191 8043904929659447327058287)
        ·
          refine ⟨12065857394489170990587431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8043904929659447327058287 12065857394489170990587431)
          ·
            refine ⟨18098786091733756485881147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12065857394489170990587431 18098786091733756485881147)
            ·
              refine ⟨27148179137600634728821721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18098786091733756485881147 27148179137600634728821721)
              ·
                refine ⟨20361134353200476046616291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27148179137600634728821721 20361134353200476046616291)
                ·
                  refine ⟨30541701529800714069924437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20361134353200476046616291 30541701529800714069924437)
                  ·
                    refine ⟨357910564802352118006927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30541701529800714069924437 357910564802352118006927)
                    ·
                      rfl

theorem cell23_2091085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_2091085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091085 prefixEnd_2091085 := by exact prefixLift 2091085
  have htrace : WordTrace (prefixWord ++ tailWord_2091085) baseStart_2091085 baseEnd_2091085 := by
    simpa [prefixWord, tailWord_2091085, baseEnd_2091085] using wordTrace_append hprefix tailTrace_2091085
  have hstable : (prefixWord ++ tailWord_2091085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091085).length < 2 ^ (prefixWord ++ tailWord_2091085).sum := by decide
  have hdescent : baseEnd_2091085 < baseStart_2091085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091096 : List Nat := [2, 1, 2, 2, 1, 6, 2, 1, 1, 3, 2]
def baseStart_2091096 : Nat := 118140960795 + 2091096 * 2 ^ 59
def prefixEnd_2091096 : Nat := 4983230072969 + 3 ^ 40 * 2091096 * 2
def baseEnd_2091096 : Nat := 1073737342694255810983231

theorem tailTrace_2091096 : CollatzResearch.WordTrace tailWord_2091096 prefixEnd_2091096 1073737342694255810983231 := by
  unfold tailWord_2091096
  simp only [CollatzResearch.WordTrace]
  refine ⟨38134268416161898804638571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50845691221549198406184761 38134268416161898804638571)
  ·
    refine ⟨57201402624242848206957857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38134268416161898804638571 57201402624242848206957857)
    ·
      refine ⟨42901051968182136155218393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57201402624242848206957857 42901051968182136155218393)
      ·
        refine ⟨32175788976136602116413795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42901051968182136155218393 32175788976136602116413795)
        ·
          refine ⟨48263683464204903174620693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32175788976136602116413795 48263683464204903174620693)
          ·
            refine ⟨2262360162384604836310345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48263683464204903174620693 2262360162384604836310345)
            ·
              refine ⟨1696770121788453627232759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2262360162384604836310345 1696770121788453627232759)
              ·
                refine ⟨2545155182682680440849139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1696770121788453627232759 2545155182682680440849139)
                ·
                  refine ⟨3817732774024020661273709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545155182682680440849139 3817732774024020661273709)
                  ·
                    refine ⟨1431649790259007747977641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817732774024020661273709 1431649790259007747977641)
                    ·
                      refine ⟨1073737342694255810983231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1431649790259007747977641 1073737342694255810983231)
                      ·
                        rfl

theorem cell23_2091096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_2091096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091096 prefixEnd_2091096 := by exact prefixLift 2091096
  have htrace : WordTrace (prefixWord ++ tailWord_2091096) baseStart_2091096 baseEnd_2091096 := by
    simpa [prefixWord, tailWord_2091096, baseEnd_2091096] using wordTrace_append hprefix tailTrace_2091096
  have hstable : (prefixWord ++ tailWord_2091096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091096).length < 2 ^ (prefixWord ++ tailWord_2091096).sum := by decide
  have hdescent : baseEnd_2091096 < baseStart_2091096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091098 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 9]
def baseStart_2091098 : Nat := 118140960795 + 2091098 * 2 ^ 59
def prefixEnd_2091098 : Nat := 4983230072969 + 3 ^ 40 * 2091098 * 2
def baseEnd_2091098 : Nat := 119304263295062755906469

theorem tailTrace_2091098 : CollatzResearch.WordTrace tailWord_2091098 prefixEnd_2091098 119304263295062755906469 := by
  unfold tailWord_2091098
  simp only [CollatzResearch.WordTrace]
  refine ⟨19067152444579137987712487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50845739852211034633899965 19067152444579137987712487)
  ·
    refine ⟨28600728666868706981568731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19067152444579137987712487 28600728666868706981568731)
    ·
      refine ⟨42901093000303060472353097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28600728666868706981568731 42901093000303060472353097)
      ·
        refine ⟨32175819750227295354264823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42901093000303060472353097 32175819750227295354264823)
        ·
          refine ⟨48263729625340943031397235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32175819750227295354264823 48263729625340943031397235)
          ·
            refine ⟨72395594438011414547095853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48263729625340943031397235 72395594438011414547095853)
            ·
              refine ⟨27148347914254280455160945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72395594438011414547095853 27148347914254280455160945)
              ·
                refine ⟨20361260935690710341370709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27148347914254280455160945 20361260935690710341370709)
                ·
                  refine ⟨119304263295062755906469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20361260935690710341370709 119304263295062755906469)
                  ·
                    rfl

theorem cell23_2091098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_2091098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091098 prefixEnd_2091098 := by exact prefixLift 2091098
  have htrace : WordTrace (prefixWord ++ tailWord_2091098) baseStart_2091098 baseEnd_2091098 := by
    simpa [prefixWord, tailWord_2091098, baseEnd_2091098] using wordTrace_append hprefix tailTrace_2091098
  have hstable : (prefixWord ++ tailWord_2091098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091098).length < 2 ^ (prefixWord ++ tailWord_2091098).sum := by decide
  have hdescent : baseEnd_2091098 < baseStart_2091098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091109 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 4, 2, 2]
def baseStart_2091109 : Nat := 118140960795 + 2091109 * 2 ^ 59
def prefixEnd_2091109 : Nat := 4983230072969 + 3 ^ 40 * 2091109 * 2
def baseEnd_2091109 : Nat := 1073744017942764260120671

theorem tailTrace_2091109 : CollatzResearch.WordTrace tailWord_2091109 prefixEnd_2091109 1073744017942764260120671 := by
  unfold tailWord_2091109
  simp only [CollatzResearch.WordTrace]
  refine ⟨76269010981276700829500381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50846007320851133886333587 76269010981276700829500381)
  ·
    refine ⟨28600879117978762811062643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76269010981276700829500381 28600879117978762811062643)
    ·
      refine ⟨42901318676968144216593965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28600879117978762811062643 42901318676968144216593965)
      ·
        refine ⟨16087994503863054081222737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42901318676968144216593965 16087994503863054081222737)
        ·
          refine ⟨12065995877897290560917053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16087994503863054081222737 12065995877897290560917053)
          ·
            refine ⟨4524748454211483960343895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12065995877897290560917053 4524748454211483960343895)
            ·
              refine ⟨6787122681317225940515843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524748454211483960343895 6787122681317225940515843)
              ·
                refine ⟨10180684021975838910773765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6787122681317225940515843 10180684021975838910773765)
                ·
                  refine ⟨1908878254120469795770081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10180684021975838910773765 1908878254120469795770081)
                  ·
                    refine ⟨1431658690590352346827561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1908878254120469795770081 1431658690590352346827561)
                    ·
                      refine ⟨1073744017942764260120671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1431658690590352346827561 1073744017942764260120671)
                      ·
                        rfl

theorem cell23_2091109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_2091109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091109 prefixEnd_2091109 := by exact prefixLift 2091109
  have htrace : WordTrace (prefixWord ++ tailWord_2091109) baseStart_2091109 baseEnd_2091109 := by
    simpa [prefixWord, tailWord_2091109, baseEnd_2091109] using wordTrace_append hprefix tailTrace_2091109
  have hstable : (prefixWord ++ tailWord_2091109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091109).length < 2 ^ (prefixWord ++ tailWord_2091109).sum := by decide
  have hdescent : baseEnd_2091109 < baseStart_2091109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091126 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_2091126 : Nat := 118140960795 + 2091126 * 2 ^ 59
def prefixEnd_2091126 : Nat := 4983230072969 + 3 ^ 40 * 2091126 * 2
def baseEnd_2091126 : Nat := 1073752747113890693608093

theorem tailTrace_2091126 : CollatzResearch.WordTrace tailWord_2091126 prefixEnd_2091126 1073752747113890693608093 := by
  unfold tailWord_2091126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4766851938888444545804327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50846420681476741821912821 4766851938888444545804327)
  ·
    refine ⟨7150277908332666818706491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4766851938888444545804327 7150277908332666818706491)
    ·
      refine ⟨10725416862499000228059737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7150277908332666818706491 10725416862499000228059737)
      ·
        refine ⟨8044062646874250171044803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10725416862499000228059737 8044062646874250171044803)
        ·
          refine ⟨12066093970311375256567205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8044062646874250171044803 12066093970311375256567205)
          ·
            refine ⟨2262392619433382860606351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12066093970311375256567205 2262392619433382860606351)
            ·
              refine ⟨3393588929150074290909527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262392619433382860606351 3393588929150074290909527)
              ·
                refine ⟨5090383393725111436364291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3393588929150074290909527 5090383393725111436364291)
                ·
                  refine ⟨7635575090587667154546437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5090383393725111436364291 7635575090587667154546437)
                  ·
                    refine ⟨1431670329485187591477457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7635575090587667154546437 1431670329485187591477457)
                    ·
                      refine ⟨1073752747113890693608093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1431670329485187591477457 1073752747113890693608093)
                      ·
                        rfl

theorem cell23_2091126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_2091126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091126 prefixEnd_2091126 := by exact prefixLift 2091126
  have htrace : WordTrace (prefixWord ++ tailWord_2091126) baseStart_2091126 baseEnd_2091126 := by
    simpa [prefixWord, tailWord_2091126, baseEnd_2091126] using wordTrace_append hprefix tailTrace_2091126
  have hstable : (prefixWord ++ tailWord_2091126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091126).length < 2 ^ (prefixWord ++ tailWord_2091126).sum := by decide
  have hdescent : baseEnd_2091126 < baseStart_2091126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091145 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 2, 5]
def baseStart_2091145 : Nat := 118140960795 + 2091145 * 2 ^ 59
def prefixEnd_2091145 : Nat := 4983230072969 + 3 ^ 40 * 2091145 * 2
def baseEnd_2091145 : Nat := 357920834415442039756835

theorem tailTrace_2091145 : CollatzResearch.WordTrace tailWord_2091145 prefixEnd_2091145 357920834415442039756835 := by
  unfold tailWord_2091145
  simp only [CollatzResearch.WordTrace]
  refine ⟨76270324009146278977810889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50846882672764185985207259 76270324009146278977810889)
  ·
    refine ⟨57202743006859709233358167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76270324009146278977810889 57202743006859709233358167)
    ·
      refine ⟨85804114510289563850037251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57202743006859709233358167 85804114510289563850037251)
      ·
        refine ⟨128706171765434345775055877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85804114510289563850037251 128706171765434345775055877)
        ·
          refine ⟨24132407206018939832822977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128706171765434345775055877 24132407206018939832822977)
          ·
            refine ⟨18099305404514204874617233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24132407206018939832822977 18099305404514204874617233)
            ·
              refine ⟨13574479053385653655962925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18099305404514204874617233 13574479053385653655962925)
              ·
                refine ⟨5090429645019620120986097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13574479053385653655962925 5090429645019620120986097)
                ·
                  refine ⟨3817822233764715090739573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5090429645019620120986097 3817822233764715090739573)
                  ·
                    refine ⟨357920834415442039756835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3817822233764715090739573 357920834415442039756835)
                    ·
                      rfl

theorem cell23_2091145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 5].length) (baseStart_2091145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091145 prefixEnd_2091145 := by exact prefixLift 2091145
  have htrace : WordTrace (prefixWord ++ tailWord_2091145) baseStart_2091145 baseEnd_2091145 := by
    simpa [prefixWord, tailWord_2091145, baseEnd_2091145] using wordTrace_append hprefix tailTrace_2091145
  have hstable : (prefixWord ++ tailWord_2091145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091145).length < 2 ^ (prefixWord ++ tailWord_2091145).sum := by decide
  have hdescent : baseEnd_2091145 < baseStart_2091145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091166 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 7]
def baseStart_2091166 : Nat := 118140960795 + 2091166 * 2 ^ 59
def prefixEnd_2091166 : Nat := 4983230072969 + 3 ^ 40 * 2091166 * 2
def baseEnd_2091166 : Nat := 119308142926674504123101

theorem tailTrace_2091166 : CollatzResearch.WordTrace tailWord_2091166 prefixEnd_2091166 119308142926674504123101 := by
  unfold tailWord_2091166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9533886242758774945540669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50847393294713466376216901 9533886242758774945540669)
  ·
    refine ⟨3575207341034540604577751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9533886242758774945540669 3575207341034540604577751)
    ·
      refine ⟨5362811011551810906866627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3575207341034540604577751 5362811011551810906866627)
      ·
        refine ⟨8044216517327716360299941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5362811011551810906866627 8044216517327716360299941)
        ·
          refine ⟨1508290596998946817556239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8044216517327716360299941 1508290596998946817556239)
          ·
            refine ⟨2262435895498420226334359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508290596998946817556239 2262435895498420226334359)
            ·
              refine ⟨3393653843247630339501539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262435895498420226334359 3393653843247630339501539)
              ·
                refine ⟨5090480764871445509252309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3393653843247630339501539 5090480764871445509252309)
                ·
                  refine ⟨119308142926674504123101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5090480764871445509252309 119308142926674504123101)
                  ·
                    rfl

theorem cell23_2091166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_2091166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091166 prefixEnd_2091166 := by exact prefixLift 2091166
  have htrace : WordTrace (prefixWord ++ tailWord_2091166) baseStart_2091166 baseEnd_2091166 := by
    simpa [prefixWord, tailWord_2091166, baseEnd_2091166] using wordTrace_append hprefix tailTrace_2091166
  have hstable : (prefixWord ++ tailWord_2091166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091166).length < 2 ^ (prefixWord ++ tailWord_2091166).sum := by decide
  have hdescent : baseEnd_2091166 < baseStart_2091166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091172 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_2091172 : Nat := 118140960795 + 2091172 * 2 ^ 59
def prefixEnd_2091172 : Nat := 4983230072969 + 3 ^ 40 * 2091172 * 2
def baseEnd_2091172 : Nat := 1073776367223997513632881

theorem tailTrace_2091172 : CollatzResearch.WordTrace tailWord_2091172 prefixEnd_2091172 1073776367223997513632881 := by
  unfold tailWord_2091172
  simp only [CollatzResearch.WordTrace]
  refine ⟨38135654390024231294521885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50847539186698975059362513 38135654390024231294521885)
  ·
    refine ⟨14300870396259086735445707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38135654390024231294521885 14300870396259086735445707)
    ·
      refine ⟨21451305594388630103168561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14300870396259086735445707 21451305594388630103168561)
      ·
        refine ⟨16088479195791472577376421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21451305594388630103168561 16088479195791472577376421)
        ·
          refine ⟨3016589849210901108258079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16088479195791472577376421 3016589849210901108258079)
          ·
            refine ⟨4524884773816351662387119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016589849210901108258079 4524884773816351662387119)
            ·
              refine ⟨6787327160724527493580679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524884773816351662387119 6787327160724527493580679)
              ·
                refine ⟨10180990741086791240371019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6787327160724527493580679 10180990741086791240371019)
                ·
                  refine ⟨15271486111630186860556529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10180990741086791240371019 15271486111630186860556529)
                  ·
                    refine ⟨11453614583722640145417397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15271486111630186860556529 11453614583722640145417397)
                    ·
                      refine ⟨1073776367223997513632881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11453614583722640145417397 1073776367223997513632881)
                      ·
                        rfl

theorem cell23_2091172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_2091172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091172 prefixEnd_2091172 := by exact prefixLift 2091172
  have htrace : WordTrace (prefixWord ++ tailWord_2091172) baseStart_2091172 baseEnd_2091172 := by
    simpa [prefixWord, tailWord_2091172, baseEnd_2091172] using wordTrace_append hprefix tailTrace_2091172
  have hstable : (prefixWord ++ tailWord_2091172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091172).length < 2 ^ (prefixWord ++ tailWord_2091172).sum := by decide
  have hdescent : baseEnd_2091172 < baseStart_2091172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091226 : List Nat := [3, 1, 1, 2, 2, 1, 6, 2, 1, 4]
def baseStart_2091226 : Nat := 118140960795 + 2091226 * 2 ^ 59
def prefixEnd_2091226 : Nat := 4983230072969 + 3 ^ 40 * 2091226 * 2
def baseEnd_2091226 : Nat := 357934698393113434119211

theorem tailTrace_2091226 : CollatzResearch.WordTrace tailWord_2091226 prefixEnd_2091226 357934698393113434119211 := by
  unfold tailWord_2091226
  simp only [CollatzResearch.WordTrace]
  refine ⟨19068319580463207452877383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50848852214568553207673021 19068319580463207452877383)
  ·
    refine ⟨28602479370694811179316075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19068319580463207452877383 28602479370694811179316075)
    ·
      refine ⟨42903719056042216768974113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28602479370694811179316075 42903719056042216768974113)
      ·
        refine ⟨32177789292031662576730585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42903719056042216768974113 32177789292031662576730585)
        ·
          refine ⟨24133341969023746932547939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32177789292031662576730585 24133341969023746932547939)
          ·
            refine ⟨36200012953535620398821909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24133341969023746932547939 36200012953535620398821909)
            ·
              refine ⟨1696875607196982206194777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36200012953535620398821909 1696875607196982206194777)
              ·
                refine ⟨1272656705397736654646083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1696875607196982206194777 1272656705397736654646083)
                ·
                  refine ⟨1908985058096604981969125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272656705397736654646083 1908985058096604981969125)
                  ·
                    refine ⟨357934698393113434119211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1908985058096604981969125 357934698393113434119211)
                    ·
                      rfl

theorem cell23_2091226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_2091226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091226 prefixEnd_2091226 := by exact prefixLift 2091226
  have htrace : WordTrace (prefixWord ++ tailWord_2091226) baseStart_2091226 baseEnd_2091226 := by
    simpa [prefixWord, tailWord_2091226, baseEnd_2091226] using wordTrace_append hprefix tailTrace_2091226
  have hstable : (prefixWord ++ tailWord_2091226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091226).length < 2 ^ (prefixWord ++ tailWord_2091226).sum := by decide
  have hdescent : baseEnd_2091226 < baseStart_2091226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091326 : List Nat := [4, 2, 1, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_2091326 : Nat := 118140960795 + 2091326 * 2 ^ 59
def prefixEnd_2091326 : Nat := 4983230072969 + 3 ^ 40 * 2091326 * 2
def baseEnd_2091326 : Nat := 1073855443244789911107173

theorem tailTrace_2091326 : CollatzResearch.WordTrace tailWord_2091326 prefixEnd_2091326 1073855443244789911107173 := by
  unfold tailWord_2091326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9534615702686318361268729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50851283747660364593433221 9534615702686318361268729)
  ·
    refine ⟨7150961777014738770951547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9534615702686318361268729 7150961777014738770951547)
    ·
      refine ⟨10726442665522108156427321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7150961777014738770951547 10726442665522108156427321)
      ·
        refine ⟨8044831999141581117320491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10726442665522108156427321 8044831999141581117320491)
        ·
          refine ⟨12067247998712371675980737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8044831999141581117320491 12067247998712371675980737)
          ·
            refine ⟨9050435999034278756985553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12067247998712371675980737 9050435999034278756985553)
            ·
              refine ⟨6787826999275709067739165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9050435999034278756985553 6787826999275709067739165)
              ·
                refine ⟨2545435124728390900402187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6787826999275709067739165 2545435124728390900402187)
                ·
                  refine ⟨3818152687092586350603281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545435124728390900402187 3818152687092586350603281)
                  ·
                    refine ⟨2863614515319439762952461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3818152687092586350603281 2863614515319439762952461)
                    ·
                      refine ⟨1073855443244789911107173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2863614515319439762952461 1073855443244789911107173)
                      ·
                        rfl

theorem cell23_2091326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_2091326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091326 prefixEnd_2091326 := by exact prefixLift 2091326
  have htrace : WordTrace (prefixWord ++ tailWord_2091326) baseStart_2091326 baseEnd_2091326 := by
    simpa [prefixWord, tailWord_2091326, baseEnd_2091326] using wordTrace_append hprefix tailTrace_2091326
  have hstable : (prefixWord ++ tailWord_2091326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091326).length < 2 ^ (prefixWord ++ tailWord_2091326).sum := by decide
  have hdescent : baseEnd_2091326 < baseStart_2091326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091329 : List Nat := [1, 2, 5, 2, 2, 2, 9]
def baseStart_2091329 : Nat := 118140960795 + 2091329 * 2 ^ 59
def prefixEnd_2091329 : Nat := 4983230072969 + 3 ^ 40 * 2091329 * 2
def baseEnd_2091329 : Nat := 13257493625762387646539

theorem tailTrace_2091329 : CollatzResearch.WordTrace tailWord_2091329 prefixEnd_2091329 13257493625762387646539 := by
  unfold tailWord_2091329
  simp only [CollatzResearch.WordTrace]
  refine ⟨76277035040479678402509041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50851356693653118935006027 76277035040479678402509041)
  ·
    refine ⟨57207776280359758801881781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76277035040479678402509041 57207776280359758801881781)
    ·
      refine ⟨5363229026283727387676417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57207776280359758801881781 5363229026283727387676417)
      ·
        refine ⟨4022421769712795540757313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5363229026283727387676417 4022421769712795540757313)
        ·
          refine ⟨3016816327284596655567985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4022421769712795540757313 3016816327284596655567985)
          ·
            refine ⟨2262612245463447491675989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3016816327284596655567985 2262612245463447491675989)
            ·
              refine ⟨13257493625762387646539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2262612245463447491675989 13257493625762387646539)
              ·
                rfl

theorem cell23_2091329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 9].length) (baseStart_2091329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091329 prefixEnd_2091329 := by exact prefixLift 2091329
  have htrace : WordTrace (prefixWord ++ tailWord_2091329) baseStart_2091329 baseEnd_2091329 := by
    simpa [prefixWord, tailWord_2091329, baseEnd_2091329] using wordTrace_append hprefix tailTrace_2091329
  have hstable : (prefixWord ++ tailWord_2091329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091329).length < 2 ^ (prefixWord ++ tailWord_2091329).sum := by decide
  have hdescent : baseEnd_2091329 < baseStart_2091329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091340 : List Nat := [2, 2, 1, 3, 2, 1, 5, 2, 1, 2, 2]
def baseStart_2091340 : Nat := 118140960795 + 2091340 * 2 ^ 59
def prefixEnd_2091340 : Nat := 4983230072969 + 3 ^ 40 * 2091340 * 2
def baseEnd_2091340 : Nat := 1073862631973952856332109

theorem tailTrace_2091340 : CollatzResearch.WordTrace tailWord_2091340 prefixEnd_2091340 1073862631973952856332109 := by
  unfold tailWord_2091340
  simp only [CollatzResearch.WordTrace]
  refine ⟨38138718121719913640579737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50851624162293218187439649 38138718121719913640579737)
  ·
    refine ⟨28604038591289935230434803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38138718121719913640579737 28604038591289935230434803)
    ·
      refine ⟨42906057886934902845652205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28604038591289935230434803 42906057886934902845652205)
      ·
        refine ⟨16089771707600588567119577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42906057886934902845652205 16089771707600588567119577)
        ·
          refine ⟨12067328780700441425339683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16089771707600588567119577 12067328780700441425339683)
          ·
            refine ⟨18100993171050662138009525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12067328780700441425339683 18100993171050662138009525)
            ·
              refine ⟨1696968109785999575438393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18100993171050662138009525 1696968109785999575438393)
              ·
                refine ⟨1272726082339499681578795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1696968109785999575438393 1272726082339499681578795)
                ·
                  refine ⟨1909089123509249522368193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272726082339499681578795 1909089123509249522368193)
                  ·
                    refine ⟨1431816842631937141776145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1909089123509249522368193 1431816842631937141776145)
                    ·
                      refine ⟨1073862631973952856332109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1431816842631937141776145 1073862631973952856332109)
                      ·
                        rfl

theorem cell23_2091340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_2091340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091340 prefixEnd_2091340 := by exact prefixLift 2091340
  have htrace : WordTrace (prefixWord ++ tailWord_2091340) baseStart_2091340 baseEnd_2091340 := by
    simpa [prefixWord, tailWord_2091340, baseEnd_2091340] using wordTrace_append hprefix tailTrace_2091340
  have hstable : (prefixWord ++ tailWord_2091340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091340).length < 2 ^ (prefixWord ++ tailWord_2091340).sum := by decide
  have hdescent : baseEnd_2091340 < baseStart_2091340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091379 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 1, 4, 2]
def baseStart_2091379 : Nat := 118140960795 + 2091379 * 2 ^ 59
def prefixEnd_2091379 : Nat := 4983230072969 + 3 ^ 40 * 2091379 * 2
def baseEnd_2091379 : Nat := 1073882657719478203744429

theorem tailTrace_2091379 : CollatzResearch.WordTrace tailWord_2091379 prefixEnd_2091379 1073882657719478203744429 := by
  unfold tailWord_2091379
  simp only [CollatzResearch.WordTrace]
  refine ⟨76278858690298536941829191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50852572460199024627886127 76278858690298536941829191)
  ·
    refine ⟨114418288035447805412743787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76278858690298536941829191 114418288035447805412743787)
    ·
      refine ⟨171627432053171708119115681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114418288035447805412743787 171627432053171708119115681)
      ·
        refine ⟨128720574039878781089336761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171627432053171708119115681 128720574039878781089336761)
        ·
          refine ⟨96540430529909085817002571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128720574039878781089336761 96540430529909085817002571)
          ·
            refine ⟨144810645794863628725503857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96540430529909085817002571 144810645794863628725503857)
            ·
              refine ⟨108607984346147721544127893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144810645794863628725503857 108607984346147721544127893)
              ·
                refine ⟨5090999266225674447380995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108607984346147721544127893 5090999266225674447380995)
                ·
                  refine ⟨7636498899338511671071493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5090999266225674447380995 7636498899338511671071493)
                  ·
                    refine ⟨1431843543625970938325905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7636498899338511671071493 1431843543625970938325905)
                    ·
                      refine ⟨1073882657719478203744429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1431843543625970938325905 1073882657719478203744429)
                      ·
                        rfl

theorem cell23_2091379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 4, 2].length) (baseStart_2091379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091379 prefixEnd_2091379 := by exact prefixLift 2091379
  have htrace : WordTrace (prefixWord ++ tailWord_2091379) baseStart_2091379 baseEnd_2091379 := by
    simpa [prefixWord, tailWord_2091379, baseEnd_2091379] using wordTrace_append hprefix tailTrace_2091379
  have hstable : (prefixWord ++ tailWord_2091379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091379).length < 2 ^ (prefixWord ++ tailWord_2091379).sum := by decide
  have hdescent : baseEnd_2091379 < baseStart_2091379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091489 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_2091489 : Nat := 118140960795 + 2091489 * 2 ^ 59
def prefixEnd_2091489 : Nat := 4983230072969 + 3 ^ 40 * 2091489 * 2
def baseEnd_2091489 : Nat := 1073939140591472773368923

theorem tailTrace_2091489 : CollatzResearch.WordTrace tailWord_2091489 prefixEnd_2091489 1073939140591472773368923 := by
  unfold tailWord_2091489
  simp only [CollatzResearch.WordTrace]
  refine ⟨76282870719900025728333521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50855247146600017152222347 76282870719900025728333521)
  ·
    refine ⟨57212153039925019296250141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76282870719900025728333521 57212153039925019296250141)
    ·
      refine ⟨21454557389971882236093803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57212153039925019296250141 21454557389971882236093803)
      ·
        refine ⟨32181836084957823354140705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21454557389971882236093803 32181836084957823354140705)
        ·
          refine ⟨24136377063718367515605529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32181836084957823354140705 24136377063718367515605529)
          ·
            refine ⟨18102282797788775636704147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24136377063718367515605529 18102282797788775636704147)
            ·
              refine ⟨27153424196683163455056221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18102282797788775636704147 27153424196683163455056221)
              ·
                refine ⟨10182534073756186295646083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27153424196683163455056221 10182534073756186295646083)
                ·
                  refine ⟨15273801110634279443469125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10182534073756186295646083 15273801110634279443469125)
                  ·
                    refine ⟨2863837708243927395650461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15273801110634279443469125 2863837708243927395650461)
                    ·
                      refine ⟨1073939140591472773368923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2863837708243927395650461 1073939140591472773368923)
                      ·
                        rfl

theorem cell23_2091489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_2091489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091489 prefixEnd_2091489 := by exact prefixLift 2091489
  have htrace : WordTrace (prefixWord ++ tailWord_2091489) baseStart_2091489 baseEnd_2091489 := by
    simpa [prefixWord, tailWord_2091489, baseEnd_2091489] using wordTrace_append hprefix tailTrace_2091489
  have hstable : (prefixWord ++ tailWord_2091489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091489).length < 2 ^ (prefixWord ++ tailWord_2091489).sum := by decide
  have hdescent : baseEnd_2091489 < baseStart_2091489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091539 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 3, 5]
def baseStart_2091539 : Nat := 118140960795 + 2091539 * 2 ^ 59
def prefixEnd_2091539 : Nat := 4983230072969 + 3 ^ 40 * 2091539 * 2
def baseEnd_2091539 : Nat := 357988271541399192581231

theorem tailTrace_2091539 : CollatzResearch.WordTrace tailWord_2091539 prefixEnd_2091539 357988271541399192581231 := by
  unfold tailWord_2091539
  simp only [CollatzResearch.WordTrace]
  refine ⟨76284694369718884267653671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50856462913145922845102447 76284694369718884267653671)
  ·
    refine ⟨114427041554578326401480507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76284694369718884267653671 114427041554578326401480507)
    ·
      refine ⟨171640562331867489602220761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114427041554578326401480507 171640562331867489602220761)
      ·
        refine ⟨128730421748900617201665571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171640562331867489602220761 128730421748900617201665571)
        ·
          refine ⟨193095632623350925802498357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128730421748900617201665571 193095632623350925802498357)
          ·
            refine ⟨18102715558439149293984221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193095632623350925802498357 18102715558439149293984221)
            ·
              refine ⟨6788518334414680985244083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18102715558439149293984221 6788518334414680985244083)
              ·
                refine ⟨10182777501622021477866125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6788518334414680985244083 10182777501622021477866125)
                ·
                  refine ⟨3818541563108258054199797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10182777501622021477866125 3818541563108258054199797)
                  ·
                    refine ⟨357988271541399192581231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3818541563108258054199797 357988271541399192581231)
                    ·
                      rfl

theorem cell23_2091539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 5].length) (baseStart_2091539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091539 prefixEnd_2091539 := by exact prefixLift 2091539
  have htrace : WordTrace (prefixWord ++ tailWord_2091539) baseStart_2091539 baseEnd_2091539 := by
    simpa [prefixWord, tailWord_2091539, baseEnd_2091539] using wordTrace_append hprefix tailTrace_2091539
  have hstable : (prefixWord ++ tailWord_2091539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091539).length < 2 ^ (prefixWord ++ tailWord_2091539).sum := by decide
  have hdescent : baseEnd_2091539 < baseStart_2091539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091540 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2091540 : Nat := 118140960795 + 2091540 * 2 ^ 59
def prefixEnd_2091540 : Nat := 4983230072969 + 3 ^ 40 * 2091540 * 2
def baseEnd_2091540 : Nat := 1073965328104852073831189

theorem tailTrace_2091540 : CollatzResearch.WordTrace tailWord_2091540 prefixEnd_2091540 1073965328104852073831189 := by
  unfold tailWord_2091540
  simp only [CollatzResearch.WordTrace]
  refine ⟨38142365421357630719220037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50856487228476840958960049 38142365421357630719220037)
  ·
    refine ⟨7151693516504555759853757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38142365421357630719220037 7151693516504555759853757)
    ·
      refine ⟨2681885068689208409945159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7151693516504555759853757 2681885068689208409945159)
      ·
        refine ⟨4022827603033812614917739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681885068689208409945159 4022827603033812614917739)
        ·
          refine ⟨6034241404550718922376609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022827603033812614917739 6034241404550718922376609)
          ·
            refine ⟨4525681053413039191782457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6034241404550718922376609 4525681053413039191782457)
            ·
              refine ⟨3394260790059779393836843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4525681053413039191782457 3394260790059779393836843)
              ·
                refine ⟨5091391185089669090755265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394260790059779393836843 5091391185089669090755265)
                ·
                  refine ⟨3818543388817251818066449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5091391185089669090755265 3818543388817251818066449)
                  ·
                    refine ⟨2863907541612938863549837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3818543388817251818066449 2863907541612938863549837)
                    ·
                      refine ⟨1073965328104852073831189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2863907541612938863549837 1073965328104852073831189)
                      ·
                        rfl

theorem cell23_2091540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2091540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091540 prefixEnd_2091540 := by exact prefixLift 2091540
  have htrace : WordTrace (prefixWord ++ tailWord_2091540) baseStart_2091540 baseEnd_2091540 := by
    simpa [prefixWord, tailWord_2091540, baseEnd_2091540] using wordTrace_append hprefix tailTrace_2091540
  have hstable : (prefixWord ++ tailWord_2091540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091540).length < 2 ^ (prefixWord ++ tailWord_2091540).sum := by decide
  have hdescent : baseEnd_2091540 < baseStart_2091540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091546 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2]
def baseStart_2091546 : Nat := 118140960795 + 2091546 * 2 ^ 59
def prefixEnd_2091546 : Nat := 4983230072969 + 3 ^ 40 * 2091546 * 2
def baseEnd_2091546 : Nat := 1073968408988779050356161

theorem tailTrace_2091546 : CollatzResearch.WordTrace tailWord_2091546 prefixEnd_2091546 1073968408988779050356161 := by
  unfold tailWord_2091546
  simp only [CollatzResearch.WordTrace]
  refine ⟨19071237420173381115789623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50856633120462349642105661 19071237420173381115789623)
  ·
    refine ⟨28606856130260071673684435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19071237420173381115789623 28606856130260071673684435)
    ·
      refine ⟨42910284195390107510526653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28606856130260071673684435 42910284195390107510526653)
      ·
        refine ⟨16091356573271290316447495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42910284195390107510526653 16091356573271290316447495)
        ·
          refine ⟨24137034859906935474671243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16091356573271290316447495 24137034859906935474671243)
          ·
            refine ⟨36205552289860403212006865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24137034859906935474671243 36205552289860403212006865)
            ·
              refine ⟨27154164217395302409005149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36205552289860403212006865 27154164217395302409005149)
              ·
                refine ⟨10182811581523238403376931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27154164217395302409005149 10182811581523238403376931)
                ·
                  refine ⟨15274217372284857605065397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10182811581523238403376931 15274217372284857605065397)
                  ·
                    refine ⟨1431957878651705400474881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15274217372284857605065397 1431957878651705400474881)
                    ·
                      refine ⟨1073968408988779050356161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1431957878651705400474881 1073968408988779050356161)
                      ·
                        rfl

theorem cell23_2091546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_2091546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091546 prefixEnd_2091546 := by exact prefixLift 2091546
  have htrace : WordTrace (prefixWord ++ tailWord_2091546) baseStart_2091546 baseEnd_2091546 := by
    simpa [prefixWord, tailWord_2091546, baseEnd_2091546] using wordTrace_append hprefix tailTrace_2091546
  have hstable : (prefixWord ++ tailWord_2091546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091546).length < 2 ^ (prefixWord ++ tailWord_2091546).sum := by decide
  have hdescent : baseEnd_2091546 < baseStart_2091546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091596 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 3, 2, 3]
def baseStart_2091596 : Nat := 118140960795 + 2091596 * 2 ^ 59
def prefixEnd_2091596 : Nat := 4983230072969 + 3 ^ 40 * 2091596 * 2
def baseEnd_2091596 : Nat := 1073994083021503854730931

theorem tailTrace_2091596 : CollatzResearch.WordTrace tailWord_2091596 prefixEnd_2091596 1073994083021503854730931 := by
  unfold tailWord_2091596
  simp only [CollatzResearch.WordTrace]
  refine ⟨38143386665256191501239321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50857848887008255334985761 38143386665256191501239321)
  ·
    refine ⟨28607539998942143625929491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38143386665256191501239321 28607539998942143625929491)
    ·
      refine ⟨42911309998413215438894237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28607539998942143625929491 42911309998413215438894237)
      ·
        refine ⟨16091741249404955789585339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42911309998413215438894237 16091741249404955789585339)
        ·
          refine ⟨24137611874107433684378009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16091741249404955789585339 24137611874107433684378009)
          ·
            refine ⟨18103208905580575263283507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24137611874107433684378009 18103208905580575263283507)
            ·
              refine ⟨27154813358370862894925261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18103208905580575263283507 27154813358370862894925261)
              ·
                refine ⟨10183055009389073585596973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27154813358370862894925261 10183055009389073585596973)
                ·
                  refine ⟨3818645628520902594598865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10183055009389073585596973 3818645628520902594598865)
                  ·
                    refine ⟨2863984221390676945949149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3818645628520902594598865 2863984221390676945949149)
                    ·
                      refine ⟨1073994083021503854730931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2863984221390676945949149 1073994083021503854730931)
                      ·
                        rfl

theorem cell23_2091596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_2091596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091596 prefixEnd_2091596 := by exact prefixLift 2091596
  have htrace : WordTrace (prefixWord ++ tailWord_2091596) baseStart_2091596 baseEnd_2091596 := by
    simpa [prefixWord, tailWord_2091596, baseEnd_2091596] using wordTrace_append hprefix tailTrace_2091596
  have hstable : (prefixWord ++ tailWord_2091596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091596).length < 2 ^ (prefixWord ++ tailWord_2091596).sum := by decide
  have hdescent : baseEnd_2091596 < baseStart_2091596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091597 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_2091597 : Nat := 118140960795 + 2091597 * 2 ^ 59
def prefixEnd_2091597 : Nat := 4983230072969 + 3 ^ 40 * 2091597 * 2
def baseEnd_2091597 : Nat := 1073994596502158350818427

theorem tailTrace_2091597 : CollatzResearch.WordTrace tailWord_2091597 prefixEnd_2091597 1073994596502158350818427 := by
  unfold tailWord_2091597
  simp only [CollatzResearch.WordTrace]
  refine ⟨76286809803508760173265045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50857873202339173448843363 76286809803508760173265045)
  ·
    refine ⟨3575944209539473133121799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76286809803508760173265045 3575944209539473133121799)
    ·
      refine ⟨5363916314309209699682699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3575944209539473133121799 5363916314309209699682699)
      ·
        refine ⟨8045874471463814549524049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5363916314309209699682699 8045874471463814549524049)
        ·
          refine ⟨6034405853597860912143037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8045874471463814549524049 6034405853597860912143037)
          ·
            refine ⟨2262902195099197842053639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6034405853597860912143037 2262902195099197842053639)
            ·
              refine ⟨3394353292648796763080459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262902195099197842053639 3394353292648796763080459)
              ·
                refine ⟨5091529938973195144620689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394353292648796763080459 5091529938973195144620689)
                ·
                  refine ⟨3818647454229896358465517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5091529938973195144620689 3818647454229896358465517)
                  ·
                    refine ⟨1431992795336211134424569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3818647454229896358465517 1431992795336211134424569)
                    ·
                      refine ⟨1073994596502158350818427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1431992795336211134424569 1073994596502158350818427)
                      ·
                        rfl

theorem cell23_2091597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_2091597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091597 prefixEnd_2091597 := by exact prefixLift 2091597
  have htrace : WordTrace (prefixWord ++ tailWord_2091597) baseStart_2091597 baseEnd_2091597 := by
    simpa [prefixWord, tailWord_2091597, baseEnd_2091597] using wordTrace_append hprefix tailTrace_2091597
  have hstable : (prefixWord ++ tailWord_2091597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091597).length < 2 ^ (prefixWord ++ tailWord_2091597).sum := by decide
  have hdescent : baseEnd_2091597 < baseStart_2091597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091637 : List Nat := [1, 3, 4, 2, 2, 1, 3, 1, 2, 4]
def baseStart_2091637 : Nat := 118140960795 + 2091637 * 2 ^ 59
def prefixEnd_2091637 : Nat := 4983230072969 + 3 ^ 40 * 2091637 * 2
def baseEnd_2091637 : Nat := 358005045242779398106081

theorem tailTrace_2091637 : CollatzResearch.WordTrace tailWord_2091637 prefixEnd_2091637 358005045242779398106081 := by
  unfold tailWord_2091637
  simp only [CollatzResearch.WordTrace]
  refine ⟨76288268723363847004721165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50858845815575898003147443 76288268723363847004721165)
  ·
    refine ⟨28608100771261442626770437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76288268723363847004721165 28608100771261442626770437)
    ·
      refine ⟨5364018894611520492519457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28608100771261442626770437 5364018894611520492519457)
      ·
        refine ⟨4023014170958640369389593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5364018894611520492519457 4023014170958640369389593)
        ·
          refine ⟨3017260628218980277042195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4023014170958640369389593 3017260628218980277042195)
          ·
            refine ⟨4525890942328470415563293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3017260628218980277042195 4525890942328470415563293)
            ·
              refine ⟨1697209103373176405836235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4525890942328470415563293 1697209103373176405836235)
              ·
                refine ⟨2545813655059764608754353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697209103373176405836235 2545813655059764608754353)
                ·
                  refine ⟨1909360241294823456565765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2545813655059764608754353 1909360241294823456565765)
                  ·
                    refine ⟨358005045242779398106081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1909360241294823456565765 358005045242779398106081)
                    ·
                      rfl

theorem cell23_2091637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_2091637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091637 prefixEnd_2091637 := by exact prefixLift 2091637
  have htrace : WordTrace (prefixWord ++ tailWord_2091637) baseStart_2091637 baseEnd_2091637 := by
    simpa [prefixWord, tailWord_2091637, baseEnd_2091637] using wordTrace_append hprefix tailTrace_2091637
  have hstable : (prefixWord ++ tailWord_2091637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091637).length < 2 ^ (prefixWord ++ tailWord_2091637).sum := by decide
  have hdescent : baseEnd_2091637 < baseStart_2091637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091659 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 4, 6]
def baseStart_2091659 : Nat := 118140960795 + 2091659 * 2 ^ 59
def prefixEnd_2091659 : Nat := 4983230072969 + 3 ^ 40 * 2091659 * 2
def baseEnd_2091659 : Nat := 358008810767579036081047

theorem tailTrace_2091659 : CollatzResearch.WordTrace tailWord_2091659 prefixEnd_2091659 358008810767579036081047 := by
  unfold tailWord_2091659
  simp only [CollatzResearch.WordTrace]
  refine ⟨76289071129284144762022031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50859380752856096508014687 76289071129284144762022031)
  ·
    refine ⟨114433606693926217143033047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76289071129284144762022031 114433606693926217143033047)
    ·
      refine ⟨171650410040889325714549571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114433606693926217143033047 171650410040889325714549571)
      ·
        refine ⟨257475615061333988571824357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171650410040889325714549571 257475615061333988571824357)
        ·
          refine ⟨48276677824000122857217067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257475615061333988571824357 48276677824000122857217067)
          ·
            refine ⟨72415016736000184285825601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48276677824000122857217067 72415016736000184285825601)
            ·
              refine ⟨54311262552000138214369201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72415016736000184285825601 54311262552000138214369201)
              ·
                refine ⟨40733446914000103660776901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54311262552000138214369201 40733446914000103660776901)
                ·
                  refine ⟨7637521296375019436395669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40733446914000103660776901 7637521296375019436395669)
                  ·
                    refine ⟨358008810767579036081047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7637521296375019436395669 358008810767579036081047)
                    ·
                      rfl

theorem cell23_2091659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 6].length) (baseStart_2091659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091659 prefixEnd_2091659 := by exact prefixLift 2091659
  have htrace : WordTrace (prefixWord ++ tailWord_2091659) baseStart_2091659 baseEnd_2091659 := by
    simpa [prefixWord, tailWord_2091659, baseEnd_2091659] using wordTrace_append hprefix tailTrace_2091659
  have hstable : (prefixWord ++ tailWord_2091659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091659).length < 2 ^ (prefixWord ++ tailWord_2091659).sum := by decide
  have hdescent : baseEnd_2091659 < baseStart_2091659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091694 : List Nat := [4, 1, 4, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_2091694 : Nat := 118140960795 + 2091694 * 2 ^ 59
def prefixEnd_2091694 : Nat := 4983230072969 + 3 ^ 40 * 2091694 * 2
def baseEnd_2091694 : Nat := 1074044404125644471305481

theorem tailTrace_2091694 : CollatzResearch.WordTrace tailWord_2091694 prefixEnd_2091694 1074044404125644471305481 := by
  unfold tailWord_2091694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9536293460519668217443267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50860231789438230493030757 9536293460519668217443267)
  ·
    refine ⟨14304440190779502326164901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9536293460519668217443267 14304440190779502326164901)
    ·
      refine ⟨2682082535771156686155919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14304440190779502326164901 2682082535771156686155919)
      ·
        refine ⟨4023123803656735029233879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2682082535771156686155919 4023123803656735029233879)
        ·
          refine ⟨6034685705485102543850819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023123803656735029233879 6034685705485102543850819)
          ·
            refine ⟨9052028558227653815776229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6034685705485102543850819 9052028558227653815776229)
            ·
              refine ⟨1697255354667685090458043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9052028558227653815776229 1697255354667685090458043)
              ·
                refine ⟨2545883032001527635687065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697255354667685090458043 2545883032001527635687065)
                ·
                  refine ⟨1909412274001145726765299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2545883032001527635687065 1909412274001145726765299)
                  ·
                    refine ⟨2864118411001718590147949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1909412274001145726765299 2864118411001718590147949)
                    ·
                      refine ⟨1074044404125644471305481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2864118411001718590147949 1074044404125644471305481)
                      ·
                        rfl

theorem cell23_2091694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_2091694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091694 prefixEnd_2091694 := by exact prefixLift 2091694
  have htrace : WordTrace (prefixWord ++ tailWord_2091694) baseStart_2091694 baseEnd_2091694 := by
    simpa [prefixWord, tailWord_2091694, baseEnd_2091694] using wordTrace_append hprefix tailTrace_2091694
  have hstable : (prefixWord ++ tailWord_2091694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091694).length < 2 ^ (prefixWord ++ tailWord_2091694).sum := by decide
  have hdescent : baseEnd_2091694 < baseStart_2091694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091743 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 2, 5, 2]
def baseStart_2091743 : Nat := 118140960795 + 2091743 * 2 ^ 59
def prefixEnd_2091743 : Nat := 4983230072969 + 3 ^ 40 * 2091743 * 2
def baseEnd_2091743 : Nat := 1074069564677714779592755

theorem tailTrace_2091743 : CollatzResearch.WordTrace tailWord_2091743 prefixEnd_2091743 1074069564677714779592755 := by
  unfold tailWord_2091743
  simp only [CollatzResearch.WordTrace]
  refine ⟨76292134860979827108079883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50861423240653218072053255 76292134860979827108079883)
  ·
    refine ⟨114438202291469740662119825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76292134860979827108079883 114438202291469740662119825)
    ·
      refine ⟨85828651718602305496589869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114438202291469740662119825 85828651718602305496589869)
      ·
        refine ⟨32185744394475864561221201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85828651718602305496589869 32185744394475864561221201)
        ·
          refine ⟨24139308295856898420915901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32185744394475864561221201 24139308295856898420915901)
          ·
            refine ⟨9052240610946336907843463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24139308295856898420915901 9052240610946336907843463)
            ·
              refine ⟨13578360916419505361765195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9052240610946336907843463 13578360916419505361765195)
              ·
                refine ⟨20367541374629258042647793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13578360916419505361765195 20367541374629258042647793)
                ·
                  refine ⟨15275656030971943531985845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20367541374629258042647793 15275656030971943531985845)
                  ·
                    refine ⟨1432092752903619706123673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15275656030971943531985845 1432092752903619706123673)
                    ·
                      refine ⟨1074069564677714779592755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1432092752903619706123673 1074069564677714779592755)
                      ·
                        rfl

theorem cell23_2091743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_2091743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091743 prefixEnd_2091743 := by exact prefixLift 2091743
  have htrace : WordTrace (prefixWord ++ tailWord_2091743) baseStart_2091743 baseEnd_2091743 := by
    simpa [prefixWord, tailWord_2091743, baseEnd_2091743] using wordTrace_append hprefix tailTrace_2091743
  have hstable : (prefixWord ++ tailWord_2091743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091743).length < 2 ^ (prefixWord ++ tailWord_2091743).sum := by decide
  have hdescent : baseEnd_2091743 < baseStart_2091743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091756 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_2091756 : Nat := 118140960795 + 2091756 * 2 ^ 59
def prefixEnd_2091756 : Nat := 4983230072969 + 3 ^ 40 * 2091756 * 2
def baseEnd_2091756 : Nat := 1074076239926223228730195

theorem tailTrace_2091756 : CollatzResearch.WordTrace tailWord_2091756 prefixEnd_2091756 1074076239926223228730195 := by
  unfold tailWord_2091756
  simp only [CollatzResearch.WordTrace]
  refine ⟨38146304504966365164151561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50861739339955153552202081 38146304504966365164151561)
  ·
    refine ⟨28609728378724773873113671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38146304504966365164151561 28609728378724773873113671)
    ·
      refine ⟨42914592568087160809670507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28609728378724773873113671 42914592568087160809670507)
      ·
        refine ⟨64371888852130741214505761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42914592568087160809670507 64371888852130741214505761)
        ·
          refine ⟨48278916639098055910879321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64371888852130741214505761 48278916639098055910879321)
          ·
            refine ⟨36209187479323541933159491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48278916639098055910879321 36209187479323541933159491)
            ·
              refine ⟨54313781218985312899739237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36209187479323541933159491 54313781218985312899739237)
              ·
                refine ⟨10183833978559746168701107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54313781218985312899739237 10183833978559746168701107)
                ·
                  refine ⟨15275750967839619253051661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10183833978559746168701107 15275750967839619253051661)
                  ·
                    refine ⟨5728406612939857219894373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15275750967839619253051661 5728406612939857219894373)
                    ·
                      refine ⟨1074076239926223228730195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5728406612939857219894373 1074076239926223228730195)
                      ·
                        rfl

theorem cell23_2091756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_2091756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091756 prefixEnd_2091756 := by exact prefixLift 2091756
  have htrace : WordTrace (prefixWord ++ tailWord_2091756) baseStart_2091756 baseEnd_2091756 := by
    simpa [prefixWord, tailWord_2091756, baseEnd_2091756] using wordTrace_append hprefix tailTrace_2091756
  have hstable : (prefixWord ++ tailWord_2091756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091756).length < 2 ^ (prefixWord ++ tailWord_2091756).sum := by decide
  have hdescent : baseEnd_2091756 < baseStart_2091756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091773 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 1, 6, 2]
def baseStart_2091773 : Nat := 118140960795 + 2091773 * 2 ^ 59
def prefixEnd_2091773 : Nat := 4983230072969 + 3 ^ 40 * 2091773 * 2
def baseEnd_2091773 : Nat := 1074084969097349662217617

theorem tailTrace_2091773 : CollatzResearch.WordTrace tailWord_2091773 prefixEnd_2091773 1074084969097349662217617 := by
  unfold tailWord_2091773
  simp only [CollatzResearch.WordTrace]
  refine ⟨76293229050871142231671973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50862152700580761487781315 76293229050871142231671973)
  ·
    refine ⟨14304980447038339168438495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76293229050871142231671973 14304980447038339168438495)
    ·
      refine ⟨21457470670557508752657743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14304980447038339168438495 21457470670557508752657743)
      ·
        refine ⟨32186206005836263128986615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21457470670557508752657743 32186206005836263128986615)
        ·
          refine ⟨48279309008754394693479923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32186206005836263128986615 48279309008754394693479923)
          ·
            refine ⟨72418963513131592040219885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48279309008754394693479923 72418963513131592040219885)
            ·
              refine ⟨27157111317424347015082457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72418963513131592040219885 27157111317424347015082457)
              ·
                refine ⟨20367833488068260261311843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27157111317424347015082457 20367833488068260261311843)
                ·
                  refine ⟨30551750232102390391967765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20367833488068260261311843 30551750232102390391967765)
                  ·
                    refine ⟨1432113292129799549623489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30551750232102390391967765 1432113292129799549623489)
                    ·
                      refine ⟨1074084969097349662217617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1432113292129799549623489 1074084969097349662217617)
                      ·
                        rfl

theorem cell23_2091773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_2091773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091773 prefixEnd_2091773 := by exact prefixLift 2091773
  have htrace : WordTrace (prefixWord ++ tailWord_2091773) baseStart_2091773 baseEnd_2091773 := by
    simpa [prefixWord, tailWord_2091773, baseEnd_2091773] using wordTrace_append hprefix tailTrace_2091773
  have hstable : (prefixWord ++ tailWord_2091773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091773).length < 2 ^ (prefixWord ++ tailWord_2091773).sum := by decide
  have hdescent : baseEnd_2091773 < baseStart_2091773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091786 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2091786 : Nat := 118140960795 + 2091786 * 2 ^ 59
def prefixEnd_2091786 : Nat := 4983230072969 + 3 ^ 40 * 2091786 * 2
def baseEnd_2091786 : Nat := 1074091644345858111355057

theorem tailTrace_2091786 : CollatzResearch.WordTrace tailWord_2091786 prefixEnd_2091786 1074091644345858111355057 := by
  unfold tailWord_2091786
  simp only [CollatzResearch.WordTrace]
  refine ⟨19073425799956011362973803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50862468799882696967930141 19073425799956011362973803)
  ·
    refine ⟨28610138699934017044460705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19073425799956011362973803 28610138699934017044460705)
    ·
      refine ⟨21457604024950512783345529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28610138699934017044460705 21457604024950512783345529)
      ·
        refine ⟨16093203018712884587509147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21457604024950512783345529 16093203018712884587509147)
        ·
          refine ⟨24139804528069326881263721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16093203018712884587509147 24139804528069326881263721)
          ·
            refine ⟨18104853396051995160947791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24139804528069326881263721 18104853396051995160947791)
            ·
              refine ⟨27157280094077992741421687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18104853396051995160947791 27157280094077992741421687)
              ·
                refine ⟨40735920141116989112132531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27157280094077992741421687 40735920141116989112132531)
                ·
                  refine ⟨61103880211675483668198797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40735920141116989112132531 61103880211675483668198797)
                  ·
                    refine ⟨22913955079378306375574549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61103880211675483668198797 22913955079378306375574549)
                    ·
                      refine ⟨1074091644345858111355057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22913955079378306375574549 1074091644345858111355057)
                      ·
                        rfl

theorem cell23_2091786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2091786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091786 prefixEnd_2091786 := by exact prefixLift 2091786
  have htrace : WordTrace (prefixWord ++ tailWord_2091786) baseStart_2091786 baseEnd_2091786 := by
    simpa [prefixWord, tailWord_2091786, baseEnd_2091786] using wordTrace_append hprefix tailTrace_2091786
  have hstable : (prefixWord ++ tailWord_2091786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091786).length < 2 ^ (prefixWord ++ tailWord_2091786).sum := by decide
  have hdescent : baseEnd_2091786 < baseStart_2091786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091793 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 3]
def baseStart_2091793 : Nat := 118140960795 + 2091793 * 2 ^ 59
def prefixEnd_2091793 : Nat := 4983230072969 + 3 ^ 40 * 2091793 * 2
def baseEnd_2091793 : Nat := 1074095238710439583967525

theorem tailTrace_2091793 : CollatzResearch.WordTrace tailWord_2091793 prefixEnd_2091793 1074095238710439583967525 := by
  unfold tailWord_2091793
  simp only [CollatzResearch.WordTrace]
  refine ⟨76293958510798685647400033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50862639007199123764933355 76293958510798685647400033)
  ·
    refine ⟨57220468883099014235550025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76293958510798685647400033 57220468883099014235550025)
    ·
      refine ⟨42915351662324260676662519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57220468883099014235550025 42915351662324260676662519)
      ·
        refine ⟨64373027493486391014993779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42915351662324260676662519 64373027493486391014993779)
        ·
          refine ⟨96559541240229586522490669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64373027493486391014993779 96559541240229586522490669)
          ·
            refine ⟨36209827965086094945934001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96559541240229586522490669 36209827965086094945934001)
            ·
              refine ⟨27157370973814571209450501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36209827965086094945934001 27157370973814571209450501)
              ·
                refine ⟨5092007057590232101771969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27157370973814571209450501 5092007057590232101771969)
                ·
                  refine ⟨3819005293192674076328977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5092007057590232101771969 3819005293192674076328977)
                  ·
                    refine ⟨2864253969894505557246733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3819005293192674076328977 2864253969894505557246733)
                    ·
                      refine ⟨1074095238710439583967525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2864253969894505557246733 1074095238710439583967525)
                      ·
                        rfl

theorem cell23_2091793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_2091793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091793 prefixEnd_2091793 := by exact prefixLift 2091793
  have htrace : WordTrace (prefixWord ++ tailWord_2091793) baseStart_2091793 baseEnd_2091793 := by
    simpa [prefixWord, tailWord_2091793, baseEnd_2091793] using wordTrace_append hprefix tailTrace_2091793
  have hstable : (prefixWord ++ tailWord_2091793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091793).length < 2 ^ (prefixWord ++ tailWord_2091793).sum := by decide
  have hdescent : baseEnd_2091793 < baseStart_2091793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091834 : List Nat := [3, 1, 1, 1, 6, 2, 1, 3, 1, 4]
def baseStart_2091834 : Nat := 118140960795 + 2091834 * 2 ^ 59
def prefixEnd_2091834 : Nat := 4983230072969 + 3 ^ 40 * 2091834 * 2
def baseEnd_2091834 : Nat := 358038763805757974518279

theorem tailTrace_2091834 : CollatzResearch.WordTrace tailWord_2091834 prefixEnd_2091834 358038763805757974518279 := by
  unfold tailWord_2091834
  simp only [CollatzResearch.WordTrace]
  refine ⟨19073863475912537412410639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50863635935766766433095037 19073863475912537412410639)
  ·
    refine ⟨28610795213868806118615959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19073863475912537412410639 28610795213868806118615959)
    ·
      refine ⟨42916192820803209177923939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28610795213868806118615959 42916192820803209177923939)
      ·
        refine ⟨64374289231204813766885909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42916192820803209177923939 64374289231204813766885909)
        ·
          refine ⟨3017544807712725645322777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64374289231204813766885909 3017544807712725645322777)
          ·
            refine ⟨2263158605784544233992083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3017544807712725645322777 2263158605784544233992083)
            ·
              refine ⟨3394737908676816350988125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2263158605784544233992083 3394737908676816350988125)
              ·
                refine ⟨1273026715753806131620547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3394737908676816350988125 1273026715753806131620547)
                ·
                  refine ⟨1909540073630709197430821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1273026715753806131620547 1909540073630709197430821)
                  ·
                    refine ⟨358038763805757974518279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1909540073630709197430821 358038763805757974518279)
                    ·
                      rfl

theorem cell23_2091834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_2091834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091834 prefixEnd_2091834 := by exact prefixLift 2091834
  have htrace : WordTrace (prefixWord ++ tailWord_2091834) baseStart_2091834 baseEnd_2091834 := by
    simpa [prefixWord, tailWord_2091834, baseEnd_2091834] using wordTrace_append hprefix tailTrace_2091834
  have hstable : (prefixWord ++ tailWord_2091834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091834).length < 2 ^ (prefixWord ++ tailWord_2091834).sum := by decide
  have hdescent : baseEnd_2091834 < baseStart_2091834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091843 : List Nat := [1, 1, 1, 3, 1, 4, 1, 5, 1, 5]
def baseStart_2091843 : Nat := 118140960795 + 2091843 * 2 ^ 59
def prefixEnd_2091843 : Nat := 4983230072969 + 3 ^ 40 * 2091843 * 2
def baseEnd_2091843 : Nat := 358040304247721462780765

theorem tailTrace_2091843 : CollatzResearch.WordTrace tailWord_2091843 prefixEnd_2091843 358040304247721462780765 := by
  unfold tailWord_2091843
  simp only [CollatzResearch.WordTrace]
  refine ⟨76295782160617544186720183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50863854773745029457813455 76295782160617544186720183)
  ·
    refine ⟨114443673240926316280080275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76295782160617544186720183 114443673240926316280080275)
    ·
      refine ⟨171665509861389474420120413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114443673240926316280080275 171665509861389474420120413)
      ·
        refine ⟨64374566198021052907545155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171665509861389474420120413 64374566198021052907545155)
        ·
          refine ⟨96561849297031579361317733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64374566198021052907545155 96561849297031579361317733)
          ·
            refine ⟨18105346743193421130247075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96561849297031579361317733 18105346743193421130247075)
            ·
              refine ⟨27158020114790131695370613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18105346743193421130247075 27158020114790131695370613)
              ·
                refine ⟨2546064385761574846440995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27158020114790131695370613 2546064385761574846440995)
                ·
                  refine ⟨3819096578642362269661493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546064385761574846440995 3819096578642362269661493)
                  ·
                    refine ⟨358040304247721462780765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3819096578642362269661493 358040304247721462780765)
                    ·
                      rfl

theorem cell23_2091843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 5].length) (baseStart_2091843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091843 prefixEnd_2091843 := by exact prefixLift 2091843
  have htrace : WordTrace (prefixWord ++ tailWord_2091843) baseStart_2091843 baseEnd_2091843 := by
    simpa [prefixWord, tailWord_2091843, baseEnd_2091843] using wordTrace_append hprefix tailTrace_2091843
  have hstable : (prefixWord ++ tailWord_2091843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091843).length < 2 ^ (prefixWord ++ tailWord_2091843).sum := by decide
  have hdescent : baseEnd_2091843 < baseStart_2091843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091844 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2091844 : Nat := 118140960795 + 2091844 * 2 ^ 59
def prefixEnd_2091844 : Nat := 4983230072969 + 3 ^ 40 * 2091844 * 2
def baseEnd_2091844 : Nat := 1074121426223818884429791

theorem tailTrace_2091844 : CollatzResearch.WordTrace tailWord_2091844 prefixEnd_2091844 1074121426223818884429791 := by
  unfold tailWord_2091844
  simp only [CollatzResearch.WordTrace]
  refine ⟨38147909316806960678753293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50863879089075947571671057 38147909316806960678753293)
  ·
    refine ⟨14305465993802610254532485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38147909316806960678753293 14305465993802610254532485)
    ·
      refine ⟨2682274873837989422724841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14305465993802610254532485 2682274873837989422724841)
      ·
        refine ⟨2011706155378492067043631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2682274873837989422724841 2011706155378492067043631)
        ·
          refine ⟨3017559233067738100565447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011706155378492067043631 3017559233067738100565447)
          ·
            refine ⟨4526338849601607150848171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3017559233067738100565447 4526338849601607150848171)
            ·
              refine ⟨6789508274402410726272257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4526338849601607150848171 6789508274402410726272257)
              ·
                refine ⟨5092131205801808044704193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6789508274402410726272257 5092131205801808044704193)
                ·
                  refine ⟨3819098404351356033528145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5092131205801808044704193 3819098404351356033528145)
                  ·
                    refine ⟨2864323803263517025146109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3819098404351356033528145 2864323803263517025146109)
                    ·
                      refine ⟨1074121426223818884429791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2864323803263517025146109 1074121426223818884429791)
                      ·
                        rfl

theorem cell23_2091844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2091844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091844 prefixEnd_2091844 := by exact prefixLift 2091844
  have htrace : WordTrace (prefixWord ++ tailWord_2091844) baseStart_2091844 baseEnd_2091844 := by
    simpa [prefixWord, tailWord_2091844, baseEnd_2091844] using wordTrace_append hprefix tailTrace_2091844
  have hstable : (prefixWord ++ tailWord_2091844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091844).length < 2 ^ (prefixWord ++ tailWord_2091844).sum := by decide
  have hdescent : baseEnd_2091844 < baseStart_2091844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091873 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 6, 4]
def baseStart_2091873 : Nat := 118140960795 + 2091873 * 2 ^ 59
def prefixEnd_2091873 : Nat := 4983230072969 + 3 ^ 40 * 2091873 * 2
def baseEnd_2091873 : Nat := 358045439054266423655719

theorem tailTrace_2091873 : CollatzResearch.WordTrace tailWord_2091873 prefixEnd_2091873 358045439054266423655719 := by
  unfold tailWord_2091873
  simp only [CollatzResearch.WordTrace]
  refine ⟨76296876350508859310312273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50864584233672572873541515 76296876350508859310312273)
  ·
    refine ⟨57222657262881644482734205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76296876350508859310312273 57222657262881644482734205)
    ·
      refine ⟨21458496473580616681025327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57222657262881644482734205 21458496473580616681025327)
      ·
        refine ⟨32187744710370925021537991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21458496473580616681025327 32187744710370925021537991)
        ·
          refine ⟨48281617065556387532306987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32187744710370925021537991 48281617065556387532306987)
          ·
            refine ⟨72422425598334581298460481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48281617065556387532306987 72422425598334581298460481)
            ·
              refine ⟨54316819198750935973845361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72422425598334581298460481 54316819198750935973845361)
              ·
                refine ⟨40737614399063201980384021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54316819198750935973845361 40737614399063201980384021)
                ·
                  refine ⟨1909575674956087592830501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40737614399063201980384021 1909575674956087592830501)
                  ·
                    refine ⟨358045439054266423655719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1909575674956087592830501 358045439054266423655719)
                    ·
                      rfl

theorem cell23_2091873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_2091873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091873 prefixEnd_2091873 := by exact prefixLift 2091873
  have htrace : WordTrace (prefixWord ++ tailWord_2091873) baseStart_2091873 baseEnd_2091873 := by
    simpa [prefixWord, tailWord_2091873, baseEnd_2091873] using wordTrace_append hprefix tailTrace_2091873
  have hstable : (prefixWord ++ tailWord_2091873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091873).length < 2 ^ (prefixWord ++ tailWord_2091873).sum := by decide
  have hdescent : baseEnd_2091873 < baseStart_2091873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091880 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2091880 : Nat := 118140960795 + 2091880 * 2 ^ 59
def prefixEnd_2091880 : Nat := 4983230072969 + 3 ^ 40 * 2091880 * 2
def baseEnd_2091880 : Nat := 1074139911527380743579625

theorem tailTrace_2091880 : CollatzResearch.WordTrace tailWord_2091880 prefixEnd_2091880 1074139911527380743579625 := by
  unfold tailWord_2091880
  simp only [CollatzResearch.WordTrace]
  refine ⟨38148565830741749752908547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50864754440988999670544729 38148565830741749752908547)
  ·
    refine ⟨57222848746112624629362821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38148565830741749752908547 57222848746112624629362821)
    ·
      refine ⟨10729284139896117118005529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57222848746112624629362821 10729284139896117118005529)
      ·
        refine ⟨8046963104922087838504147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10729284139896117118005529 8046963104922087838504147)
        ·
          refine ⟨12070444657383131757756221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8046963104922087838504147 12070444657383131757756221)
          ·
            refine ⟨4526416746518674409158583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12070444657383131757756221 4526416746518674409158583)
            ·
              refine ⟨6789625119778011613737875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4526416746518674409158583 6789625119778011613737875)
              ·
                refine ⟨10184437679667017420606813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6789625119778011613737875 10184437679667017420606813)
                ·
                  refine ⟨3819164129875131532727555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10184437679667017420606813 3819164129875131532727555)
                  ·
                    refine ⟨5728746194812697299091333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3819164129875131532727555 5728746194812697299091333)
                    ·
                      refine ⟨1074139911527380743579625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5728746194812697299091333 1074139911527380743579625)
                      ·
                        rfl

theorem cell23_2091880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2091880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091880 prefixEnd_2091880 := by exact prefixLift 2091880
  have htrace : WordTrace (prefixWord ++ tailWord_2091880) baseStart_2091880 baseEnd_2091880 := by
    simpa [prefixWord, tailWord_2091880, baseEnd_2091880] using wordTrace_append hprefix tailTrace_2091880
  have hstable : (prefixWord ++ tailWord_2091880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091880).length < 2 ^ (prefixWord ++ tailWord_2091880).sum := by decide
  have hdescent : baseEnd_2091880 < baseStart_2091880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091894 : List Nat := [5, 1, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_2091894 : Nat := 118140960795 + 2091894 * 2 ^ 59
def prefixEnd_2091894 : Nat := 4983230072969 + 3 ^ 40 * 2091894 * 2
def baseEnd_2091894 : Nat := 358049033418847896268187

theorem tailTrace_2091894 : CollatzResearch.WordTrace tailWord_2091894 prefixEnd_2091894 358049033418847896268187 := by
  unfold tailWord_2091894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4768602642714548743551671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50865094855621853264551157 4768602642714548743551671)
  ·
    refine ⟨7152903964071823115327507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4768602642714548743551671 7152903964071823115327507)
    ·
      refine ⟨10729355946107734672991261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7152903964071823115327507 10729355946107734672991261)
      ·
        refine ⟨4023508479790400502371723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10729355946107734672991261 4023508479790400502371723)
        ·
          refine ⟨6035262719685600753557585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023508479790400502371723 6035262719685600753557585)
          ·
            refine ⟨4526447039764200565168189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6035262719685600753557585 4526447039764200565168189)
            ·
              refine ⟨1697417639911575211938071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4526447039764200565168189 1697417639911575211938071)
              ·
                refine ⟨2546126459867362817907107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697417639911575211938071 2546126459867362817907107)
                ·
                  refine ⟨3819189689801044226860661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546126459867362817907107 3819189689801044226860661)
                  ·
                    refine ⟨358049033418847896268187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3819189689801044226860661 358049033418847896268187)
                    ·
                      rfl

theorem cell23_2091894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_2091894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091894 prefixEnd_2091894 := by exact prefixLift 2091894
  have htrace : WordTrace (prefixWord ++ tailWord_2091894) baseStart_2091894 baseEnd_2091894 := by
    simpa [prefixWord, tailWord_2091894, baseEnd_2091894] using wordTrace_append hprefix tailTrace_2091894
  have hstable : (prefixWord ++ tailWord_2091894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091894).length < 2 ^ (prefixWord ++ tailWord_2091894).sum := by decide
  have hdescent : baseEnd_2091894 < baseStart_2091894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091897 : List Nat := [1, 2, 1, 3, 2, 4, 3, 1, 1, 1, 4]
def baseStart_2091897 : Nat := 118140960795 + 2091897 * 2 ^ 59
def prefixEnd_2091897 : Nat := 4983230072969 + 3 ^ 40 * 2091897 * 2
def baseEnd_2091897 : Nat := 1074148640698507177067047

theorem tailTrace_2091897 : CollatzResearch.WordTrace tailWord_2091897 prefixEnd_2091897 1074148640698507177067047 := by
  unfold tailWord_2091897
  simp only [CollatzResearch.WordTrace]
  refine ⟨76297751702421911409185945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50865167801614607606123963 76297751702421911409185945)
  ·
    refine ⟨57223313776816433556889459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76297751702421911409185945 57223313776816433556889459)
    ·
      refine ⟨85834970665224650335334189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57223313776816433556889459 85834970665224650335334189)
      ·
        refine ⟨32188113999459243875750321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85834970665224650335334189 32188113999459243875750321)
        ·
          refine ⟨24141085499594432906812741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32188113999459243875750321 24141085499594432906812741)
          ·
            refine ⟨4526453531173956170027389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24141085499594432906812741 4526453531173956170027389)
            ·
              refine ⟨1697420074190233563760271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4526453531173956170027389 1697420074190233563760271)
              ·
                refine ⟨2546130111285350345640407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697420074190233563760271 2546130111285350345640407)
                ·
                  refine ⟨3819195166928025518460611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546130111285350345640407 3819195166928025518460611)
                  ·
                    refine ⟨5728792750392038277690917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3819195166928025518460611 5728792750392038277690917)
                    ·
                      refine ⟨1074148640698507177067047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5728792750392038277690917 1074148640698507177067047)
                      ·
                        rfl

theorem cell23_2091897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_2091897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091897 prefixEnd_2091897 := by exact prefixLift 2091897
  have htrace : WordTrace (prefixWord ++ tailWord_2091897) baseStart_2091897 baseEnd_2091897 := by
    simpa [prefixWord, tailWord_2091897, baseEnd_2091897] using wordTrace_append hprefix tailTrace_2091897
  have hstable : (prefixWord ++ tailWord_2091897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091897).length < 2 ^ (prefixWord ++ tailWord_2091897).sum := by decide
  have hdescent : baseEnd_2091897 < baseStart_2091897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091900 : List Nat := [2, 2, 2, 1, 1, 1, 1, 7, 1, 2, 3]
def baseStart_2091900 : Nat := 118140960795 + 2091900 * 2 ^ 59
def prefixEnd_2091900 : Nat := 4983230072969 + 3 ^ 40 * 2091900 * 2
def baseEnd_2091900 : Nat := 1074150181140470665329533

theorem tailTrace_2091900 : CollatzResearch.WordTrace tailWord_2091900 prefixEnd_2091900 1074150181140470665329533 := by
  unfold tailWord_2091900
  simp only [CollatzResearch.WordTrace]
  refine ⟨38148930560705521460772577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50865240747607361947696769 38148930560705521460772577)
  ·
    refine ⟨28611697920529141095579433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38148930560705521460772577 28611697920529141095579433)
    ·
      refine ⟨21458773440396855821684575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28611697920529141095579433 21458773440396855821684575)
      ·
        refine ⟨32188160160595283732526863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21458773440396855821684575 32188160160595283732526863)
        ·
          refine ⟨48282240240892925598790295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32188160160595283732526863 48282240240892925598790295)
          ·
            refine ⟨72423360361339388398185443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48282240240892925598790295 72423360361339388398185443)
            ·
              refine ⟨108635040542009082597278165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72423360361339388398185443 108635040542009082597278165)
              ·
                refine ⟨2546133762703337873373707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108635040542009082597278165 2546133762703337873373707)
                ·
                  refine ⟨3819200644055006810060561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546133762703337873373707 3819200644055006810060561)
                  ·
                    refine ⟨2864400483041255107545421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3819200644055006810060561 2864400483041255107545421)
                    ·
                      refine ⟨1074150181140470665329533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2864400483041255107545421 1074150181140470665329533)
                      ·
                        rfl

theorem cell23_2091900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_2091900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091900 prefixEnd_2091900 := by exact prefixLift 2091900
  have htrace : WordTrace (prefixWord ++ tailWord_2091900) baseStart_2091900 baseEnd_2091900 := by
    simpa [prefixWord, tailWord_2091900, baseEnd_2091900] using wordTrace_append hprefix tailTrace_2091900
  have hstable : (prefixWord ++ tailWord_2091900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091900).length < 2 ^ (prefixWord ++ tailWord_2091900).sum := by decide
  have hdescent : baseEnd_2091900 < baseStart_2091900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091933 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_2091933 : Nat := 118140960795 + 2091933 * 2 ^ 59
def prefixEnd_2091933 : Nat := 4983230072969 + 3 ^ 40 * 2091933 * 2
def baseEnd_2091933 : Nat := 358055708667356345405627

theorem tailTrace_2091933 : CollatzResearch.WordTrace tailWord_2091933 prefixEnd_2091933 358055708667356345405627 := by
  unfold tailWord_2091933
  simp only [CollatzResearch.WordTrace]
  refine ⟨76299064730291489557496453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50866043153527659704997635 76299064730291489557496453)
  ·
    refine ⟨14306074636929654292030585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76299064730291489557496453 14306074636929654292030585)
    ·
      refine ⟨10729555977697240719022939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14306074636929654292030585 10729555977697240719022939)
      ·
        refine ⟨16094333966545861078534409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10729555977697240719022939 16094333966545861078534409)
        ·
          refine ⟨12070750474909395808900807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16094333966545861078534409 12070750474909395808900807)
          ·
            refine ⟨18106125712364093713351211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12070750474909395808900807 18106125712364093713351211)
            ·
              refine ⟨27159188568546140570026817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18106125712364093713351211 27159188568546140570026817)
              ·
                refine ⟨20369391426409605427520113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27159188568546140570026817 20369391426409605427520113)
                ·
                  refine ⟨15277043569807204070640085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20369391426409605427520113 15277043569807204070640085)
                  ·
                    refine ⟨358055708667356345405627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15277043569807204070640085 358055708667356345405627)
                    ·
                      rfl

theorem cell23_2091933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_2091933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2091933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2091933 prefixEnd_2091933 := by exact prefixLift 2091933
  have htrace : WordTrace (prefixWord ++ tailWord_2091933) baseStart_2091933 baseEnd_2091933 := by
    simpa [prefixWord, tailWord_2091933, baseEnd_2091933] using wordTrace_append hprefix tailTrace_2091933
  have hstable : (prefixWord ++ tailWord_2091933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091933).length < 2 ^ (prefixWord ++ tailWord_2091933).sum := by decide
  have hdescent : baseEnd_2091933 < baseStart_2091933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092094 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_2092094 : Nat := 118140960795 + 2092094 * 2 ^ 59
def prefixEnd_2092094 : Nat := 4983230072969 + 3 ^ 40 * 2092094 * 2
def baseEnd_2092094 : Nat := 1074249796387442906303641

theorem tailTrace_2092094 : CollatzResearch.WordTrace tailWord_2092094 prefixEnd_2092094 1074249796387442906303641 := by
  unfold tailWord_2092094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9538117110338526756763417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50869957921805476036071557 9538117110338526756763417)
  ·
    refine ⟨7153587832753895067572563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9538117110338526756763417 7153587832753895067572563)
    ·
      refine ⟨10730381749130842601358845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7153587832753895067572563 10730381749130842601358845)
      ·
        refine ⟨4023893155924065975509567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10730381749130842601358845 4023893155924065975509567)
        ·
          refine ⟨6035839733886098963264351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023893155924065975509567 6035839733886098963264351)
          ·
            refine ⟨9053759600829148444896527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6035839733886098963264351 9053759600829148444896527)
            ·
              refine ⟨13580639401243722667344791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9053759600829148444896527 13580639401243722667344791)
              ·
                refine ⟨20370959101865584001017187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13580639401243722667344791 20370959101865584001017187)
                ·
                  refine ⟨30556438652798376001525781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20370959101865584001017187 30556438652798376001525781)
                  ·
                    refine ⟨1432333061849923875071521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30556438652798376001525781 1432333061849923875071521)
                    ·
                      refine ⟨1074249796387442906303641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1432333061849923875071521 1074249796387442906303641)
                      ·
                        rfl

theorem cell23_2092094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_2092094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092094 prefixEnd_2092094 := by exact prefixLift 2092094
  have htrace : WordTrace (prefixWord ++ tailWord_2092094) baseStart_2092094 baseEnd_2092094 := by
    simpa [prefixWord, tailWord_2092094, baseEnd_2092094] using wordTrace_append hprefix tailTrace_2092094
  have hstable : (prefixWord ++ tailWord_2092094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092094).length < 2 ^ (prefixWord ++ tailWord_2092094).sum := by decide
  have hdescent : baseEnd_2092094 < baseStart_2092094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092114 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_2092114 : Nat := 118140960795 + 2092114 * 2 ^ 59
def prefixEnd_2092114 : Nat := 4983230072969 + 3 ^ 40 * 2092114 * 2
def baseEnd_2092114 : Nat := 1074260066000532828053549

theorem tailTrace_2092114 : CollatzResearch.WordTrace tailWord_2092114 prefixEnd_2092114 1074260066000532828053549 := by
  unfold tailWord_2092114
  simp only [CollatzResearch.WordTrace]
  refine ⟨19076416585658939367458849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50870444228423838313223597 19076416585658939367458849)
  ·
    refine ⟨14307312439244204525594137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19076416585658939367458849 14307312439244204525594137)
    ·
      refine ⟨10730484329433153394195603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14307312439244204525594137 10730484329433153394195603)
      ·
        refine ⟨16095726494149730091293405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10730484329433153394195603 16095726494149730091293405)
        ·
          refine ⟨6035897435306148784235027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16095726494149730091293405 6035897435306148784235027)
          ·
            refine ⟨9053846152959223176352541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6035897435306148784235027 9053846152959223176352541)
            ·
              refine ⟨3395192307359708691132203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9053846152959223176352541 3395192307359708691132203)
              ·
                refine ⟨5092788461039563036698305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395192307359708691132203 5092788461039563036698305)
                ·
                  refine ⟨3819591345779672277523729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5092788461039563036698305 3819591345779672277523729)
                  ·
                    refine ⟨2864693509334754208142797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3819591345779672277523729 2864693509334754208142797)
                    ·
                      refine ⟨1074260066000532828053549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2864693509334754208142797 1074260066000532828053549)
                      ·
                        rfl

theorem cell23_2092114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_2092114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092114 prefixEnd_2092114 := by exact prefixLift 2092114
  have htrace : WordTrace (prefixWord ++ tailWord_2092114) baseStart_2092114 baseEnd_2092114 := by
    simpa [prefixWord, tailWord_2092114, baseEnd_2092114] using wordTrace_append hprefix tailTrace_2092114
  have hstable : (prefixWord ++ tailWord_2092114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092114).length < 2 ^ (prefixWord ++ tailWord_2092114).sum := by decide
  have hdescent : baseEnd_2092114 < baseStart_2092114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092127 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 5, 1, 3]
def baseStart_2092127 : Nat := 118140960795 + 2092127 * 2 ^ 59
def prefixEnd_2092127 : Nat := 4983230072969 + 3 ^ 40 * 2092127 * 2
def baseEnd_2092127 : Nat := 1074266741249041277190989

theorem tailTrace_2092127 : CollatzResearch.WordTrace tailWord_2092127 prefixEnd_2092127 1074266741249041277190989 := by
  unfold tailWord_2092127
  simp only [CollatzResearch.WordTrace]
  refine ⟨76306140491588660690058635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50870760327725773793372423 76306140491588660690058635)
  ·
    refine ⟨114459210737382991035087953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76306140491588660690058635 114459210737382991035087953)
    ·
      refine ⟨85844408053037243276315965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114459210737382991035087953 85844408053037243276315965)
      ·
        refine ⟨32191653019888966228618487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85844408053037243276315965 32191653019888966228618487)
        ·
          refine ⟨48287479529833449342927731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32191653019888966228618487 48287479529833449342927731)
          ·
            refine ⟨72431219294750174014391597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48287479529833449342927731 72431219294750174014391597)
            ·
              refine ⟨27161707235531315255396849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72431219294750174014391597 27161707235531315255396849)
              ·
                refine ⟨20371280426648486441547637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27161707235531315255396849 20371280426648486441547637)
                ·
                  refine ⟨1909807539998295603895091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20371280426648486441547637 1909807539998295603895091)
                  ·
                    refine ⟨2864711309997443405842637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1909807539998295603895091 2864711309997443405842637)
                    ·
                      refine ⟨1074266741249041277190989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2864711309997443405842637 1074266741249041277190989)
                      ·
                        rfl

theorem cell23_2092127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_2092127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092127 prefixEnd_2092127 := by exact prefixLift 2092127
  have htrace : WordTrace (prefixWord ++ tailWord_2092127) baseStart_2092127 baseEnd_2092127 := by
    simpa [prefixWord, tailWord_2092127, baseEnd_2092127] using wordTrace_append hprefix tailTrace_2092127
  have hstable : (prefixWord ++ tailWord_2092127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092127).length < 2 ^ (prefixWord ++ tailWord_2092127).sum := by decide
  have hdescent : baseEnd_2092127 < baseStart_2092127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092144 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 3, 1, 3]
def baseStart_2092144 : Nat := 118140960795 + 2092144 * 2 ^ 59
def prefixEnd_2092144 : Nat := 4983230072969 + 3 ^ 40 * 2092144 * 2
def baseEnd_2092144 : Nat := 1074275470420167710678411

theorem tailTrace_2092144 : CollatzResearch.WordTrace tailWord_2092144 prefixEnd_2092144 1074275470420167710678411 := by
  unfold tailWord_2092144
  simp only [CollatzResearch.WordTrace]
  refine ⟨38153380266263536296713743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50871173688351381728951657 38153380266263536296713743)
  ·
    refine ⟨57230070399395304445070615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38153380266263536296713743 57230070399395304445070615)
    ·
      refine ⟨85845105599092956667605923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57230070399395304445070615 85845105599092956667605923)
      ·
        refine ⟨128767658398639435001408885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85845105599092956667605923 128767658398639435001408885)
        ·
          refine ⟨12071967974872447031382083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128767658398639435001408885 12071967974872447031382083)
          ·
            refine ⟨18107951962308670547073125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12071967974872447031382083 18107951962308670547073125)
            ·
              refine ⟨3395240992932875727576211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18107951962308670547073125 3395240992932875727576211)
              ·
                refine ⟨5092861489399313591364317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395240992932875727576211 5092861489399313591364317)
                ·
                  refine ⟨1909823058524742596761619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5092861489399313591364317 1909823058524742596761619)
                  ·
                    refine ⟨2864734587787113895142429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1909823058524742596761619 2864734587787113895142429)
                    ·
                      refine ⟨1074275470420167710678411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2864734587787113895142429 1074275470420167710678411)
                      ·
                        rfl

theorem cell23_2092144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 3, 1, 3].length) (baseStart_2092144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092144 prefixEnd_2092144 := by exact prefixLift 2092144
  have htrace : WordTrace (prefixWord ++ tailWord_2092144) baseStart_2092144 baseEnd_2092144 := by
    simpa [prefixWord, tailWord_2092144, baseEnd_2092144] using wordTrace_append hprefix tailTrace_2092144
  have hstable : (prefixWord ++ tailWord_2092144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092144).length < 2 ^ (prefixWord ++ tailWord_2092144).sum := by decide
  have hdescent : baseEnd_2092144 < baseStart_2092144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092164 : List Nat := [2, 3, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_2092164 : Nat := 118140960795 + 2092164 * 2 ^ 59
def prefixEnd_2092164 : Nat := 4983230072969 + 3 ^ 40 * 2092164 * 2
def baseEnd_2092164 : Nat := 358095246677752544142773

theorem tailTrace_2092164 : CollatzResearch.WordTrace tailWord_2092164 prefixEnd_2092164 358095246677752544142773 := by
  unfold tailWord_2092164
  simp only [CollatzResearch.WordTrace]
  refine ⟨38153744996227308004577773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50871659994969744006103697 38153744996227308004577773)
  ·
    refine ⟨14307654373585240501716665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38153744996227308004577773 14307654373585240501716665)
    ·
      refine ⟨10730740780188930376287499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14307654373585240501716665 10730740780188930376287499)
      ·
        refine ⟨16096111170283395564431249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10730740780188930376287499 16096111170283395564431249)
        ·
          refine ⟨12072083377712546673323437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16096111170283395564431249 12072083377712546673323437)
          ·
            refine ⟨4527031266642205002496289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12072083377712546673323437 4527031266642205002496289)
            ·
              refine ⟨3395273449981653751872217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4527031266642205002496289 3395273449981653751872217)
              ·
                refine ⟨2546455087486240313904163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395273449981653751872217 2546455087486240313904163)
                ·
                  refine ⟨3819682631229360470856245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546455087486240313904163 3819682631229360470856245)
                  ·
                    refine ⟨358095246677752544142773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3819682631229360470856245 358095246677752544142773)
                    ·
                      rfl

theorem cell23_2092164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_2092164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092164 prefixEnd_2092164 := by exact prefixLift 2092164
  have htrace : WordTrace (prefixWord ++ tailWord_2092164) baseStart_2092164 baseEnd_2092164 := by
    simpa [prefixWord, tailWord_2092164, baseEnd_2092164] using wordTrace_append hprefix tailTrace_2092164
  have hstable : (prefixWord ++ tailWord_2092164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092164).length < 2 ^ (prefixWord ++ tailWord_2092164).sum := by decide
  have hdescent : baseEnd_2092164 < baseStart_2092164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092167 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 1, 8, 2]
def baseStart_2092167 : Nat := 118140960795 + 2092167 * 2 ^ 59
def prefixEnd_2092167 : Nat := 4983230072969 + 3 ^ 40 * 2092167 * 2
def baseEnd_2092167 : Nat := 1074287280475221120690805

theorem tailTrace_2092167 : CollatzResearch.WordTrace tailWord_2092167 prefixEnd_2092167 1074287280475221120690805 := by
  unfold tailWord_2092167
  simp only [CollatzResearch.WordTrace]
  refine ⟨76307599411443747521514755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50871732940962498347676503 76307599411443747521514755)
  ·
    refine ⟨114461399117165621282272133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76307599411443747521514755 114461399117165621282272133)
    ·
      refine ⟨21461512334468553990426025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114461399117165621282272133 21461512334468553990426025)
      ·
        refine ⟨16096134250851415492819519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21461512334468553990426025 16096134250851415492819519)
        ·
          refine ⟨24144201376277123239229279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16096134250851415492819519 24144201376277123239229279)
          ·
            refine ⟨36216302064415684858843919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24144201376277123239229279 36216302064415684858843919)
            ·
              refine ⟨54324453096623527288265879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36216302064415684858843919 54324453096623527288265879)
              ·
                refine ⟨81486679644935290932398819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54324453096623527288265879 81486679644935290932398819)
                ·
                  refine ⟨122230019467402936398598229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81486679644935290932398819 122230019467402936398598229)
                  ·
                    refine ⟨1432383040633628160921073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122230019467402936398598229 1432383040633628160921073)
                    ·
                      refine ⟨1074287280475221120690805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1432383040633628160921073 1074287280475221120690805)
                      ·
                        rfl

theorem cell23_2092167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_2092167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092167 prefixEnd_2092167 := by exact prefixLift 2092167
  have htrace : WordTrace (prefixWord ++ tailWord_2092167) baseStart_2092167 baseEnd_2092167 := by
    simpa [prefixWord, tailWord_2092167, baseEnd_2092167] using wordTrace_append hprefix tailTrace_2092167
  have hstable : (prefixWord ++ tailWord_2092167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092167).length < 2 ^ (prefixWord ++ tailWord_2092167).sum := by decide
  have hdescent : baseEnd_2092167 < baseStart_2092167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092178 : List Nat := [3, 2, 3, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_2092178 : Nat := 118140960795 + 2092178 * 2 ^ 59
def prefixEnd_2092178 : Nat := 4983230072969 + 3 ^ 40 * 2092178 * 2
def baseEnd_2092178 : Nat := 1074292928762420577653255

theorem tailTrace_2092178 : CollatzResearch.WordTrace tailWord_2092178 prefixEnd_2092178 1074292928762420577653255 := by
  unfold tailWord_2092178
  simp only [CollatzResearch.WordTrace]
  refine ⟨19077000153600974100041297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50872000409602597600110125 19077000153600974100041297)
  ·
    refine ⟨14307750115200730575030973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19077000153600974100041297 14307750115200730575030973)
    ·
      refine ⟨5365406293200273965636615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14307750115200730575030973 5365406293200273965636615)
      ·
        refine ⟨8048109439800410948454923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5365406293200273965636615 8048109439800410948454923)
        ·
          refine ⟨12072164159700616422682385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8048109439800410948454923 12072164159700616422682385)
          ·
            refine ⟨9054123119775462317011789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12072164159700616422682385 9054123119775462317011789)
            ·
              refine ⟨3395296169915798368879421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9054123119775462317011789 3395296169915798368879421)
              ·
                refine ⟨1273236063718424388329783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3395296169915798368879421 1273236063718424388329783)
                ·
                  refine ⟨1909854095577636582494675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1273236063718424388329783 1909854095577636582494675)
                  ·
                    refine ⟨2864781143366454873742013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1909854095577636582494675 2864781143366454873742013)
                    ·
                      refine ⟨1074292928762420577653255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2864781143366454873742013 1074292928762420577653255)
                      ·
                        rfl

theorem cell23_2092178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_2092178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092178 prefixEnd_2092178 := by exact prefixLift 2092178
  have htrace : WordTrace (prefixWord ++ tailWord_2092178) baseStart_2092178 baseEnd_2092178 := by
    simpa [prefixWord, tailWord_2092178, baseEnd_2092178] using wordTrace_append hprefix tailTrace_2092178
  have hstable : (prefixWord ++ tailWord_2092178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092178).length < 2 ^ (prefixWord ++ tailWord_2092178).sum := by decide
  have hdescent : baseEnd_2092178 < baseStart_2092178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092184 : List Nat := [2, 1, 2, 4, 2, 1, 2, 3, 1, 1, 4]
def baseStart_2092184 : Nat := 118140960795 + 2092184 * 2 ^ 59
def prefixEnd_2092184 : Nat := 4983230072969 + 3 ^ 40 * 2092184 * 2
def baseEnd_2092184 : Nat := 1074296009646347554178227

theorem tailTrace_2092184 : CollatzResearch.WordTrace tailWord_2092184 prefixEnd_2092184 1074296009646347554178227 := by
  unfold tailWord_2092184
  simp only [CollatzResearch.WordTrace]
  refine ⟨38154109726191079712441803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50872146301588106283255737 38154109726191079712441803)
  ·
    refine ⟨57231164589286619568662705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38154109726191079712441803 57231164589286619568662705)
    ·
      refine ⟨42923373441964964676497029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57231164589286619568662705 42923373441964964676497029)
      ·
        refine ⟨8048132520368430876843193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42923373441964964676497029 8048132520368430876843193)
        ·
          refine ⟨6036099390276323157632395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8048132520368430876843193 6036099390276323157632395)
          ·
            refine ⟨9054149085414484736448593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6036099390276323157632395 9054149085414484736448593)
            ·
              refine ⟨6790611814060863552336445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9054149085414484736448593 6790611814060863552336445)
              ·
                refine ⟨2546479430272823832126167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6790611814060863552336445 2546479430272823832126167)
                ·
                  refine ⟨3819719145409235748189251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546479430272823832126167 3819719145409235748189251)
                  ·
                    refine ⟨5729578718113853622283877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3819719145409235748189251 5729578718113853622283877)
                    ·
                      refine ⟨1074296009646347554178227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5729578718113853622283877 1074296009646347554178227)
                      ·
                        rfl

theorem cell23_2092184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_2092184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092184 prefixEnd_2092184 := by exact prefixLift 2092184
  have htrace : WordTrace (prefixWord ++ tailWord_2092184) baseStart_2092184 baseEnd_2092184 := by
    simpa [prefixWord, tailWord_2092184, baseEnd_2092184] using wordTrace_append hprefix tailTrace_2092184
  have hstable : (prefixWord ++ tailWord_2092184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092184).length < 2 ^ (prefixWord ++ tailWord_2092184).sum := by decide
  have hdescent : baseEnd_2092184 < baseStart_2092184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092234 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_2092234 : Nat := 118140960795 + 2092234 * 2 ^ 59
def prefixEnd_2092234 : Nat := 4983230072969 + 3 ^ 40 * 2092234 * 2
def baseEnd_2092234 : Nat := 1074321683679072358552997

theorem tailTrace_2092234 : CollatzResearch.WordTrace tailWord_2092234 prefixEnd_2092234 1074321683679072358552997 := by
  unfold tailWord_2092234
  simp only [CollatzResearch.WordTrace]
  refine ⟨19077510775550254491050939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50873362068134011976135837 19077510775550254491050939)
  ·
    refine ⟨28616266163325381736576409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19077510775550254491050939 28616266163325381736576409)
    ·
      refine ⟨21462199622494036302432307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28616266163325381736576409 21462199622494036302432307)
      ·
        refine ⟨32193299433741054453648461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21462199622494036302432307 32193299433741054453648461)
        ·
          refine ⟨12072487287652895420118173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32193299433741054453648461 12072487287652895420118173)
          ·
            refine ⟨4527182732869835782544315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12072487287652895420118173 4527182732869835782544315)
            ·
              refine ⟨6790774099304753673816473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4527182732869835782544315 6790774099304753673816473)
              ·
                refine ⟨5093080574478565255362355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6790774099304753673816473 5093080574478565255362355)
                ·
                  refine ⟨7639620861717847883043533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093080574478565255362355 7639620861717847883043533)
                  ·
                    refine ⟨2864857823144192956141325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7639620861717847883043533 2864857823144192956141325)
                    ·
                      refine ⟨1074321683679072358552997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2864857823144192956141325 1074321683679072358552997)
                      ·
                        rfl

theorem cell23_2092234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_2092234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092234 prefixEnd_2092234 := by exact prefixLift 2092234
  have htrace : WordTrace (prefixWord ++ tailWord_2092234) baseStart_2092234 baseEnd_2092234 := by
    simpa [prefixWord, tailWord_2092234, baseEnd_2092234] using wordTrace_append hprefix tailTrace_2092234
  have hstable : (prefixWord ++ tailWord_2092234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092234).length < 2 ^ (prefixWord ++ tailWord_2092234).sum := by decide
  have hdescent : baseEnd_2092234 < baseStart_2092234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092238 : List Nat := [4, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3]
def baseStart_2092238 : Nat := 118140960795 + 2092238 * 2 ^ 59
def prefixEnd_2092238 : Nat := 4983230072969 + 3 ^ 40 * 2092238 * 2
def baseEnd_2092238 : Nat := 1074323737601690342902979

theorem tailTrace_2092238 : CollatzResearch.WordTrace tailWord_2092238 prefixEnd_2092238 1074323737601690342902979 := by
  unfold tailWord_2092238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9538773624273315830918671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50873459329457684431566245 9538773624273315830918671)
  ·
    refine ⟨14308160436409973746378007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9538773624273315830918671 14308160436409973746378007)
    ·
      refine ⟨21462240654614960619567011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14308160436409973746378007 21462240654614960619567011)
      ·
        refine ⟨32193360981922440929350517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21462240654614960619567011 32193360981922440929350517)
        ·
          refine ⟨3018127592055228837126611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32193360981922440929350517 3018127592055228837126611)
          ·
            refine ⟨4527191388082843255689917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018127592055228837126611 4527191388082843255689917)
            ·
              refine ⟨1697696770531066220883719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4527191388082843255689917 1697696770531066220883719)
              ·
                refine ⟨2546545155796599331325579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697696770531066220883719 2546545155796599331325579)
                ·
                  refine ⟨3819817733694898996988369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546545155796599331325579 3819817733694898996988369)
                  ·
                    refine ⟨2864863300271174247741277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3819817733694898996988369 2864863300271174247741277)
                    ·
                      refine ⟨1074323737601690342902979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2864863300271174247741277 1074323737601690342902979)
                      ·
                        rfl

theorem cell23_2092238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_2092238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092238 prefixEnd_2092238 := by exact prefixLift 2092238
  have htrace : WordTrace (prefixWord ++ tailWord_2092238) baseStart_2092238 baseEnd_2092238 := by
    simpa [prefixWord, tailWord_2092238, baseEnd_2092238] using wordTrace_append hprefix tailTrace_2092238
  have hstable : (prefixWord ++ tailWord_2092238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092238).length < 2 ^ (prefixWord ++ tailWord_2092238).sum := by decide
  have hdescent : baseEnd_2092238 < baseStart_2092238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092257 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_2092257 : Nat := 118140960795 + 2092257 * 2 ^ 59
def prefixEnd_2092257 : Nat := 4983230072969 + 3 ^ 40 * 2092257 * 2
def baseEnd_2092257 : Nat := 1074333493734125768565391

theorem tailTrace_2092257 : CollatzResearch.WordTrace tailWord_2092257 prefixEnd_2092257 1074333493734125768565391 := by
  unfold tailWord_2092257
  simp only [CollatzResearch.WordTrace]
  refine ⟨76310881981117692892291025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50873921320745128594860683 76310881981117692892291025)
  ·
    refine ⟨57233161485838269669218269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76310881981117692892291025 57233161485838269669218269)
    ·
      refine ⟨21462435557189351125956851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57233161485838269669218269 21462435557189351125956851)
      ·
        refine ⟨32193653335784026688935277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21462435557189351125956851 32193653335784026688935277)
        ·
          refine ⟨12072620000919010008350729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32193653335784026688935277 12072620000919010008350729)
          ·
            refine ⟨9054465000689257506263047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12072620000919010008350729 9054465000689257506263047)
            ·
              refine ⟨13581697501033886259394571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9054465000689257506263047 13581697501033886259394571)
              ·
                refine ⟨20372546251550829389091857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13581697501033886259394571 20372546251550829389091857)
                ·
                  refine ⟨15279409688663122041818893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20372546251550829389091857 15279409688663122041818893)
                  ·
                    refine ⟨5729778633248670765682085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15279409688663122041818893 5729778633248670765682085)
                    ·
                      refine ⟨1074333493734125768565391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5729778633248670765682085 1074333493734125768565391)
                      ·
                        rfl

theorem cell23_2092257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_2092257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092257 prefixEnd_2092257 := by exact prefixLift 2092257
  have htrace : WordTrace (prefixWord ++ tailWord_2092257) baseStart_2092257 baseEnd_2092257 := by
    simpa [prefixWord, tailWord_2092257, baseEnd_2092257] using wordTrace_append hprefix tailTrace_2092257
  have hstable : (prefixWord ++ tailWord_2092257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092257).length < 2 ^ (prefixWord ++ tailWord_2092257).sum := by decide
  have hdescent : baseEnd_2092257 < baseStart_2092257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092267 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 2, 6]
def baseStart_2092267 : Nat := 118140960795 + 2092267 * 2 ^ 59
def prefixEnd_2092267 : Nat := 4983230072969 + 3 ^ 40 * 2092267 * 2
def baseEnd_2092267 : Nat := 358112876180223576480115

theorem tailTrace_2092267 : CollatzResearch.WordTrace tailWord_2092267 prefixEnd_2092267 358112876180223576480115 := by
  unfold tailWord_2092267
  simp only [CollatzResearch.WordTrace]
  refine ⟨76311246711081464600155055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50874164474054309733436703 76311246711081464600155055)
  ·
    refine ⟨114466870066622196900232583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76311246711081464600155055 114466870066622196900232583)
    ·
      refine ⟨171700305099933295350348875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114466870066622196900232583 171700305099933295350348875)
      ·
        refine ⟨257550457649899943025523313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171700305099933295350348875 257550457649899943025523313)
        ·
          refine ⟨193162843237424957269142485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257550457649899943025523313 193162843237424957269142485)
          ·
            refine ⟨4527254138377147435995527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 193162843237424957269142485 4527254138377147435995527)
            ·
              refine ⟨6790881207565721153993291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4527254138377147435995527 6790881207565721153993291)
              ·
                refine ⟨10186321811348581730989937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6790881207565721153993291 10186321811348581730989937)
                ·
                  refine ⟨7639741358511436298242453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10186321811348581730989937 7639741358511436298242453)
                  ·
                    refine ⟨358112876180223576480115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7639741358511436298242453 358112876180223576480115)
                    ·
                      rfl

theorem cell23_2092267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 6].length) (baseStart_2092267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092267 prefixEnd_2092267 := by exact prefixLift 2092267
  have htrace : WordTrace (prefixWord ++ tailWord_2092267) baseStart_2092267 baseEnd_2092267 := by
    simpa [prefixWord, tailWord_2092267, baseEnd_2092267] using wordTrace_append hprefix tailTrace_2092267
  have hstable : (prefixWord ++ tailWord_2092267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092267).length < 2 ^ (prefixWord ++ tailWord_2092267).sum := by decide
  have hdescent : baseEnd_2092267 < baseStart_2092267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092314 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 7]
def baseStart_2092314 : Nat := 118140960795 + 2092314 * 2 ^ 59
def prefixEnd_2092314 : Nat := 4983230072969 + 3 ^ 40 * 2092314 * 2
def baseEnd_2092314 : Nat := 119373640236825782839181

theorem tailTrace_2092314 : CollatzResearch.WordTrace tailWord_2092314 prefixEnd_2092314 119373640236825782839181 := by
  unfold tailWord_2092314
  simp only [CollatzResearch.WordTrace]
  refine ⟨19078240235477797906778999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50875307294607461084743997 19078240235477797906778999)
  ·
    refine ⟨28617360353216696860168499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19078240235477797906778999 28617360353216696860168499)
    ·
      refine ⟨42926040529825045290252749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28617360353216696860168499 42926040529825045290252749)
      ·
        refine ⟨16097265198684391983844781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42926040529825045290252749 16097265198684391983844781)
        ·
          refine ⟨6036474449506646993941793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16097265198684391983844781 6036474449506646993941793)
          ·
            refine ⟨4527355837129985245456345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6036474449506646993941793 4527355837129985245456345)
            ·
              refine ⟨3395516877847488934092259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4527355837129985245456345 3395516877847488934092259)
              ·
                refine ⟨5093275316771233401138389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395516877847488934092259 5093275316771233401138389)
                ·
                  refine ⟨119373640236825782839181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5093275316771233401138389 119373640236825782839181)
                  ·
                    rfl

theorem cell23_2092314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 7].length) (baseStart_2092314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092314 prefixEnd_2092314 := by exact prefixLift 2092314
  have htrace : WordTrace (prefixWord ++ tailWord_2092314) baseStart_2092314 baseEnd_2092314 := by
    simpa [prefixWord, tailWord_2092314, baseEnd_2092314] using wordTrace_append hprefix tailTrace_2092314
  have hstable : (prefixWord ++ tailWord_2092314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092314).length < 2 ^ (prefixWord ++ tailWord_2092314).sum := by decide
  have hdescent : baseEnd_2092314 < baseStart_2092314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092324 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_2092324 : Nat := 118140960795 + 2092324 * 2 ^ 59
def prefixEnd_2092324 : Nat := 4983230072969 + 3 ^ 40 * 2092324 * 2
def baseEnd_2092324 : Nat := 1074367896937977006427583

theorem tailTrace_2092324 : CollatzResearch.WordTrace tailWord_2092324 prefixEnd_2092324 1074367896937977006427583 := by
  unfold tailWord_2092324
  simp only [CollatzResearch.WordTrace]
  refine ⟨38156662835937481667490013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50875550447916642223320017 38156662835937481667490013)
  ·
    refine ⟨14308748563476555625308755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38156662835937481667490013 14308748563476555625308755)
    ·
      refine ⟨21463122845214833437963133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14308748563476555625308755 21463122845214833437963133)
      ·
        refine ⟨8048671066955562539236175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21463122845214833437963133 8048671066955562539236175)
        ·
          refine ⟨12073006600433343808854263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8048671066955562539236175 12073006600433343808854263)
          ·
            refine ⟨18109509900650015713281395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12073006600433343808854263 18109509900650015713281395)
            ·
              refine ⟨27164264850975023569922093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18109509900650015713281395 27164264850975023569922093)
              ·
                refine ⟨10186599319115633838720785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27164264850975023569922093 10186599319115633838720785)
                ·
                  refine ⟨7639949489336725379040589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10186599319115633838720785 7639949489336725379040589)
                  ·
                    refine ⟨2864981058501272017140221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7639949489336725379040589 2864981058501272017140221)
                    ·
                      refine ⟨1074367896937977006427583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2864981058501272017140221 1074367896937977006427583)
                      ·
                        rfl

theorem cell23_2092324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_2092324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092324 prefixEnd_2092324 := by exact prefixLift 2092324
  have htrace : WordTrace (prefixWord ++ tailWord_2092324) baseStart_2092324 baseEnd_2092324 := by
    simpa [prefixWord, tailWord_2092324, baseEnd_2092324] using wordTrace_append hprefix tailTrace_2092324
  have hstable : (prefixWord ++ tailWord_2092324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092324).length < 2 ^ (prefixWord ++ tailWord_2092324).sum := by decide
  have hdescent : baseEnd_2092324 < baseStart_2092324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092325 : List Nat := [1, 3, 1, 2, 4, 2, 3, 1, 2, 2, 2]
def baseStart_2092325 : Nat := 118140960795 + 2092325 * 2 ^ 59
def prefixEnd_2092325 : Nat := 4983230072969 + 3 ^ 40 * 2092325 * 2
def baseEnd_2092325 : Nat := 1074368410418631502515079

theorem tailTrace_2092325 : CollatzResearch.WordTrace tailWord_2092325 prefixEnd_2092325 1074368410418631502515079 := by
  unfold tailWord_2092325
  simp only [CollatzResearch.WordTrace]
  refine ⟨76313362144871340505766429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50875574763247560337177619 76313362144871340505766429)
  ·
    refine ⟨28617510804326752689662411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76313362144871340505766429 28617510804326752689662411)
    ·
      refine ⟨42926266206490129034493617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28617510804326752689662411 42926266206490129034493617)
      ·
        refine ⟨32194699654867596775870213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42926266206490129034493617 32194699654867596775870213)
        ·
          refine ⟨6036506185287674395475665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32194699654867596775870213 6036506185287674395475665)
          ·
            refine ⟨4527379638965755796606749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6036506185287674395475665 4527379638965755796606749)
            ·
              refine ⟨1697767364612158423727531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4527379638965755796606749 1697767364612158423727531)
              ·
                refine ⟨2546651046918237635591297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697767364612158423727531 2546651046918237635591297)
                ·
                  refine ⟨1909988285188678226693473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2546651046918237635591297 1909988285188678226693473)
                  ·
                    refine ⟨1432491213891508670020105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1909988285188678226693473 1432491213891508670020105)
                    ·
                      refine ⟨1074368410418631502515079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1432491213891508670020105 1074368410418631502515079)
                      ·
                        rfl

theorem cell23_2092325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_2092325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092325 prefixEnd_2092325 := by exact prefixLift 2092325
  have htrace : WordTrace (prefixWord ++ tailWord_2092325) baseStart_2092325 baseEnd_2092325 := by
    simpa [prefixWord, tailWord_2092325, baseEnd_2092325] using wordTrace_append hprefix tailTrace_2092325
  have hstable : (prefixWord ++ tailWord_2092325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092325).length < 2 ^ (prefixWord ++ tailWord_2092325).sum := by decide
  have hdescent : baseEnd_2092325 < baseStart_2092325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092364 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2092364 : Nat := 118140960795 + 2092364 * 2 ^ 59
def prefixEnd_2092364 : Nat := 4983230072969 + 3 ^ 40 * 2092364 * 2
def baseEnd_2092364 : Nat := 1074388436164156849927399

theorem tailTrace_2092364 : CollatzResearch.WordTrace tailWord_2092364 prefixEnd_2092364 1074388436164156849927399 := by
  unfold tailWord_2092364
  simp only [CollatzResearch.WordTrace]
  refine ⟨38157392295865025083218073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50876523061153366777624097 38157392295865025083218073)
  ·
    refine ⟨28618044221898768812413555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38157392295865025083218073 28618044221898768812413555)
    ·
      refine ⟨42927066332848153218620333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28618044221898768812413555 42927066332848153218620333)
      ·
        refine ⟨16097649874818057456982625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42927066332848153218620333 16097649874818057456982625)
        ·
          refine ⟨12073237406113543092736969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16097649874818057456982625 12073237406113543092736969)
          ·
            refine ⟨9054928054585157319552727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12073237406113543092736969 9054928054585157319552727)
            ·
              refine ⟨13582392081877735979329091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9054928054585157319552727 13582392081877735979329091)
              ·
                refine ⟨20373588122816603968993637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13582392081877735979329091 20373588122816603968993637)
                ·
                  refine ⟨3820047773028113244186307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20373588122816603968993637 3820047773028113244186307)
                  ·
                    refine ⟨5730071659542169866279461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3820047773028113244186307 5730071659542169866279461)
                    ·
                      refine ⟨1074388436164156849927399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5730071659542169866279461 1074388436164156849927399)
                      ·
                        rfl

theorem cell23_2092364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2092364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092364 prefixEnd_2092364 := by exact prefixLift 2092364
  have htrace : WordTrace (prefixWord ++ tailWord_2092364) baseStart_2092364 baseEnd_2092364 := by
    simpa [prefixWord, tailWord_2092364, baseEnd_2092364] using wordTrace_append hprefix tailTrace_2092364
  have hstable : (prefixWord ++ tailWord_2092364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092364).length < 2 ^ (prefixWord ++ tailWord_2092364).sum := by decide
  have hdescent : baseEnd_2092364 < baseStart_2092364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092365 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 7]
def baseStart_2092365 : Nat := 118140960795 + 2092365 * 2 ^ 59
def prefixEnd_2092365 : Nat := 4983230072969 + 3 ^ 40 * 2092365 * 2
def baseEnd_2092365 : Nat := 119376549960534594001655

theorem tailTrace_2092365 : CollatzResearch.WordTrace tailWord_2092365 prefixEnd_2092365 119376549960534594001655 := by
  unfold tailWord_2092365
  simp only [CollatzResearch.WordTrace]
  refine ⟨76314821064726427337222549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50876547376484284891481699 76314821064726427337222549)
  ·
    refine ⟨3577257237409051281432307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76314821064726427337222549 3577257237409051281432307)
    ·
      refine ⟨5365885856113576922148461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3577257237409051281432307 5365885856113576922148461)
      ·
        refine ⟨2012207196042591345805673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5365885856113576922148461 2012207196042591345805673)
        ·
          refine ⟨1509155397031943509354255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2012207196042591345805673 1509155397031943509354255)
          ·
            refine ⟨2263733095547915264031383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509155397031943509354255 2263733095547915264031383)
            ·
              refine ⟨3395599643321872896047075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2263733095547915264031383 3395599643321872896047075)
              ·
                refine ⟨5093399464982809344070613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395599643321872896047075 5093399464982809344070613)
                ·
                  refine ⟨119376549960534594001655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5093399464982809344070613 119376549960534594001655)
                  ·
                    rfl

theorem cell23_2092365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_2092365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092365 prefixEnd_2092365 := by exact prefixLift 2092365
  have htrace : WordTrace (prefixWord ++ tailWord_2092365) baseStart_2092365 baseEnd_2092365 := by
    simpa [prefixWord, tailWord_2092365, baseEnd_2092365] using wordTrace_append hprefix tailTrace_2092365
  have hstable : (prefixWord ++ tailWord_2092365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092365).length < 2 ^ (prefixWord ++ tailWord_2092365).sum := by decide
  have hdescent : baseEnd_2092365 < baseStart_2092365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092377 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 6]
def baseStart_2092377 : Nat := 118140960795 + 2092377 * 2 ^ 59
def prefixEnd_2092377 : Nat := 4983230072969 + 3 ^ 40 * 2092377 * 2
def baseEnd_2092377 : Nat := 1074395111412665299064839

theorem tailTrace_2092377 : CollatzResearch.WordTrace tailWord_2092377 prefixEnd_2092377 1074395111412665299064839 := by
  unfold tailWord_2092377
  simp only [CollatzResearch.WordTrace]
  refine ⟨76315258740682953386659385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50876839160455302257772923 76315258740682953386659385)
  ·
    refine ⟨57236444055512215039994539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76315258740682953386659385 57236444055512215039994539)
    ·
      refine ⟨85854666083268322559991809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57236444055512215039994539 85854666083268322559991809)
      ·
        refine ⟨64390999562451241919993857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85854666083268322559991809 64390999562451241919993857)
        ·
          refine ⟨48293249671838431439995393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64390999562451241919993857 48293249671838431439995393)
          ·
            refine ⟨36219937253878823579996545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48293249671838431439995393 36219937253878823579996545)
            ·
              refine ⟨27164952940409117684997409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36219937253878823579996545 27164952940409117684997409)
              ·
                refine ⟨20373714705306838263748057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27164952940409117684997409 20373714705306838263748057)
                ·
                  refine ⟨15280286028980128697811043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20373714705306838263748057 15280286028980128697811043)
                  ·
                    refine ⟨22920429043470193046716565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15280286028980128697811043 22920429043470193046716565)
                    ·
                      refine ⟨1074395111412665299064839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22920429043470193046716565 1074395111412665299064839)
                      ·
                        rfl

theorem cell23_2092377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_2092377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092377 prefixEnd_2092377 := by exact prefixLift 2092377
  have htrace : WordTrace (prefixWord ++ tailWord_2092377) baseStart_2092377 baseEnd_2092377 := by
    simpa [prefixWord, tailWord_2092377, baseEnd_2092377] using wordTrace_append hprefix tailTrace_2092377
  have hstable : (prefixWord ++ tailWord_2092377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092377).length < 2 ^ (prefixWord ++ tailWord_2092377).sum := by decide
  have hdescent : baseEnd_2092377 < baseStart_2092377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092465 : List Nat := [1, 2, 2, 4, 1, 1, 4, 3, 1, 1, 3]
def baseStart_2092465 : Nat := 118140960795 + 2092465 * 2 ^ 59
def prefixEnd_2092465 : Nat := 4983230072969 + 3 ^ 40 * 2092465 * 2
def baseEnd_2092465 : Nat := 1074440297710260954764435

theorem tailTrace_2092465 : CollatzResearch.WordTrace tailWord_2092465 prefixEnd_2092465 1074440297710260954764435 := by
  unfold tailWord_2092465
  simp only [CollatzResearch.WordTrace]
  refine ⟨76318468364364144415862849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50878978909576096277241899 76318468364364144415862849)
  ·
    refine ⟨57238851273273108311897137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76318468364364144415862849 57238851273273108311897137)
    ·
      refine ⟨42929138454954831233922853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57238851273273108311897137 42929138454954831233922853)
      ·
        refine ⟨8049213460304030856360535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42929138454954831233922853 8049213460304030856360535)
        ·
          refine ⟨12073820190456046284540803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8049213460304030856360535 12073820190456046284540803)
          ·
            refine ⟨18110730285684069426811205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12073820190456046284540803 18110730285684069426811205)
            ·
              refine ⟨3395761928565763017527101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18110730285684069426811205 3395761928565763017527101)
              ·
                refine ⟨1273410723212161131572663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3395761928565763017527101 1273410723212161131572663)
                ·
                  refine ⟨1910116084818241697358995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1273410723212161131572663 1910116084818241697358995)
                  ·
                    refine ⟨2865174127227362546038493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1910116084818241697358995 2865174127227362546038493)
                    ·
                      refine ⟨1074440297710260954764435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2865174127227362546038493 1074440297710260954764435)
                      ·
                        rfl

theorem cell23_2092465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_2092465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092465 prefixEnd_2092465 := by exact prefixLift 2092465
  have htrace : WordTrace (prefixWord ++ tailWord_2092465) baseStart_2092465 baseEnd_2092465 := by
    simpa [prefixWord, tailWord_2092465, baseEnd_2092465] using wordTrace_append hprefix tailTrace_2092465
  have hstable : (prefixWord ++ tailWord_2092465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092465).length < 2 ^ (prefixWord ++ tailWord_2092465).sum := by decide
  have hdescent : baseEnd_2092465 < baseStart_2092465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092471 : List Nat := [1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 4]
def baseStart_2092471 : Nat := 118140960795 + 2092471 * 2 ^ 59
def prefixEnd_2092471 : Nat := 4983230072969 + 3 ^ 40 * 2092471 * 2
def baseEnd_2092471 : Nat := 1074443378594187931289407

theorem tailTrace_2092471 : CollatzResearch.WordTrace tailWord_2092471 prefixEnd_2092471 1074443378594187931289407 := by
  unfold tailWord_2092471
  simp only [CollatzResearch.WordTrace]
  refine ⟨76318687202342407440581267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50879124801561604960387511 76318687202342407440581267)
  ·
    refine ⟨114478030803513611160871901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76318687202342407440581267 114478030803513611160871901)
    ·
      refine ⟨42929261551317604185326963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114478030803513611160871901 42929261551317604185326963)
      ·
        refine ⟨64393892326976406277990445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42929261551317604185326963 64393892326976406277990445)
        ·
          refine ⟨24147709622616152354246417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64393892326976406277990445 24147709622616152354246417)
          ·
            refine ⟨18110782216962114265684813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24147709622616152354246417 18110782216962114265684813)
            ·
              refine ⟨6791543331360792849631805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18110782216962114265684813 6791543331360792849631805)
              ·
                refine ⟨2546828749260297318611927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6791543331360792849631805 2546828749260297318611927)
                ·
                  refine ⟨3820243123890445977917891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546828749260297318611927 3820243123890445977917891)
                  ·
                    refine ⟨5730364685835668966876837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3820243123890445977917891 5730364685835668966876837)
                    ·
                      refine ⟨1074443378594187931289407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5730364685835668966876837 1074443378594187931289407)
                      ·
                        rfl

theorem cell23_2092471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_2092471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092471 prefixEnd_2092471 := by exact prefixLift 2092471
  have htrace : WordTrace (prefixWord ++ tailWord_2092471) baseStart_2092471 baseEnd_2092471 := by
    simpa [prefixWord, tailWord_2092471, baseEnd_2092471] using wordTrace_append hprefix tailTrace_2092471
  have hstable : (prefixWord ++ tailWord_2092471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092471).length < 2 ^ (prefixWord ++ tailWord_2092471).sum := by decide
  have hdescent : baseEnd_2092471 < baseStart_2092471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092538 : List Nat := [3, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3]
def baseStart_2092538 : Nat := 118140960795 + 2092538 * 2 ^ 59
def prefixEnd_2092538 : Nat := 4983230072969 + 3 ^ 40 * 2092538 * 2
def baseEnd_2092538 : Nat := 1074477781798039169151599

theorem tailTrace_2092538 : CollatzResearch.WordTrace tailWord_2092538 prefixEnd_2092538 1074477781798039169151599 := by
  unfold tailWord_2092538
  simp only [CollatzResearch.WordTrace]
  refine ⟨19080282723274919470817567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50880753928733118588846845 19080282723274919470817567)
  ·
    refine ⟨28620424084912379206226351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19080282723274919470817567 28620424084912379206226351)
    ·
      refine ⟨42930636127368568809339527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28620424084912379206226351 42930636127368568809339527)
      ·
        refine ⟨64395954191052853214009291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42930636127368568809339527 64395954191052853214009291)
        ·
          refine ⟨96593931286579279821013937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64395954191052853214009291 96593931286579279821013937)
          ·
            refine ⟨72445448464934459865760453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96593931286579279821013937 72445448464934459865760453)
            ·
              refine ⟨13583521587175211224830085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72445448464934459865760453 13583521587175211224830085)
              ·
                refine ⟨2546910297595352104655641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13583521587175211224830085 2546910297595352104655641)
                ·
                  refine ⟨1910182723196514078491731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2546910297595352104655641 1910182723196514078491731)
                  ·
                    refine ⟨2865274084794771117737597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1910182723196514078491731 2865274084794771117737597)
                    ·
                      refine ⟨1074477781798039169151599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2865274084794771117737597 1074477781798039169151599)
                      ·
                        rfl

theorem cell23_2092538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_2092538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092538 prefixEnd_2092538 := by exact prefixLift 2092538
  have htrace : WordTrace (prefixWord ++ tailWord_2092538) baseStart_2092538 baseEnd_2092538 := by
    simpa [prefixWord, tailWord_2092538, baseEnd_2092538] using wordTrace_append hprefix tailTrace_2092538
  have hstable : (prefixWord ++ tailWord_2092538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092538).length < 2 ^ (prefixWord ++ tailWord_2092538).sum := by decide
  have hdescent : baseEnd_2092538 < baseStart_2092538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092555 : List Nat := [1, 1, 1, 1, 8, 1, 1, 3, 2, 1, 3]
def baseStart_2092555 : Nat := 118140960795 + 2092555 * 2 ^ 59
def prefixEnd_2092555 : Nat := 4983230072969 + 3 ^ 40 * 2092555 * 2
def baseEnd_2092555 : Nat := 1074486510969165602639021

theorem tailTrace_2092555 : CollatzResearch.WordTrace tailWord_2092555 prefixEnd_2092555 1074486510969165602639021 := by
  unfold tailWord_2092555
  simp only [CollatzResearch.WordTrace]
  refine ⟨76321750934038089786639119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50881167289358726524426079 76321750934038089786639119)
  ·
    refine ⟨114482626401057134679958679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76321750934038089786639119 114482626401057134679958679)
    ·
      refine ⟨171723939601585702019938019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114482626401057134679958679 171723939601585702019938019)
      ·
        refine ⟨257585909402378553029907029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171723939601585702019938019 257585909402378553029907029)
        ·
          refine ⟨3018584875809123668319223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 257585909402378553029907029 3018584875809123668319223)
          ·
            refine ⟨4527877313713685502478835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018584875809123668319223 4527877313713685502478835)
            ·
              refine ⟨6791815970570528253718253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4527877313713685502478835 6791815970570528253718253)
              ·
                refine ⟨2546930988963948095144345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6791815970570528253718253 2546930988963948095144345)
                ·
                  refine ⟨1910198241722961071358259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2546930988963948095144345 1910198241722961071358259)
                  ·
                    refine ⟨2865297362584441607037389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1910198241722961071358259 2865297362584441607037389)
                    ·
                      refine ⟨1074486510969165602639021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2865297362584441607037389 1074486510969165602639021)
                      ·
                        rfl

theorem cell23_2092555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 1, 3].length) (baseStart_2092555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092555 prefixEnd_2092555 := by exact prefixLift 2092555
  have htrace : WordTrace (prefixWord ++ tailWord_2092555) baseStart_2092555 baseEnd_2092555 := by
    simpa [prefixWord, tailWord_2092555, baseEnd_2092555] using wordTrace_append hprefix tailTrace_2092555
  have hstable : (prefixWord ++ tailWord_2092555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092555).length < 2 ^ (prefixWord ++ tailWord_2092555).sum := by decide
  have hdescent : baseEnd_2092555 < baseStart_2092555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092565 : List Nat := [1, 3, 2, 1, 3, 2, 3, 2, 1, 3, 2]
def baseStart_2092565 : Nat := 118140960795 + 2092565 * 2 ^ 59
def prefixEnd_2092565 : Nat := 4983230072969 + 3 ^ 40 * 2092565 * 2
def baseEnd_2092565 : Nat := 1074491645775710563513975

theorem tailTrace_2092565 : CollatzResearch.WordTrace tailWord_2092565 prefixEnd_2092565 1074491645775710563513975 := by
  unfold tailWord_2092565
  simp only [CollatzResearch.WordTrace]
  refine ⟨76322115664001861494503149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50881410442667907663002099 76322115664001861494503149)
  ·
    refine ⟨28620793374000698060438681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76322115664001861494503149 28620793374000698060438681)
    ·
      refine ⟨21465595030500523545329011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28620793374000698060438681 21465595030500523545329011)
      ·
        refine ⟨32198392545750785317993517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21465595030500523545329011 32198392545750785317993517)
        ·
          refine ⟨12074397204656544494247569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32198392545750785317993517 12074397204656544494247569)
          ·
            refine ⟨9055797903492408370685677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12074397204656544494247569 9055797903492408370685677)
            ·
              refine ⟨3395924213809653139007129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9055797903492408370685677 3395924213809653139007129)
              ·
                refine ⟨2546943160357239854255347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395924213809653139007129 2546943160357239854255347)
                ·
                  refine ⟨3820414740535859781383021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546943160357239854255347 3820414740535859781383021)
                  ·
                    refine ⟨1432655527700947418018633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3820414740535859781383021 1432655527700947418018633)
                    ·
                      refine ⟨1074491645775710563513975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1432655527700947418018633 1074491645775710563513975)
                      ·
                        rfl

theorem cell23_2092565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_2092565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092565 prefixEnd_2092565 := by exact prefixLift 2092565
  have htrace : WordTrace (prefixWord ++ tailWord_2092565) baseStart_2092565 baseEnd_2092565 := by
    simpa [prefixWord, tailWord_2092565, baseEnd_2092565] using wordTrace_append hprefix tailTrace_2092565
  have hstable : (prefixWord ++ tailWord_2092565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092565).length < 2 ^ (prefixWord ++ tailWord_2092565).sum := by decide
  have hdescent : baseEnd_2092565 < baseStart_2092565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092578 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_2092578 : Nat := 118140960795 + 2092578 * 2 ^ 59
def prefixEnd_2092578 : Nat := 4983230072969 + 3 ^ 40 * 2092578 * 2
def baseEnd_2092578 : Nat := 1074498321024219012651415

theorem tailTrace_2092578 : CollatzResearch.WordTrace tailWord_2092578 prefixEnd_2092578 1074498321024219012651415 := by
  unfold tailWord_2092578
  simp only [CollatzResearch.WordTrace]
  refine ⟨19080647453238691178681597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50881726541969843143150925 19080647453238691178681597)
  ·
    refine ⟨7155242794964509192005599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19080647453238691178681597 7155242794964509192005599)
    ·
      refine ⟨10732864192446763788008399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7155242794964509192005599 10732864192446763788008399)
      ·
        refine ⟨16099296288670145682012599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10732864192446763788008399 16099296288670145682012599)
        ·
          refine ⟨24148944433005218523018899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16099296288670145682012599 24148944433005218523018899)
          ·
            refine ⟨36223416649507827784528349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24148944433005218523018899 36223416649507827784528349)
            ·
              refine ⟨13583781243565435419198131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36223416649507827784528349 13583781243565435419198131)
              ·
                refine ⟨20375671865348153128797197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13583781243565435419198131 20375671865348153128797197)
                ·
                  refine ⟨7640876949505557423298949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20375671865348153128797197 7640876949505557423298949)
                  ·
                    refine ⟨1432664428032292016868553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7640876949505557423298949 1432664428032292016868553)
                    ·
                      refine ⟨1074498321024219012651415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1432664428032292016868553 1074498321024219012651415)
                      ·
                        rfl

theorem cell23_2092578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_2092578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092578 prefixEnd_2092578 := by exact prefixLift 2092578
  have htrace : WordTrace (prefixWord ++ tailWord_2092578) baseStart_2092578 baseEnd_2092578 := by
    simpa [prefixWord, tailWord_2092578, baseEnd_2092578] using wordTrace_append hprefix tailTrace_2092578
  have hstable : (prefixWord ++ tailWord_2092578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092578).length < 2 ^ (prefixWord ++ tailWord_2092578).sum := by decide
  have hdescent : baseEnd_2092578 < baseStart_2092578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092595 : List Nat := [1, 1, 1, 2, 4, 3, 1, 4, 2, 2, 2]
def baseStart_2092595 : Nat := 118140960795 + 2092595 * 2 ^ 59
def prefixEnd_2092595 : Nat := 4983230072969 + 3 ^ 40 * 2092595 * 2
def baseEnd_2092595 : Nat := 1074507050195345446138837

theorem tailTrace_2092595 : CollatzResearch.WordTrace tailWord_2092595 prefixEnd_2092595 1074507050195345446138837 := by
  unfold tailWord_2092595
  simp only [CollatzResearch.WordTrace]
  refine ⟨76323209853893176618095239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50882139902595451078730159 76323209853893176618095239)
  ·
    refine ⟨114484814780839764927142859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76323209853893176618095239 114484814780839764927142859)
    ·
      refine ⟨171727222171259647390714289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114484814780839764927142859 171727222171259647390714289)
      ·
        refine ⟨128795416628444735543035717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171727222171259647390714289 128795416628444735543035717)
        ·
          refine ⟨24149140617833387914319197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128795416628444735543035717 24149140617833387914319197)
          ·
            refine ⟨9055927731687520467869699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24149140617833387914319197 9055927731687520467869699)
            ·
              refine ⟨13583891597531280701804549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9055927731687520467869699 13583891597531280701804549)
              ·
                refine ⟨2546979674537115131588353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13583891597531280701804549 2546979674537115131588353)
                ·
                  refine ⟨1910234755902836348691265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2546979674537115131588353 1910234755902836348691265)
                  ·
                    refine ⟨1432676066927127261518449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1910234755902836348691265 1432676066927127261518449)
                    ·
                      refine ⟨1074507050195345446138837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1432676066927127261518449 1074507050195345446138837)
                      ·
                        rfl

theorem cell23_2092595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 2, 2].length) (baseStart_2092595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092595 prefixEnd_2092595 := by exact prefixLift 2092595
  have htrace : WordTrace (prefixWord ++ tailWord_2092595) baseStart_2092595 baseEnd_2092595 := by
    simpa [prefixWord, tailWord_2092595, baseEnd_2092595] using wordTrace_append hprefix tailTrace_2092595
  have hstable : (prefixWord ++ tailWord_2092595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092595).length < 2 ^ (prefixWord ++ tailWord_2092595).sum := by decide
  have hdescent : baseEnd_2092595 < baseStart_2092595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092631 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 1, 7]
def baseStart_2092631 : Nat := 118140960795 + 2092631 * 2 ^ 59
def prefixEnd_2092631 : Nat := 4983230072969 + 3 ^ 40 * 2092631 * 2
def baseEnd_2092631 : Nat := 358175178499635768429557

theorem tailTrace_2092631 : CollatzResearch.WordTrace tailWord_2092631 prefixEnd_2092631 358175178499635768429557 := by
  unfold tailWord_2092631
  simp only [CollatzResearch.WordTrace]
  refine ⟨76324522881762754766405747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50883015254508503177603831 76324522881762754766405747)
  ·
    refine ⟨114486784322644132149608621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76324522881762754766405747 114486784322644132149608621)
    ·
      refine ⟨42932544120991549556103233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114486784322644132149608621 42932544120991549556103233)
      ·
        refine ⟨32199408090743662167077425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42932544120991549556103233 32199408090743662167077425)
        ·
          refine ⟨24149556068057746625308069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32199408090743662167077425 24149556068057746625308069)
          ·
            refine ⟨4528041762760827492245263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24149556068057746625308069 4528041762760827492245263)
            ·
              refine ⟨6792062644141241238367895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528041762760827492245263 6792062644141241238367895)
              ·
                refine ⟨10188093966211861857551843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792062644141241238367895 10188093966211861857551843)
                ·
                  refine ⟨15282140949317792786327765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10188093966211861857551843 15282140949317792786327765)
                  ·
                    refine ⟨358175178499635768429557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15282140949317792786327765 358175178499635768429557)
                    ·
                      rfl

theorem cell23_2092631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_2092631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092631 prefixEnd_2092631 := by exact prefixLift 2092631
  have htrace : WordTrace (prefixWord ++ tailWord_2092631) baseStart_2092631 baseEnd_2092631 := by
    simpa [prefixWord, tailWord_2092631, baseEnd_2092631] using wordTrace_append hprefix tailTrace_2092631
  have hstable : (prefixWord ++ tailWord_2092631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092631).length < 2 ^ (prefixWord ++ tailWord_2092631).sum := by decide
  have hdescent : baseEnd_2092631 < baseStart_2092631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092705 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_2092705 : Nat := 118140960795 + 2092705 * 2 ^ 59
def prefixEnd_2092705 : Nat := 4983230072969 + 3 ^ 40 * 2092705 * 2
def baseEnd_2092705 : Nat := 1074563533067340015763331

theorem tailTrace_2092705 : CollatzResearch.WordTrace tailWord_2092705 prefixEnd_2092705 1074563533067340015763331 := by
  unfold tailWord_2092705
  simp only [CollatzResearch.WordTrace]
  refine ⟨76327221883494665404599569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50884814588996443603066379 76327221883494665404599569)
  ·
    refine ⟨57245416412620999053449677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76327221883494665404599569 57245416412620999053449677)
    ·
      refine ⟨21467031154732874645043629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57245416412620999053449677 21467031154732874645043629)
      ·
        refine ⟨8050136683024827991891361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21467031154732874645043629 8050136683024827991891361)
        ·
          refine ⟨6037602512268620993918521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8050136683024827991891361 6037602512268620993918521)
          ·
            refine ⟨4528201884201465745438891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6037602512268620993918521 4528201884201465745438891)
            ·
              refine ⟨6792302826302198618158337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528201884201465745438891 6792302826302198618158337)
              ·
                refine ⟨5094227119726648963618753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6792302826302198618158337 5094227119726648963618753)
                ·
                  refine ⟨3820670339794986722714065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5094227119726648963618753 3820670339794986722714065)
                  ·
                    refine ⟨2865502754846240042035549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3820670339794986722714065 2865502754846240042035549)
                    ·
                      refine ⟨1074563533067340015763331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2865502754846240042035549 1074563533067340015763331)
                      ·
                        rfl

theorem cell23_2092705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_2092705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092705 prefixEnd_2092705 := by exact prefixLift 2092705
  have htrace : WordTrace (prefixWord ++ tailWord_2092705) baseStart_2092705 baseEnd_2092705 := by
    simpa [prefixWord, tailWord_2092705, baseEnd_2092705] using wordTrace_append hprefix tailTrace_2092705
  have hstable : (prefixWord ++ tailWord_2092705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092705).length < 2 ^ (prefixWord ++ tailWord_2092705).sum := by decide
  have hdescent : baseEnd_2092705 < baseStart_2092705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092725 : List Nat := [1, 3, 3, 3, 2, 1, 1, 3, 6]
def baseStart_2092725 : Nat := 118140960795 + 2092725 * 2 ^ 59
def prefixEnd_2092725 : Nat := 4983230072969 + 3 ^ 40 * 2092725 * 2
def baseEnd_2092725 : Nat := 119397089186714437501471

theorem tailTrace_2092725 : CollatzResearch.WordTrace tailWord_2092725 prefixEnd_2092725 119397089186714437501471 := by
  unfold tailWord_2092725
  simp only [CollatzResearch.WordTrace]
  refine ⟨76327951343422208820327629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50885300895614805880218419 76327951343422208820327629)
  ·
    refine ⟨28622981753783328307622861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76327951343422208820327629 28622981753783328307622861)
    ·
      refine ⟨10733618157668748115358573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28622981753783328307622861 10733618157668748115358573)
      ·
        refine ⟨4025106809125780543259465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10733618157668748115358573 4025106809125780543259465)
        ·
          refine ⟨3018830106844335407444599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4025106809125780543259465 3018830106844335407444599)
          ·
            refine ⟨4528245160266503111166899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018830106844335407444599 4528245160266503111166899)
            ·
              refine ⟨6792367740399754666750349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528245160266503111166899 6792367740399754666750349)
              ·
                refine ⟨2547137902649908000031381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6792367740399754666750349 2547137902649908000031381)
                ·
                  refine ⟨119397089186714437501471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2547137902649908000031381 119397089186714437501471)
                  ·
                    rfl

theorem cell23_2092725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 6].length) (baseStart_2092725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092725 prefixEnd_2092725 := by exact prefixLift 2092725
  have htrace : WordTrace (prefixWord ++ tailWord_2092725) baseStart_2092725 baseEnd_2092725 := by
    simpa [prefixWord, tailWord_2092725, baseEnd_2092725] using wordTrace_append hprefix tailTrace_2092725
  have hstable : (prefixWord ++ tailWord_2092725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092725).length < 2 ^ (prefixWord ++ tailWord_2092725).sum := by decide
  have hdescent : baseEnd_2092725 < baseStart_2092725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092728 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 3, 5, 2]
def baseStart_2092728 : Nat := 118140960795 + 2092728 * 2 ^ 59
def prefixEnd_2092728 : Nat := 4983230072969 + 3 ^ 40 * 2092728 * 2
def baseEnd_2092728 : Nat := 1074575343122393425775725

theorem tailTrace_2092728 : CollatzResearch.WordTrace tailWord_2092728 prefixEnd_2092728 1074575343122393425775725 := by
  unfold tailWord_2092728
  simp only [CollatzResearch.WordTrace]
  refine ⟨38164030381205670166343419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50885373841607560221791225 38164030381205670166343419)
  ·
    refine ⟨57246045571808505249515129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38164030381205670166343419 57246045571808505249515129)
    ·
      refine ⟨42934534178856378937136347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57246045571808505249515129 42934534178856378937136347)
      ·
        refine ⟨64401801268284568405704521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42934534178856378937136347 64401801268284568405704521)
        ·
          refine ⟨48301350951213426304278391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64401801268284568405704521 48301350951213426304278391)
          ·
            refine ⟨72452026426820139456417587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48301350951213426304278391 72452026426820139456417587)
            ·
              refine ⟨108678039640230209184626381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72452026426820139456417587 108678039640230209184626381)
              ·
                refine ⟨40754264865086328444234893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108678039640230209184626381 40754264865086328444234893)
                ·
                  refine ⟨15282849324407373166588085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40754264865086328444234893 15282849324407373166588085)
                  ·
                    refine ⟨1432767124163191234367633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15282849324407373166588085 1432767124163191234367633)
                    ·
                      refine ⟨1074575343122393425775725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1432767124163191234367633 1074575343122393425775725)
                      ·
                        rfl

theorem cell23_2092728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 5, 2].length) (baseStart_2092728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092728 prefixEnd_2092728 := by exact prefixLift 2092728
  have htrace : WordTrace (prefixWord ++ tailWord_2092728) baseStart_2092728 baseEnd_2092728 := by
    simpa [prefixWord, tailWord_2092728, baseEnd_2092728] using wordTrace_append hprefix tailTrace_2092728
  have hstable : (prefixWord ++ tailWord_2092728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092728).length < 2 ^ (prefixWord ++ tailWord_2092728).sum := by decide
  have hdescent : baseEnd_2092728 < baseStart_2092728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092741 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_2092741 : Nat := 118140960795 + 2092741 * 2 ^ 59
def prefixEnd_2092741 : Nat := 4983230072969 + 3 ^ 40 * 2092741 * 2
def baseEnd_2092741 : Nat := 1074582018370901874913165

theorem tailTrace_2092741 : CollatzResearch.WordTrace tailWord_2092741 prefixEnd_2092741 1074582018370901874913165 := by
  unfold tailWord_2092741
  simp only [CollatzResearch.WordTrace]
  refine ⟨76328534911364243552910077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50885689940909495701940051 76328534911364243552910077)
  ·
    refine ⟨28623200591761591332341279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76328534911364243552910077 28623200591761591332341279)
    ·
      refine ⟨42934800887642386998511919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28623200591761591332341279 42934800887642386998511919)
      ·
        refine ⟨64402201331463580497767879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42934800887642386998511919 64402201331463580497767879)
        ·
          refine ⟨96603301997195370746651819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64402201331463580497767879 96603301997195370746651819)
          ·
            refine ⟨144904952995793056119977729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96603301997195370746651819 144904952995793056119977729)
            ·
              refine ⟨108678714746844792089983297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144904952995793056119977729 108678714746844792089983297)
              ·
                refine ⟨81509036060133594067487473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108678714746844792089983297 81509036060133594067487473)
                ·
                  refine ⟨61131777045100195550615605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81509036060133594067487473 61131777045100195550615605)
                  ·
                    refine ⟨5731104097978143332870213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61131777045100195550615605 5731104097978143332870213)
                    ·
                      refine ⟨1074582018370901874913165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5731104097978143332870213 1074582018370901874913165)
                      ·
                        rfl

theorem cell23_2092741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_2092741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092741 prefixEnd_2092741 := by exact prefixLift 2092741
  have htrace : WordTrace (prefixWord ++ tailWord_2092741) baseStart_2092741 baseEnd_2092741 := by
    simpa [prefixWord, tailWord_2092741, baseEnd_2092741] using wordTrace_append hprefix tailTrace_2092741
  have hstable : (prefixWord ++ tailWord_2092741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092741).length < 2 ^ (prefixWord ++ tailWord_2092741).sum := by decide
  have hdescent : baseEnd_2092741 < baseStart_2092741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092768 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 4, 4]
def baseStart_2092768 : Nat := 118140960795 + 2092768 * 2 ^ 59
def prefixEnd_2092768 : Nat := 4983230072969 + 3 ^ 40 * 2092768 * 2
def baseEnd_2092768 : Nat := 358198627449524423091847

theorem tailTrace_2092768 : CollatzResearch.WordTrace tailWord_2092768 prefixEnd_2092768 358198627449524423091847 := by
  unfold tailWord_2092768
  simp only [CollatzResearch.WordTrace]
  refine ⟨38164759841133213582071479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50886346454844284776095305 38164759841133213582071479)
  ·
    refine ⟨57247139761699820373107219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38164759841133213582071479 57247139761699820373107219)
    ·
      refine ⟨85870709642549730559660829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57247139761699820373107219 85870709642549730559660829)
      ·
        refine ⟨32201516115956148959872811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85870709642549730559660829 32201516115956148959872811)
        ·
          refine ⟨48302274173934223439809217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32201516115956148959872811 48302274173934223439809217)
          ·
            refine ⟨36226705630450667579856913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48302274173934223439809217 36226705630450667579856913)
            ·
              refine ⟨27170029222838000684892685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36226705630450667579856913 27170029222838000684892685)
              ·
                refine ⟨10188760958564250256834757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27170029222838000684892685 10188760958564250256834757)
                ·
                  refine ⟨1910392679730796923156517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10188760958564250256834757 1910392679730796923156517)
                  ·
                    refine ⟨358198627449524423091847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1910392679730796923156517 358198627449524423091847)
                    ·
                      rfl

theorem cell23_2092768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 4, 4].length) (baseStart_2092768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092768 prefixEnd_2092768 := by exact prefixLift 2092768
  have htrace : WordTrace (prefixWord ++ tailWord_2092768) baseStart_2092768 baseEnd_2092768 := by
    simpa [prefixWord, tailWord_2092768, baseEnd_2092768] using wordTrace_append hprefix tailTrace_2092768
  have hstable : (prefixWord ++ tailWord_2092768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092768).length < 2 ^ (prefixWord ++ tailWord_2092768).sum := by decide
  have hdescent : baseEnd_2092768 < baseStart_2092768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092769 : List Nat := [1, 2, 3, 1, 5, 1, 1, 4, 1, 1, 3]
def baseStart_2092769 : Nat := 118140960795 + 2092769 * 2 ^ 59
def prefixEnd_2092769 : Nat := 4983230072969 + 3 ^ 40 * 2092769 * 2
def baseEnd_2092769 : Nat := 1074596395829227765363037

theorem tailTrace_2092769 : CollatzResearch.WordTrace tailWord_2092769 prefixEnd_2092769 1074596395829227765363037 := by
  unfold tailWord_2092769
  simp only [CollatzResearch.WordTrace]
  refine ⟨76329556155262804334929361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50886370770175202889952907 76329556155262804334929361)
  ·
    refine ⟨57247167116447103251197021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76329556155262804334929361 57247167116447103251197021)
    ·
      refine ⟨21467687668667663719198883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57247167116447103251197021 21467687668667663719198883)
      ·
        refine ⟨32201531503001495578798325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21467687668667663719198883 32201531503001495578798325)
        ·
          refine ⟨3018893578406390210512343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32201531503001495578798325 3018893578406390210512343)
          ·
            refine ⟨4528340367609585315768515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018893578406390210512343 4528340367609585315768515)
            ·
              refine ⟨6792510551414377973652773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528340367609585315768515 6792510551414377973652773)
              ·
                refine ⟨1273595728390195870059895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6792510551414377973652773 1273595728390195870059895)
                ·
                  refine ⟨1910393592585293805089843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1273595728390195870059895 1910393592585293805089843)
                  ·
                    refine ⟨2865590388877940707634765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1910393592585293805089843 2865590388877940707634765)
                    ·
                      refine ⟨1074596395829227765363037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2865590388877940707634765 1074596395829227765363037)
                      ·
                        rfl

theorem cell23_2092769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_2092769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092769 prefixEnd_2092769 := by exact prefixLift 2092769
  have htrace : WordTrace (prefixWord ++ tailWord_2092769) baseStart_2092769 baseEnd_2092769 := by
    simpa [prefixWord, tailWord_2092769, baseEnd_2092769] using wordTrace_append hprefix tailTrace_2092769
  have hstable : (prefixWord ++ tailWord_2092769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092769).length < 2 ^ (prefixWord ++ tailWord_2092769).sum := by decide
  have hdescent : baseEnd_2092769 < baseStart_2092769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092778 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_2092778 : Nat := 118140960795 + 2092778 * 2 ^ 59
def prefixEnd_2092778 : Nat := 4983230072969 + 3 ^ 40 * 2092778 * 2
def baseEnd_2092778 : Nat := 1074601017155118230150495

theorem tailTrace_2092778 : CollatzResearch.WordTrace tailWord_2092778 prefixEnd_2092778 1074601017155118230150495 := by
  unfold tailWord_2092778
  simp only [CollatzResearch.WordTrace]
  refine ⟨19082471103057549718001747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50886589608153465914671325 19082471103057549718001747)
  ·
    refine ⟨28623706654586324577002621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19082471103057549718001747 28623706654586324577002621)
    ·
      refine ⟨10733889995469871716375983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28623706654586324577002621 10733889995469871716375983)
      ·
        refine ⟨16100834993204807574563975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10733889995469871716375983 16100834993204807574563975)
        ·
          refine ⟨24151252489807211361845963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16100834993204807574563975 24151252489807211361845963)
          ·
            refine ⟨36226878734710817042768945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24151252489807211361845963 36226878734710817042768945)
            ·
              refine ⟨27170159051033112782076709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36226878734710817042768945 27170159051033112782076709)
              ·
                refine ⟨5094404822068708646639383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27170159051033112782076709 5094404822068708646639383)
                ·
                  refine ⟨7641607233103062969959075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5094404822068708646639383 7641607233103062969959075)
                  ·
                    refine ⟨11462410849654594454938613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7641607233103062969959075 11462410849654594454938613)
                    ·
                      refine ⟨1074601017155118230150495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11462410849654594454938613 1074601017155118230150495)
                      ·
                        rfl

theorem cell23_2092778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_2092778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092778 prefixEnd_2092778 := by exact prefixLift 2092778
  have htrace : WordTrace (prefixWord ++ tailWord_2092778) baseStart_2092778 baseEnd_2092778 := by
    simpa [prefixWord, tailWord_2092778, baseEnd_2092778] using wordTrace_append hprefix tailTrace_2092778
  have hstable : (prefixWord ++ tailWord_2092778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092778).length < 2 ^ (prefixWord ++ tailWord_2092778).sum := by decide
  have hdescent : baseEnd_2092778 < baseStart_2092778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092785 : List Nat := [1, 2, 2, 2, 2, 3, 2, 3, 2, 4]
def baseStart_2092785 : Nat := 118140960795 + 2092785 * 2 ^ 59
def prefixEnd_2092785 : Nat := 4983230072969 + 3 ^ 40 * 2092785 * 2
def baseEnd_2092785 : Nat := 358201537173233234254321

theorem tailTrace_2092785 : CollatzResearch.WordTrace tailWord_2092785 prefixEnd_2092785 358201537173233234254321 := by
  unfold tailWord_2092785
  simp only [CollatzResearch.WordTrace]
  refine ⟨76330139723204839067511809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50886759815469892711674539 76330139723204839067511809)
  ·
    refine ⟨57247604792403629300633857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76330139723204839067511809 57247604792403629300633857)
    ·
      refine ⟨42935703594302721975475393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57247604792403629300633857 42935703594302721975475393)
      ·
        refine ⟨32201777695727041481606545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42935703594302721975475393 32201777695727041481606545)
        ·
          refine ⟨24151333271795281111204909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32201777695727041481606545 24151333271795281111204909)
          ·
            refine ⟨9056749976923230416701841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24151333271795281111204909 9056749976923230416701841)
            ·
              refine ⟨6792562482692422812526381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9056749976923230416701841 6792562482692422812526381)
              ·
                refine ⟨2547210931009658554697393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6792562482692422812526381 2547210931009658554697393)
                ·
                  refine ⟨1910408198257243916023045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2547210931009658554697393 1910408198257243916023045)
                  ·
                    refine ⟨358201537173233234254321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1910408198257243916023045 358201537173233234254321)
                    ·
                      rfl

theorem cell23_2092785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_2092785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092785 prefixEnd_2092785 := by exact prefixLift 2092785
  have htrace : WordTrace (prefixWord ++ tailWord_2092785) baseStart_2092785 baseEnd_2092785 := by
    simpa [prefixWord, tailWord_2092785, baseEnd_2092785] using wordTrace_append hprefix tailTrace_2092785
  have hstable : (prefixWord ++ tailWord_2092785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092785).length < 2 ^ (prefixWord ++ tailWord_2092785).sum := by decide
  have hdescent : baseEnd_2092785 < baseStart_2092785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092812 : List Nat := [2, 2, 1, 2, 2, 1, 6, 1, 1, 2, 3]
def baseStart_2092812 : Nat := 118140960795 + 2092812 * 2 ^ 59
def prefixEnd_2092812 : Nat := 4983230072969 + 3 ^ 40 * 2092812 * 2
def baseEnd_2092812 : Nat := 1074618475497371097125339

theorem tailTrace_2092812 : CollatzResearch.WordTrace tailWord_2092812 prefixEnd_2092812 1074618475497371097125339 := by
  unfold tailWord_2092812
  simp only [CollatzResearch.WordTrace]
  refine ⟨38165562247053511339372345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50887416329404681785829793 38165562247053511339372345)
  ·
    refine ⟨28624171685290133504529259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38165562247053511339372345 28624171685290133504529259)
    ·
      refine ⟨42936257527935200256793889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28624171685290133504529259 42936257527935200256793889)
      ·
        refine ⟨32202193145951400192595417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42936257527935200256793889 32202193145951400192595417)
        ·
          refine ⟨24151644859463550144446563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32202193145951400192595417 24151644859463550144446563)
          ·
            refine ⟨36227467289195325216669845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24151644859463550144446563 36227467289195325216669845)
            ·
              refine ⟨1698162529181030869531399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36227467289195325216669845 1698162529181030869531399)
              ·
                refine ⟨2547243793771546304297099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1698162529181030869531399 2547243793771546304297099)
                ·
                  refine ⟨3820865690657319456445649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2547243793771546304297099 3820865690657319456445649)
                  ·
                    refine ⟨2865649267992989592334237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3820865690657319456445649 2865649267992989592334237)
                    ·
                      refine ⟨1074618475497371097125339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2865649267992989592334237 1074618475497371097125339)
                      ·
                        rfl

theorem cell23_2092812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_2092812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092812 prefixEnd_2092812 := by exact prefixLift 2092812
  have htrace : WordTrace (prefixWord ++ tailWord_2092812) baseStart_2092812 baseEnd_2092812 := by
    simpa [prefixWord, tailWord_2092812, baseEnd_2092812] using wordTrace_append hprefix tailTrace_2092812
  have hstable : (prefixWord ++ tailWord_2092812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092812).length < 2 ^ (prefixWord ++ tailWord_2092812).sum := by decide
  have hdescent : baseEnd_2092812 < baseStart_2092812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092835 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 5, 3, 2]
def baseStart_2092835 : Nat := 118140960795 + 2092835 * 2 ^ 59
def prefixEnd_2092835 : Nat := 4983230072969 + 3 ^ 40 * 2092835 * 2
def baseEnd_2092835 : Nat := 1074630285552424507137733

theorem tailTrace_2092835 : CollatzResearch.WordTrace tailWord_2092835 prefixEnd_2092835 1074630285552424507137733 := by
  unfold tailWord_2092835
  simp only [CollatzResearch.WordTrace]
  refine ⟨76331963373023697606831959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50887975582015798404554639 76331963373023697606831959)
  ·
    refine ⟨114497945059535546410247939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76331963373023697606831959 114497945059535546410247939)
    ·
      refine ⟨171746917589303319615371909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114497945059535546410247939 171746917589303319615371909)
      ·
        refine ⟨32202547047994372427882233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171746917589303319615371909 32202547047994372427882233)
        ·
          refine ⟨24151910285995779320911675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32202547047994372427882233 24151910285995779320911675)
          ·
            refine ⟨36227865428993668981367513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24151910285995779320911675 36227865428993668981367513)
            ·
              refine ⟨27170899071745251736025635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36227865428993668981367513 27170899071745251736025635)
              ·
                refine ⟨40756348607617877604038453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27170899071745251736025635 40756348607617877604038453)
                ·
                  refine ⟨3820907681964176025378605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40756348607617877604038453 3820907681964176025378605)
                  ·
                    refine ⟨1432840380736566009516977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3820907681964176025378605 1432840380736566009516977)
                    ·
                      refine ⟨1074630285552424507137733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1432840380736566009516977 1074630285552424507137733)
                      ·
                        rfl

theorem cell23_2092835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_2092835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092835 prefixEnd_2092835 := by exact prefixLift 2092835
  have htrace : WordTrace (prefixWord ++ tailWord_2092835) baseStart_2092835 baseEnd_2092835 := by
    simpa [prefixWord, tailWord_2092835, baseEnd_2092835] using wordTrace_append hprefix tailTrace_2092835
  have hstable : (prefixWord ++ tailWord_2092835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092835).length < 2 ^ (prefixWord ++ tailWord_2092835).sum := by decide
  have hdescent : baseEnd_2092835 < baseStart_2092835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092928 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 5]
def baseStart_2092928 : Nat := 118140960795 + 2092928 * 2 ^ 59
def prefixEnd_2092928 : Nat := 4983230072969 + 3 ^ 40 * 2092928 * 2
def baseEnd_2092928 : Nat := 1074678039253292643274805

theorem tailTrace_2092928 : CollatzResearch.WordTrace tailWord_2092928 prefixEnd_2092928 1074678039253292643274805 := by
  unfold tailWord_2092928
  simp only [CollatzResearch.WordTrace]
  refine ⟨38167677680843387244983719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50890236907791182993311625 38167677680843387244983719)
  ·
    refine ⟨57251516521265080867475579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38167677680843387244983719 57251516521265080867475579)
    ·
      refine ⟨85877274781897621301213369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57251516521265080867475579 85877274781897621301213369)
      ·
        refine ⟨64407956086423215975910027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85877274781897621301213369 64407956086423215975910027)
        ·
          refine ⟨96611934129634823963865041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64407956086423215975910027 96611934129634823963865041)
          ·
            refine ⟨72458950597226117972898781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96611934129634823963865041 72458950597226117972898781)
            ·
              refine ⟨27172106473959794239837043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72458950597226117972898781 27172106473959794239837043)
              ·
                refine ⟨40758159710939691359755565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27172106473959794239837043 40758159710939691359755565)
                ·
                  refine ⟨15284309891602384259908337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40758159710939691359755565 15284309891602384259908337)
                  ·
                    refine ⟨11463232418701788194931253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15284309891602384259908337 11463232418701788194931253)
                    ·
                      refine ⟨1074678039253292643274805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11463232418701788194931253 1074678039253292643274805)
                      ·
                        rfl

theorem cell23_2092928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_2092928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092928 prefixEnd_2092928 := by exact prefixLift 2092928
  have htrace : WordTrace (prefixWord ++ tailWord_2092928) baseStart_2092928 baseEnd_2092928 := by
    simpa [prefixWord, tailWord_2092928, baseEnd_2092928] using wordTrace_append hprefix tailTrace_2092928
  have hstable : (prefixWord ++ tailWord_2092928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092928).length < 2 ^ (prefixWord ++ tailWord_2092928).sum := by decide
  have hdescent : baseEnd_2092928 < baseStart_2092928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092975 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 3]
def baseStart_2092975 : Nat := 118140960795 + 2092975 * 2 ^ 59
def prefixEnd_2092975 : Nat := 4983230072969 + 3 ^ 40 * 2092975 * 2
def baseEnd_2092975 : Nat := 1074702172844053959387089

theorem tailTrace_2092975 : CollatzResearch.WordTrace tailWord_2092975 prefixEnd_2092975 1074702172844053959387089 := by
  unfold tailWord_2092975
  simp only [CollatzResearch.WordTrace]
  refine ⟨76337069592516501516928379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50891379728344334344618919 76337069592516501516928379)
  ·
    refine ⟨114505604388774752275392569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76337069592516501516928379 114505604388774752275392569)
    ·
      refine ⟨85879203291581064206544427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114505604388774752275392569 85879203291581064206544427)
      ·
        refine ⟨128818804937371596309816641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85879203291581064206544427 128818804937371596309816641)
        ·
          refine ⟨96614103703028697232362481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128818804937371596309816641 96614103703028697232362481)
          ·
            refine ⟨72460577777271522924271861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96614103703028697232362481 72460577777271522924271861)
            ·
              refine ⟨6793179166619205274150487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72460577777271522924271861 6793179166619205274150487)
              ·
                refine ⟨10189768749928807911225731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6793179166619205274150487 10189768749928807911225731)
                ·
                  refine ⟨15284653124893211866838597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10189768749928807911225731 15284653124893211866838597)
                  ·
                    refine ⟨2865872460917477225032237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15284653124893211866838597 2865872460917477225032237)
                    ·
                      refine ⟨1074702172844053959387089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2865872460917477225032237 1074702172844053959387089)
                      ·
                        rfl

theorem cell23_2092975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 3].length) (baseStart_2092975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2092975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2092975 prefixEnd_2092975 := by exact prefixLift 2092975
  have htrace : WordTrace (prefixWord ++ tailWord_2092975) baseStart_2092975 baseEnd_2092975 := by
    simpa [prefixWord, tailWord_2092975, baseEnd_2092975] using wordTrace_append hprefix tailTrace_2092975
  have hstable : (prefixWord ++ tailWord_2092975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092975).length < 2 ^ (prefixWord ++ tailWord_2092975).sum := by decide
  have hdescent : baseEnd_2092975 < baseStart_2092975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093025 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 3, 5]
def baseStart_2093025 : Nat := 118140960795 + 2093025 * 2 ^ 59
def prefixEnd_2093025 : Nat := 4983230072969 + 3 ^ 40 * 2093025 * 2
def baseEnd_2093025 : Nat := 358242615625592921253953

theorem tailTrace_2093025 : CollatzResearch.WordTrace tailWord_2093025 prefixEnd_2093025 358242615625592921253953 := by
  unfold tailWord_2093025
  simp only [CollatzResearch.WordTrace]
  refine ⟨76338893242335360056248529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50892595494890240037499019 76338893242335360056248529)
  ·
    refine ⟨57254169931751520042186397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76338893242335360056248529 57254169931751520042186397)
    ·
      refine ⟨21470313724406820015819899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57254169931751520042186397 21470313724406820015819899)
      ·
        refine ⟨32205470586610230023729849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21470313724406820015819899 32205470586610230023729849)
        ·
          refine ⟨24154102939957672517797387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32205470586610230023729849 24154102939957672517797387)
          ·
            refine ⟨36231154409936508776696081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24154102939957672517797387 36231154409936508776696081)
            ·
              refine ⟨27173365807452381582522061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36231154409936508776696081 27173365807452381582522061)
              ·
                refine ⟨10190012177794643093445773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27173365807452381582522061 10190012177794643093445773)
                ·
                  refine ⟨3821254566672991160042165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10190012177794643093445773 3821254566672991160042165)
                  ·
                    refine ⟨358242615625592921253953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3821254566672991160042165 358242615625592921253953)
                    ·
                      rfl

theorem cell23_2093025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_2093025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093025 prefixEnd_2093025 := by exact prefixLift 2093025
  have htrace : WordTrace (prefixWord ++ tailWord_2093025) baseStart_2093025 baseEnd_2093025 := by
    simpa [prefixWord, tailWord_2093025, baseEnd_2093025] using wordTrace_append hprefix tailTrace_2093025
  have hstable : (prefixWord ++ tailWord_2093025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093025).length < 2 ^ (prefixWord ++ tailWord_2093025).sum := by decide
  have hdescent : baseEnd_2093025 < baseStart_2093025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093049 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 2, 3, 2]
def baseStart_2093049 : Nat := 118140960795 + 2093049 * 2 ^ 59
def prefixEnd_2093049 : Nat := 4983230072969 + 3 ^ 40 * 2093049 * 2
def baseEnd_2093049 : Nat := 1074740170412486669861749

theorem tailTrace_2093049 : CollatzResearch.WordTrace tailWord_2093049 prefixEnd_2093049 1074740170412486669861749 := by
  unfold tailWord_2093049
  simp only [CollatzResearch.WordTrace]
  refine ⟨76339768594248412155122201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50893179062832274770081467 76339768594248412155122201)
  ·
    refine ⟨57254826445686309116341651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76339768594248412155122201 57254826445686309116341651)
    ·
      refine ⟨85882239668529463674512477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57254826445686309116341651 85882239668529463674512477)
      ·
        refine ⟨32205839875698548877942179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85882239668529463674512477 32205839875698548877942179)
        ·
          refine ⟨48308759813547823316913269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32205839875698548877942179 48308759813547823316913269)
          ·
            refine ⟨4528946232520108435960619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48308759813547823316913269 4528946232520108435960619)
            ·
              refine ⟨6793419348780162653940929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528946232520108435960619 6793419348780162653940929)
              ·
                refine ⟨5095064511585121990455697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6793419348780162653940929 5095064511585121990455697)
                ·
                  refine ⟨3821298383688841492841773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5095064511585121990455697 3821298383688841492841773)
                  ·
                    refine ⟨1432986893883315559815665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3821298383688841492841773 1432986893883315559815665)
                    ·
                      refine ⟨1074740170412486669861749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1432986893883315559815665 1074740170412486669861749)
                      ·
                        rfl

theorem cell23_2093049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_2093049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093049 prefixEnd_2093049 := by exact prefixLift 2093049
  have htrace : WordTrace (prefixWord ++ tailWord_2093049) baseStart_2093049 baseEnd_2093049 := by
    simpa [prefixWord, tailWord_2093049, baseEnd_2093049] using wordTrace_append hprefix tailTrace_2093049
  have hstable : (prefixWord ++ tailWord_2093049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093049).length < 2 ^ (prefixWord ++ tailWord_2093049).sum := by decide
  have hdescent : baseEnd_2093049 < baseStart_2093049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093065 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 1, 8, 3]
def baseStart_2093065 : Nat := 118140960795 + 2093065 * 2 ^ 59
def prefixEnd_2093065 : Nat := 4983230072969 + 3 ^ 40 * 2093065 * 2
def baseEnd_2093065 : Nat := 1074748386102958607261675

theorem tailTrace_2093065 : CollatzResearch.WordTrace tailWord_2093065 prefixEnd_2093065 1074748386102958607261675 := by
  unfold tailWord_2093065
  simp only [CollatzResearch.WordTrace]
  refine ⟨76340352162190446887704649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50893568108126964591803099 76340352162190446887704649)
  ·
    refine ⟨57255264121642835165778487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76340352162190446887704649 57255264121642835165778487)
    ·
      refine ⟨85882896182464252748667731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57255264121642835165778487 85882896182464252748667731)
      ·
        refine ⟨128824344273696379123001597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85882896182464252748667731 128824344273696379123001597)
        ·
          refine ⟨48309129102636142171125599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128824344273696379123001597 48309129102636142171125599)
          ·
            refine ⟨72463693653954213256688399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48309129102636142171125599 72463693653954213256688399)
            ·
              refine ⟨108695540480931319885032599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72463693653954213256688399 108695540480931319885032599)
              ·
                refine ⟨163043310721396979827548899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108695540480931319885032599 163043310721396979827548899)
                ·
                  refine ⟨244564966082095469741323349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163043310721396979827548899 244564966082095469741323349)
                  ·
                    refine ⟨2865995696274556286031133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 244564966082095469741323349 2865995696274556286031133)
                    ·
                      refine ⟨1074748386102958607261675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2865995696274556286031133 1074748386102958607261675)
                      ·
                        rfl

theorem cell23_2093065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 8, 3].length) (baseStart_2093065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093065 prefixEnd_2093065 := by exact prefixLift 2093065
  have htrace : WordTrace (prefixWord ++ tailWord_2093065) baseStart_2093065 baseEnd_2093065 := by
    simpa [prefixWord, tailWord_2093065, baseEnd_2093065] using wordTrace_append hprefix tailTrace_2093065
  have hstable : (prefixWord ++ tailWord_2093065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093065).length < 2 ^ (prefixWord ++ tailWord_2093065).sum := by decide
  have hdescent : baseEnd_2093065 < baseStart_2093065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093072 : List Nat := [2, 1, 1, 1, 1, 1, 1, 9, 2, 4]
def baseStart_2093072 : Nat := 118140960795 + 2093072 * 2 ^ 59
def prefixEnd_2093072 : Nat := 4983230072969 + 3 ^ 40 * 2093072 * 2
def baseEnd_2093072 : Nat := 358250660155846693291381

theorem tailTrace_2093072 : CollatzResearch.WordTrace tailWord_2093072 prefixEnd_2093072 358250660155846693291381 := by
  unfold tailWord_2093072
  simp only [CollatzResearch.WordTrace]
  refine ⟨38170303736582543541604735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50893738315443391388806313 38170303736582543541604735)
  ·
    refine ⟨57255455604873815312407103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38170303736582543541604735 57255455604873815312407103)
    ·
      refine ⟨85883183407310722968610655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57255455604873815312407103 85883183407310722968610655)
      ·
        refine ⟨128824775110966084452915983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85883183407310722968610655 128824775110966084452915983)
        ·
          refine ⟨193237162666449126679373975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128824775110966084452915983 193237162666449126679373975)
          ·
            refine ⟨289855743999673690019060963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193237162666449126679373975 289855743999673690019060963)
            ·
              refine ⟨434783615999510535028591445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289855743999673690019060963 434783615999510535028591445)
              ·
                refine ⟨2547560249997132041183153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 434783615999510535028591445 2547560249997132041183153)
                ·
                  refine ⟨1910670187497849030887365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2547560249997132041183153 1910670187497849030887365)
                  ·
                    refine ⟨358250660155846693291381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1910670187497849030887365 358250660155846693291381)
                    ·
                      rfl

theorem cell23_2093072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 2, 4].length) (baseStart_2093072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093072 prefixEnd_2093072 := by exact prefixLift 2093072
  have htrace : WordTrace (prefixWord ++ tailWord_2093072) baseStart_2093072 baseEnd_2093072 := by
    simpa [prefixWord, tailWord_2093072, baseEnd_2093072] using wordTrace_append hprefix tailTrace_2093072
  have hstable : (prefixWord ++ tailWord_2093072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093072).length < 2 ^ (prefixWord ++ tailWord_2093072).sum := by decide
  have hdescent : baseEnd_2093072 < baseStart_2093072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093075 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 6]
def baseStart_2093075 : Nat := 118140960795 + 2093075 * 2 ^ 59
def prefixEnd_2093075 : Nat := 4983230072969 + 3 ^ 40 * 2093075 * 2
def baseEnd_2093075 : Nat := 1074753520909503568136629

theorem tailTrace_2093075 : CollatzResearch.WordTrace tailWord_2093075 prefixEnd_2093075 1074753520909503568136629 := by
  unfold tailWord_2093075
  simp only [CollatzResearch.WordTrace]
  refine ⟨76340716892154218595568679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50893811261436145730379119 76340716892154218595568679)
  ·
    refine ⟨114511075338231327893353019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76340716892154218595568679 114511075338231327893353019)
    ·
      refine ⟨171766613007346991840029529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114511075338231327893353019 171766613007346991840029529)
      ·
        refine ⟨128824959755510243880022147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171766613007346991840029529 128824959755510243880022147)
        ·
          refine ⟨193237439633265365820033221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128824959755510243880022147 193237439633265365820033221)
          ·
            refine ⟨36232019931237256091256229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193237439633265365820033221 36232019931237256091256229)
            ·
              refine ⟨6793503737106985517110543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36232019931237256091256229 6793503737106985517110543)
              ·
                refine ⟨10190255605660478275665815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6793503737106985517110543 10190255605660478275665815)
                ·
                  refine ⟨15285383408490717413498723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10190255605660478275665815 15285383408490717413498723)
                  ·
                    refine ⟨22928075112736076120248085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15285383408490717413498723 22928075112736076120248085)
                    ·
                      refine ⟨1074753520909503568136629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22928075112736076120248085 1074753520909503568136629)
                      ·
                        rfl

theorem cell23_2093075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_2093075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093075 prefixEnd_2093075 := by exact prefixLift 2093075
  have htrace : WordTrace (prefixWord ++ tailWord_2093075) baseStart_2093075 baseEnd_2093075 := by
    simpa [prefixWord, tailWord_2093075, baseEnd_2093075] using wordTrace_append hprefix tailTrace_2093075
  have hstable : (prefixWord ++ tailWord_2093075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093075).length < 2 ^ (prefixWord ++ tailWord_2093075).sum := by decide
  have hdescent : baseEnd_2093075 < baseStart_2093075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093076 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2093076 : Nat := 118140960795 + 2093076 * 2 ^ 59
def prefixEnd_2093076 : Nat := 4983230072969 + 3 ^ 40 * 2093076 * 2
def baseEnd_2093076 : Nat := 358251344796719354741375

theorem tailTrace_2093076 : CollatzResearch.WordTrace tailWord_2093076 prefixEnd_2093076 358251344796719354741375 := by
  unfold tailWord_2093076
  simp only [CollatzResearch.WordTrace]
  refine ⟨38170376682575297883177541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50893835576767063844236721 38170376682575297883177541)
  ·
    refine ⟨7156945627982868353095789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38170376682575297883177541 7156945627982868353095789)
    ·
      refine ⟨2683854610493575632410921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7156945627982868353095789 2683854610493575632410921)
      ·
        refine ⟨2012890957870181724308191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2683854610493575632410921 2012890957870181724308191)
        ·
          refine ⟨3019336436805272586462287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2012890957870181724308191 3019336436805272586462287)
          ·
            refine ⟨4529004655207908879693431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019336436805272586462287 4529004655207908879693431)
            ·
              refine ⟨6793506982811863319540147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529004655207908879693431 6793506982811863319540147)
              ·
                refine ⟨10190260474217794979310221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6793506982811863319540147 10190260474217794979310221)
                ·
                  refine ⟨3821347677831673117241333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10190260474217794979310221 3821347677831673117241333)
                  ·
                    refine ⟨358251344796719354741375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3821347677831673117241333 358251344796719354741375)
                    ·
                      rfl

theorem cell23_2093076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2093076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093076 prefixEnd_2093076 := by exact prefixLift 2093076
  have htrace : WordTrace (prefixWord ++ tailWord_2093076) baseStart_2093076 baseEnd_2093076 := by
    simpa [prefixWord, tailWord_2093076, baseEnd_2093076] using wordTrace_append hprefix tailTrace_2093076
  have hstable : (prefixWord ++ tailWord_2093076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093076).length < 2 ^ (prefixWord ++ tailWord_2093076).sum := by decide
  have hdescent : baseEnd_2093076 < baseStart_2093076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093079 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2093079 : Nat := 118140960795 + 2093079 * 2 ^ 59
def prefixEnd_2093079 : Nat := 4983230072969 + 3 ^ 40 * 2093079 * 2
def baseEnd_2093079 : Nat := 1074755574832121552486611

theorem tailTrace_2093079 : CollatzResearch.WordTrace tailWord_2093079 prefixEnd_2093079 1074755574832121552486611 := by
  unfold tailWord_2093079
  simp only [CollatzResearch.WordTrace]
  refine ⟨76340862784139727278714291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50893908522759818185809527 76340862784139727278714291)
  ·
    refine ⟨114511294176209590918071437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76340862784139727278714291 114511294176209590918071437)
    ·
      refine ⟨42941735316078596594276789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114511294176209590918071437 42941735316078596594276789)
      ·
        refine ⟨4025787685882368430713449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42941735316078596594276789 4025787685882368430713449)
        ·
          refine ⟨3019340764411776323035087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4025787685882368430713449 3019340764411776323035087)
          ·
            refine ⟨4529011146617664484552631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019340764411776323035087 4529011146617664484552631)
            ·
              refine ⟨6793516719926496726828947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529011146617664484552631 6793516719926496726828947)
              ·
                refine ⟨10190275079889745090243421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6793516719926496726828947 10190275079889745090243421)
                ·
                  refine ⟨3821353154958654408841283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10190275079889745090243421 3821353154958654408841283)
                  ·
                    refine ⟨5732029732437981613261925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3821353154958654408841283 5732029732437981613261925)
                    ·
                      refine ⟨1074755574832121552486611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5732029732437981613261925 1074755574832121552486611)
                      ·
                        rfl

theorem cell23_2093079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2093079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093079 prefixEnd_2093079 := by exact prefixLift 2093079
  have htrace : WordTrace (prefixWord ++ tailWord_2093079) baseStart_2093079 baseEnd_2093079 := by
    simpa [prefixWord, tailWord_2093079, baseEnd_2093079] using wordTrace_append hprefix tailTrace_2093079
  have hstable : (prefixWord ++ tailWord_2093079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093079).length < 2 ^ (prefixWord ++ tailWord_2093079).sum := by decide
  have hdescent : baseEnd_2093079 < baseStart_2093079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093125 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_2093125 : Nat := 118140960795 + 2093125 * 2 ^ 59
def prefixEnd_2093125 : Nat := 4983230072969 + 3 ^ 40 * 2093125 * 2
def baseEnd_2093125 : Nat := 1074779194942228372511399

theorem tailTrace_2093125 : CollatzResearch.WordTrace tailWord_2093125 prefixEnd_2093125 1074779194942228372511399 := by
  unfold tailWord_2093125
  simp only [CollatzResearch.WordTrace]
  refine ⟨76342540541973077134888829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50895027027982051423259219 76342540541973077134888829)
  ·
    refine ⟨28628452703239903925583311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76342540541973077134888829 28628452703239903925583311)
    ·
      refine ⟨42942679054859855888374967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28628452703239903925583311 42942679054859855888374967)
      ·
        refine ⟨64414018582289783832562451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42942679054859855888374967 64414018582289783832562451)
        ·
          refine ⟨96621027873434675748843677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64414018582289783832562451 96621027873434675748843677)
          ·
            refine ⟨36232885452538003405816379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96621027873434675748843677 36232885452538003405816379)
            ·
              refine ⟨54349328178807005108724569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36232885452538003405816379 54349328178807005108724569)
              ·
                refine ⟨40761996134105253831543427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54349328178807005108724569 40761996134105253831543427)
                ·
                  refine ⟨61142994201157880747315141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40761996134105253831543427 61142994201157880747315141)
                  ·
                    refine ⟨11464311412717102640121589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61142994201157880747315141 11464311412717102640121589)
                    ·
                      refine ⟨1074779194942228372511399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11464311412717102640121589 1074779194942228372511399)
                      ·
                        rfl

theorem cell23_2093125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_2093125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093125 prefixEnd_2093125 := by exact prefixLift 2093125
  have htrace : WordTrace (prefixWord ++ tailWord_2093125) baseStart_2093125 baseEnd_2093125 := by
    simpa [prefixWord, tailWord_2093125, baseEnd_2093125] using wordTrace_append hprefix tailTrace_2093125
  have hstable : (prefixWord ++ tailWord_2093125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093125).length < 2 ^ (prefixWord ++ tailWord_2093125).sum := by decide
  have hdescent : baseEnd_2093125 < baseStart_2093125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093126 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_2093126 : Nat := 118140960795 + 2093126 * 2 ^ 59
def prefixEnd_2093126 : Nat := 4983230072969 + 3 ^ 40 * 2093126 * 2
def baseEnd_2093126 : Nat := 1074779708422882868598895

theorem tailTrace_2093126 : CollatzResearch.WordTrace tailWord_2093126 prefixEnd_2093126 1074779708422882868598895 := by
  unfold tailWord_2093126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385705531717795447052351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50895051343312969537116821 2385705531717795447052351)
  ·
    refine ⟨3578558297576693170578527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2385705531717795447052351 3578558297576693170578527)
    ·
      refine ⟨5367837446365039755867791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3578558297576693170578527 5367837446365039755867791)
      ·
        refine ⟨8051756169547559633801687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5367837446365039755867791 8051756169547559633801687)
        ·
          refine ⟨12077634254321339450702531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8051756169547559633801687 12077634254321339450702531)
          ·
            refine ⟨18116451381482009176053797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12077634254321339450702531 18116451381482009176053797)
            ·
              refine ⟨3396834634027876720510087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18116451381482009176053797 3396834634027876720510087)
              ·
                refine ⟨5095251951041815080765131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3396834634027876720510087 5095251951041815080765131)
                ·
                  refine ⟨7642877926562722621147697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095251951041815080765131 7642877926562722621147697)
                  ·
                    refine ⟨5732158444922041965860773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7642877926562722621147697 5732158444922041965860773)
                    ·
                      refine ⟨1074779708422882868598895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5732158444922041965860773 1074779708422882868598895)
                      ·
                        rfl

theorem cell23_2093126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_2093126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093126 prefixEnd_2093126 := by exact prefixLift 2093126
  have htrace : WordTrace (prefixWord ++ tailWord_2093126) baseStart_2093126 baseEnd_2093126 := by
    simpa [prefixWord, tailWord_2093126, baseEnd_2093126] using wordTrace_append hprefix tailTrace_2093126
  have hstable : (prefixWord ++ tailWord_2093126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093126).length < 2 ^ (prefixWord ++ tailWord_2093126).sum := by decide
  have hdescent : baseEnd_2093126 < baseStart_2093126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093129 : List Nat := [1, 2, 1, 1, 2, 2, 3, 5, 2, 1, 3]
def baseStart_2093129 : Nat := 118140960795 + 2093129 * 2 ^ 59
def prefixEnd_2093129 : Nat := 4983230072969 + 3 ^ 40 * 2093129 * 2
def baseEnd_2093129 : Nat := 1074781248864846356861381

theorem tailTrace_2093129 : CollatzResearch.WordTrace tailWord_2093129 prefixEnd_2093129 1074781248864846356861381 := by
  unfold tailWord_2093129
  simp only [CollatzResearch.WordTrace]
  refine ⟨76342686433958585818034441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50895124289305723878689627 76342686433958585818034441)
  ·
    refine ⟨57257014825468939363525831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76342686433958585818034441 57257014825468939363525831)
    ·
      refine ⟨85885522238203409045288747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57257014825468939363525831 85885522238203409045288747)
      ·
        refine ⟨128828283357305113567933121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85885522238203409045288747 128828283357305113567933121)
        ·
          refine ⟨96621212517978835175949841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128828283357305113567933121 96621212517978835175949841)
          ·
            refine ⟨72465909388484126381962381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96621212517978835175949841 72465909388484126381962381)
            ·
              refine ⟨27174716020681547393235893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72465909388484126381962381 27174716020681547393235893)
              ·
                refine ⟨2547629626938895068115865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27174716020681547393235893 2547629626938895068115865)
                ·
                  refine ⟨1910722220204171301086899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2547629626938895068115865 1910722220204171301086899)
                  ·
                    refine ⟨2866083330306256951630349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1910722220204171301086899 2866083330306256951630349)
                    ·
                      refine ⟨1074781248864846356861381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2866083330306256951630349 1074781248864846356861381)
                      ·
                        rfl

theorem cell23_2093129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 1, 3].length) (baseStart_2093129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093129 prefixEnd_2093129 := by exact prefixLift 2093129
  have htrace : WordTrace (prefixWord ++ tailWord_2093129) baseStart_2093129 baseEnd_2093129 := by
    simpa [prefixWord, tailWord_2093129, baseEnd_2093129] using wordTrace_append hprefix tailTrace_2093129
  have hstable : (prefixWord ++ tailWord_2093129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093129).length < 2 ^ (prefixWord ++ tailWord_2093129).sum := by decide
  have hdescent : baseEnd_2093129 < baseStart_2093129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093145 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 1, 8]
def baseStart_2093145 : Nat := 118140960795 + 2093145 * 2 ^ 59
def prefixEnd_2093145 : Nat := 4983230072969 + 3 ^ 40 * 2093145 * 2
def baseEnd_2093145 : Nat := 358263154851772764753769

theorem tailTrace_2093145 : CollatzResearch.WordTrace tailWord_2093145 prefixEnd_2093145 358263154851772764753769 := by
  unfold tailWord_2093145
  simp only [CollatzResearch.WordTrace]
  refine ⟨76343270001900620550616889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50895513334600413700411259 76343270001900620550616889)
  ·
    refine ⟨57257452501425465412962667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76343270001900620550616889 57257452501425465412962667)
    ·
      refine ⟨85886178752138198119444001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57257452501425465412962667 85886178752138198119444001)
      ·
        refine ⟨64414634064103648589583001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85886178752138198119444001 64414634064103648589583001)
        ·
          refine ⟨48310975548077736442187251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64414634064103648589583001 48310975548077736442187251)
          ·
            refine ⟨72466463322116604663280877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48310975548077736442187251 72466463322116604663280877)
            ·
              refine ⟨27174923745793726748730329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72466463322116604663280877 27174923745793726748730329)
              ·
                refine ⟨20381192809345295061547747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27174923745793726748730329 20381192809345295061547747)
                ·
                  refine ⟨30571789214017942592321621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20381192809345295061547747 30571789214017942592321621)
                  ·
                    refine ⟨358263154851772764753769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30571789214017942592321621 358263154851772764753769)
                    ·
                      rfl

theorem cell23_2093145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_2093145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093145 prefixEnd_2093145 := by exact prefixLift 2093145
  have htrace : WordTrace (prefixWord ++ tailWord_2093145) baseStart_2093145 baseEnd_2093145 := by
    simpa [prefixWord, tailWord_2093145, baseEnd_2093145] using wordTrace_append hprefix tailTrace_2093145
  have hstable : (prefixWord ++ tailWord_2093145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093145).length < 2 ^ (prefixWord ++ tailWord_2093145).sum := by decide
  have hdescent : baseEnd_2093145 < baseStart_2093145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093150 : List Nat := [4, 4, 1, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_2093150 : Nat := 118140960795 + 2093150 * 2 ^ 59
def prefixEnd_2093150 : Nat := 4983230072969 + 3 ^ 40 * 2093150 * 2
def baseEnd_2093150 : Nat := 1074792031958590774698785

theorem tailTrace_2093150 : CollatzResearch.WordTrace tailWord_2093150 prefixEnd_2093150 1074792031958590774698785 := by
  unfold tailWord_2093150
  simp only [CollatzResearch.WordTrace]
  refine ⟨9542931545860313300568613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50895634911255004269699269 9542931545860313300568613)
  ·
    refine ⟨1789299664848808743856615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9542931545860313300568613 1789299664848808743856615)
    ·
      refine ⟨2683949497273213115784923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1789299664848808743856615 2683949497273213115784923)
      ·
        refine ⟨4025924245909819673677385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2683949497273213115784923 4025924245909819673677385)
        ·
          refine ⟨3019443184432364755258039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4025924245909819673677385 3019443184432364755258039)
          ·
            refine ⟨4529164776648547132887059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019443184432364755258039 4529164776648547132887059)
            ·
              refine ⟨6793747164972820699330589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529164776648547132887059 6793747164972820699330589)
              ·
                refine ⟨2547655186864807762248971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6793747164972820699330589 2547655186864807762248971)
                ·
                  refine ⟨3821482780297211643373457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2547655186864807762248971 3821482780297211643373457)
                  ·
                    refine ⟨2866112085222908732530093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3821482780297211643373457 2866112085222908732530093)
                    ·
                      refine ⟨1074792031958590774698785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2866112085222908732530093 1074792031958590774698785)
                      ·
                        rfl

theorem cell23_2093150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_2093150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093150 prefixEnd_2093150 := by exact prefixLift 2093150
  have htrace : WordTrace (prefixWord ++ tailWord_2093150) baseStart_2093150 baseEnd_2093150 := by
    simpa [prefixWord, tailWord_2093150, baseEnd_2093150] using wordTrace_append hprefix tailTrace_2093150
  have hstable : (prefixWord ++ tailWord_2093150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093150).length < 2 ^ (prefixWord ++ tailWord_2093150).sum := by decide
  have hdescent : baseEnd_2093150 < baseStart_2093150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093242 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_2093242 : Nat := 118140960795 + 2093242 * 2 ^ 59
def prefixEnd_2093242 : Nat := 4983230072969 + 3 ^ 40 * 2093242 * 2
def baseEnd_2093242 : Nat := 1074839272178804414748361

theorem tailTrace_2093242 : CollatzResearch.WordTrace tailWord_2093242 prefixEnd_2093242 1074839272178804414748361 := by
  unfold tailWord_2093242
  simp only [CollatzResearch.WordTrace]
  refine ⟨19086701970637301529224495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50897871921699470744598653 19086701970637301529224495)
  ·
    refine ⟨28630052955955952293836743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19086701970637301529224495 28630052955955952293836743)
    ·
      refine ⟨42945079433933928440755115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28630052955955952293836743 42945079433933928440755115)
      ·
        refine ⟨64417619150900892661132673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42945079433933928440755115 64417619150900892661132673)
        ·
          refine ⟨48313214363175669495849505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64417619150900892661132673 48313214363175669495849505)
          ·
            refine ⟨36234910772381752121887129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48313214363175669495849505 36234910772381752121887129)
            ·
              refine ⟨27176183079286314091415347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36234910772381752121887129 27176183079286314091415347)
              ·
                refine ⟨40764274618929471137123021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27176183079286314091415347 40764274618929471137123021)
                ·
                  refine ⟨15286602982098551676421133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40764274618929471137123021 15286602982098551676421133)
                  ·
                    refine ⟨5732476118286956878657925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15286602982098551676421133 5732476118286956878657925)
                    ·
                      refine ⟨1074839272178804414748361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5732476118286956878657925 1074839272178804414748361)
                      ·
                        rfl

theorem cell23_2093242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_2093242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093242 prefixEnd_2093242 := by exact prefixLift 2093242
  have htrace : WordTrace (prefixWord ++ tailWord_2093242) baseStart_2093242 baseEnd_2093242 := by
    simpa [prefixWord, tailWord_2093242, baseEnd_2093242] using wordTrace_append hprefix tailTrace_2093242
  have hstable : (prefixWord ++ tailWord_2093242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093242).length < 2 ^ (prefixWord ++ tailWord_2093242).sum := by decide
  have hdescent : baseEnd_2093242 < baseStart_2093242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093259 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 4]
def baseStart_2093259 : Nat := 118140960795 + 2093259 * 2 ^ 59
def prefixEnd_2093259 : Nat := 4983230072969 + 3 ^ 40 * 2093259 * 2
def baseEnd_2093259 : Nat := 1074848001349930848235783

theorem tailTrace_2093259 : CollatzResearch.WordTrace tailWord_2093259 prefixEnd_2093259 1074848001349930848235783 := by
  unfold tailWord_2093259
  simp only [CollatzResearch.WordTrace]
  refine ⟨76347427923487618020266831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50898285282325078680177887 76347427923487618020266831)
  ·
    refine ⟨114521141885231427030400247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76347427923487618020266831 114521141885231427030400247)
    ·
      refine ⟨171781712827847140545600371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114521141885231427030400247 171781712827847140545600371)
      ·
        refine ⟨257672569241770710818400557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171781712827847140545600371 257672569241770710818400557)
        ·
          refine ⟨96627213465664016556900209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257672569241770710818400557 96627213465664016556900209)
          ·
            refine ⟨72470410099248012417675157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96627213465664016556900209 72470410099248012417675157)
            ·
              refine ⟨3397050473402250582078523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72470410099248012417675157 3397050473402250582078523)
              ·
                refine ⟨5095575710103375873117785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3397050473402250582078523 5095575710103375873117785)
                ·
                  refine ⟨3821681782577531904838339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5095575710103375873117785 3821681782577531904838339)
                  ·
                    refine ⟨5732522673866297857257509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3821681782577531904838339 5732522673866297857257509)
                    ·
                      refine ⟨1074848001349930848235783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5732522673866297857257509 1074848001349930848235783)
                      ·
                        rfl

theorem cell23_2093259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 4].length) (baseStart_2093259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093259 prefixEnd_2093259 := by exact prefixLift 2093259
  have htrace : WordTrace (prefixWord ++ tailWord_2093259) baseStart_2093259 baseEnd_2093259 := by
    simpa [prefixWord, tailWord_2093259, baseEnd_2093259] using wordTrace_append hprefix tailTrace_2093259
  have hstable : (prefixWord ++ tailWord_2093259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093259).length < 2 ^ (prefixWord ++ tailWord_2093259).sum := by decide
  have hdescent : baseEnd_2093259 < baseStart_2093259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093293 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_2093293 : Nat := 118140960795 + 2093293 * 2 ^ 59
def prefixEnd_2093293 : Nat := 4983230072969 + 3 ^ 40 * 2093293 * 2
def baseEnd_2093293 : Nat := 1074865459692183715210627

theorem tailTrace_2093293 : CollatzResearch.WordTrace tailWord_2093293 prefixEnd_2093293 1074865459692183715210627 := by
  unfold tailWord_2093293
  simp only [CollatzResearch.WordTrace]
  refine ⟨76348668005364441827004533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50899112003576294551336355 76348668005364441827004533)
  ·
    refine ⟨7157687625502916421281675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76348668005364441827004533 7157687625502916421281675)
    ·
      refine ⟨10736531438254374631922513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7157687625502916421281675 10736531438254374631922513)
      ·
        refine ⟨8052398578690780973941885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10736531438254374631922513 8052398578690780973941885)
        ·
          refine ⟨3019649467009042865228207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8052398578690780973941885 3019649467009042865228207)
          ·
            refine ⟨4529474200513564297842311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019649467009042865228207 4529474200513564297842311)
            ·
              refine ⟨6794211300770346446763467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529474200513564297842311 6794211300770346446763467)
              ·
                refine ⟨10191316951155519670145201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6794211300770346446763467 10191316951155519670145201)
                ·
                  refine ⟨7643487713366639752608901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10191316951155519670145201 7643487713366639752608901)
                  ·
                    refine ⟨1433153946256244953614169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7643487713366639752608901 1433153946256244953614169)
                    ·
                      refine ⟨1074865459692183715210627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1433153946256244953614169 1074865459692183715210627)
                      ·
                        rfl

theorem cell23_2093293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_2093293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093293 prefixEnd_2093293 := by exact prefixLift 2093293
  have htrace : WordTrace (prefixWord ++ tailWord_2093293) baseStart_2093293 baseEnd_2093293 := by
    simpa [prefixWord, tailWord_2093293, baseEnd_2093293] using wordTrace_append hprefix tailTrace_2093293
  have hstable : (prefixWord ++ tailWord_2093293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093293).length < 2 ^ (prefixWord ++ tailWord_2093293).sum := by decide
  have hdescent : baseEnd_2093293 < baseStart_2093293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093326 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3]
def baseStart_2093326 : Nat := 118140960795 + 2093326 * 2 ^ 59
def prefixEnd_2093326 : Nat := 4983230072969 + 3 ^ 40 * 2093326 * 2
def baseEnd_2093326 : Nat := 1074882404553782086097975

theorem tailTrace_2093326 : CollatzResearch.WordTrace tailWord_2093326 prefixEnd_2093326 1074882404553782086097975 := by
  unfold tailWord_2093326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9543733951780611057869479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50899914409496592308637221 9543733951780611057869479)
  ·
    refine ⟨14315600927670916586804219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9543733951780611057869479 14315600927670916586804219)
    ·
      refine ⟨21473401391506374880206329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14315600927670916586804219 21473401391506374880206329)
      ·
        refine ⟨16105051043629781160154747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21473401391506374880206329 16105051043629781160154747)
        ·
          refine ⟨24157576565444671740232121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16105051043629781160154747 24157576565444671740232121)
          ·
            refine ⟨18118182424083503805174091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24157576565444671740232121 18118182424083503805174091)
            ·
              refine ⟨27177273636125255707761137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18118182424083503805174091 27177273636125255707761137)
              ·
                refine ⟨20382955227093941780820853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27177273636125255707761137 20382955227093941780820853)
                ·
                  refine ⟨1910902052540057041951955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20382955227093941780820853 1910902052540057041951955)
                  ·
                    refine ⟨2866353078810085562927933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1910902052540057041951955 2866353078810085562927933)
                    ·
                      refine ⟨1074882404553782086097975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2866353078810085562927933 1074882404553782086097975)
                      ·
                        rfl

theorem cell23_2093326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_2093326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093326 prefixEnd_2093326 := by exact prefixLift 2093326
  have htrace : WordTrace (prefixWord ++ tailWord_2093326) baseStart_2093326 baseEnd_2093326 := by
    simpa [prefixWord, tailWord_2093326, baseEnd_2093326] using wordTrace_append hprefix tailTrace_2093326
  have hstable : (prefixWord ++ tailWord_2093326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093326).length < 2 ^ (prefixWord ++ tailWord_2093326).sum := by decide
  have hdescent : baseEnd_2093326 < baseStart_2093326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093336 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 4, 3, 2]
def baseStart_2093336 : Nat := 118140960795 + 2093336 * 2 ^ 59
def prefixEnd_2093336 : Nat := 4983230072969 + 3 ^ 40 * 2093336 * 2
def baseEnd_2093336 : Nat := 1074887539360327046972929

theorem tailTrace_2093336 : CollatzResearch.WordTrace tailWord_2093336 prefixEnd_2093336 1074887539360327046972929 := by
  unfold tailWord_2093336
  simp only [CollatzResearch.WordTrace]
  refine ⟨38175118172104330085409931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50900157562805773447213241 38175118172104330085409931)
  ·
    refine ⟨57262677258156495128114897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38175118172104330085409931 57262677258156495128114897)
    ·
      refine ⟨42947007943617371346086173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57262677258156495128114897 42947007943617371346086173)
      ·
        refine ⟨16105127978856514254782315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42947007943617371346086173 16105127978856514254782315)
        ·
          refine ⟨24157691968284771382173473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16105127978856514254782315 24157691968284771382173473)
          ·
            refine ⟨18118268976213578536630105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24157691968284771382173473 18118268976213578536630105)
            ·
              refine ⟨13588701732160183902472579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18118268976213578536630105 13588701732160183902472579)
              ·
                refine ⟨20383052598240275853708869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13588701732160183902472579 20383052598240275853708869)
                ·
                  refine ⟨3821822362170051722570413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20383052598240275853708869 3821822362170051722570413)
                  ·
                    refine ⟨1433183385813769395963905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3821822362170051722570413 1433183385813769395963905)
                    ·
                      refine ⟨1074887539360327046972929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1433183385813769395963905 1074887539360327046972929)
                      ·
                        rfl

theorem cell23_2093336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_2093336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093336 prefixEnd_2093336 := by exact prefixLift 2093336
  have htrace : WordTrace (prefixWord ++ tailWord_2093336) baseStart_2093336 baseEnd_2093336 := by
    simpa [prefixWord, tailWord_2093336, baseEnd_2093336] using wordTrace_append hprefix tailTrace_2093336
  have hstable : (prefixWord ++ tailWord_2093336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093336).length < 2 ^ (prefixWord ++ tailWord_2093336).sum := by decide
  have hdescent : baseEnd_2093336 < baseStart_2093336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093343 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 3, 1, 3]
def baseStart_2093343 : Nat := 118140960795 + 2093343 * 2 ^ 59
def prefixEnd_2093343 : Nat := 4983230072969 + 3 ^ 40 * 2093343 * 2
def baseEnd_2093343 : Nat := 1074891133724908519585397

theorem tailTrace_2093343 : CollatzResearch.WordTrace tailWord_2093343 prefixEnd_2093343 1074891133724908519585397 := by
  unfold tailWord_2093343
  simp only [CollatzResearch.WordTrace]
  refine ⟨76350491655183300366324683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50900327770122200244216455 76350491655183300366324683)
  ·
    refine ⟨114525737482774950549487025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76350491655183300366324683 114525737482774950549487025)
    ·
      refine ⟨85894303112081212912115269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114525737482774950549487025 85894303112081212912115269)
      ·
        refine ⟨16105181833515227421021613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85894303112081212912115269 16105181833515227421021613)
        ·
          refine ⟨6039443187568210282883105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16105181833515227421021613 6039443187568210282883105)
          ·
            refine ⟨4529582390676157712162329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6039443187568210282883105 4529582390676157712162329)
            ·
              refine ⟨3397186793007118284121747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4529582390676157712162329 3397186793007118284121747)
              ·
                refine ⟨5095780189510677426182621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3397186793007118284121747 5095780189510677426182621)
                ·
                  refine ⟨1910917571066504034818483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5095780189510677426182621 1910917571066504034818483)
                  ·
                    refine ⟨2866376356599756052227725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1910917571066504034818483 2866376356599756052227725)
                    ·
                      refine ⟨1074891133724908519585397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2866376356599756052227725 1074891133724908519585397)
                      ·
                        rfl

theorem cell23_2093343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_2093343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093343 prefixEnd_2093343 := by exact prefixLift 2093343
  have htrace : WordTrace (prefixWord ++ tailWord_2093343) baseStart_2093343 baseEnd_2093343 := by
    simpa [prefixWord, tailWord_2093343, baseEnd_2093343] using wordTrace_append hprefix tailTrace_2093343
  have hstable : (prefixWord ++ tailWord_2093343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093343).length < 2 ^ (prefixWord ++ tailWord_2093343).sum := by decide
  have hdescent : baseEnd_2093343 < baseStart_2093343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093359 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 1, 6]
def baseStart_2093359 : Nat := 118140960795 + 2093359 * 2 ^ 59
def prefixEnd_2093359 : Nat := 4983230072969 + 3 ^ 40 * 2093359 * 2
def baseEnd_2093359 : Nat := 358299783138460152328441

theorem tailTrace_2093359 : CollatzResearch.WordTrace tailWord_2093359 prefixEnd_2093359 358299783138460152328441 := by
  unfold tailWord_2093359
  simp only [CollatzResearch.WordTrace]
  refine ⟨76351075223125335098907131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50900716815416890065938087 76351075223125335098907131)
  ·
    refine ⟨114526612834688002648360697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76351075223125335098907131 114526612834688002648360697)
    ·
      refine ⟨85894959626016001986270523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114526612834688002648360697 85894959626016001986270523)
      ·
        refine ⟨128842439439024002979405785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85894959626016001986270523 128842439439024002979405785)
        ·
          refine ⟨96631829579268002234554339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128842439439024002979405785 96631829579268002234554339)
          ·
            refine ⟨144947744368902003351831509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96631829579268002234554339 144947744368902003351831509)
            ·
              refine ⟨3397212758646140703558551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 144947744368902003351831509 3397212758646140703558551)
              ·
                refine ⟨5095819137969211055337827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3397212758646140703558551 5095819137969211055337827)
                ·
                  refine ⟨7643728706953816583006741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095819137969211055337827 7643728706953816583006741)
                  ·
                    refine ⟨358299783138460152328441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7643728706953816583006741 358299783138460152328441)
                    ·
                      rfl

theorem cell23_2093359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 6].length) (baseStart_2093359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093359 prefixEnd_2093359 := by exact prefixLift 2093359
  have htrace : WordTrace (prefixWord ++ tailWord_2093359) baseStart_2093359 baseEnd_2093359 := by
    simpa [prefixWord, tailWord_2093359, baseEnd_2093359] using wordTrace_append hprefix tailTrace_2093359
  have hstable : (prefixWord ++ tailWord_2093359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093359).length < 2 ^ (prefixWord ++ tailWord_2093359).sum := by decide
  have hdescent : baseEnd_2093359 < baseStart_2093359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093379 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 4]
def baseStart_2093379 : Nat := 118140960795 + 2093379 * 2 ^ 59
def prefixEnd_2093379 : Nat := 4983230072969 + 3 ^ 40 * 2093379 * 2
def baseEnd_2093379 : Nat := 1074909619028470378735231

theorem tailTrace_2093379 : CollatzResearch.WordTrace tailWord_2093379 prefixEnd_2093379 1074909619028470378735231 := by
  unfold tailWord_2093379
  simp only [CollatzResearch.WordTrace]
  refine ⟨76351804683052878514635191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50901203122035252343090127 76351804683052878514635191)
  ·
    refine ⟨114527707024579317771952787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76351804683052878514635191 114527707024579317771952787)
    ·
      refine ⟨171791560536868976657929181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114527707024579317771952787 171791560536868976657929181)
      ·
        refine ⟨64421835201325866246723443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171791560536868976657929181 64421835201325866246723443)
        ·
          refine ⟨96632752801988799370085165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64421835201325866246723443 96632752801988799370085165)
          ·
            refine ⟨36237282300745799763781937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96632752801988799370085165 36237282300745799763781937)
            ·
              refine ⟨27177961725559349822836453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36237282300745799763781937 27177961725559349822836453)
              ·
                refine ⟨5095867823542378091781835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27177961725559349822836453 5095867823542378091781835)
                ·
                  refine ⟨7643801735313567137672753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095867823542378091781835 7643801735313567137672753)
                  ·
                    refine ⟨5732851301485175353254565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7643801735313567137672753 5732851301485175353254565)
                    ·
                      refine ⟨1074909619028470378735231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5732851301485175353254565 1074909619028470378735231)
                      ·
                        rfl

theorem cell23_2093379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_2093379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093379 prefixEnd_2093379 := by exact prefixLift 2093379
  have htrace : WordTrace (prefixWord ++ tailWord_2093379) baseStart_2093379 baseEnd_2093379 := by
    simpa [prefixWord, tailWord_2093379, baseEnd_2093379] using wordTrace_append hprefix tailTrace_2093379
  have hstable : (prefixWord ++ tailWord_2093379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093379).length < 2 ^ (prefixWord ++ tailWord_2093379).sum := by decide
  have hdescent : baseEnd_2093379 < baseStart_2093379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093410 : List Nat := [3, 3, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2093410 : Nat := 118140960795 + 2093410 * 2 ^ 59
def prefixEnd_2093410 : Nat := 4983230072969 + 3 ^ 40 * 2093410 * 2
def baseEnd_2093410 : Nat := 358308512309586585815863

theorem tailTrace_2093410 : CollatzResearch.WordTrace tailWord_2093410 prefixEnd_2093410 358308512309586585815863 := by
  unfold tailWord_2093410
  simp only [CollatzResearch.WordTrace]
  refine ⟨19088233836485142702253421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50901956897293713872675789 19088233836485142702253421)
  ·
    refine ⟨7158087688681928513345033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19088233836485142702253421 7158087688681928513345033)
    ·
      refine ⟨5368565766511446385008775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7158087688681928513345033 5368565766511446385008775)
      ·
        refine ⟨8052848649767169577513163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5368565766511446385008775 8052848649767169577513163)
        ·
          refine ⟨12079272974650754366269745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8052848649767169577513163 12079272974650754366269745)
          ·
            refine ⟨9059454730988065774702309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12079272974650754366269745 9059454730988065774702309)
            ·
              refine ⟨1698647762060262332756683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9059454730988065774702309 1698647762060262332756683)
              ·
                refine ⟨2547971643090393499135025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1698647762060262332756683 2547971643090393499135025)
                ·
                  refine ⟨1910978732317795124351269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2547971643090393499135025 1910978732317795124351269)
                  ·
                    refine ⟨358308512309586585815863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1910978732317795124351269 358308512309586585815863)
                    ·
                      rfl

theorem cell23_2093410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2093410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093410 prefixEnd_2093410 := by exact prefixLift 2093410
  have htrace : WordTrace (prefixWord ++ tailWord_2093410) baseStart_2093410 baseEnd_2093410 := by
    simpa [prefixWord, tailWord_2093410, baseEnd_2093410] using wordTrace_append hprefix tailTrace_2093410
  have hstable : (prefixWord ++ tailWord_2093410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093410).length < 2 ^ (prefixWord ++ tailWord_2093410).sum := by decide
  have hdescent : baseEnd_2093410 < baseStart_2093410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093420 : List Nat := [2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 3]
def baseStart_2093420 : Nat := 118140960795 + 2093420 * 2 ^ 59
def prefixEnd_2093420 : Nat := 4983230072969 + 3 ^ 40 * 2093420 * 2
def baseEnd_2093420 : Nat := 1074930671735304718322543

theorem tailTrace_2093420 : CollatzResearch.WordTrace tailWord_2093420 prefixEnd_2093420 1074930671735304718322543 := by
  unfold tailWord_2093420
  simp only [CollatzResearch.WordTrace]
  refine ⟨38176650037952171258438857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50902200050602895011251809 38176650037952171258438857)
  ·
    refine ⟨28632487528464128443829143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38176650037952171258438857 28632487528464128443829143)
    ·
      refine ⟨42948731292696192665743715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28632487528464128443829143 42948731292696192665743715)
      ·
        refine ⟨64423096939044288998615573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42948731292696192665743715 64423096939044288998615573)
        ·
          refine ⟨3019832669017701046810105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64423096939044288998615573 3019832669017701046810105)
          ·
            refine ⟨2264874501763275785107579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3019832669017701046810105 2264874501763275785107579)
            ·
              refine ⟨3397311752644913677661369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264874501763275785107579 3397311752644913677661369)
              ·
                refine ⟨2547983814483685258246027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3397311752644913677661369 2547983814483685258246027)
                ·
                  refine ⟨3821975721725527887369041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2547983814483685258246027 3821975721725527887369041)
                  ·
                    refine ⟨2866481791294145915526781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3821975721725527887369041 2866481791294145915526781)
                    ·
                      refine ⟨1074930671735304718322543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2866481791294145915526781 1074930671735304718322543)
                      ·
                        rfl

theorem cell23_2093420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_2093420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093420 prefixEnd_2093420 := by exact prefixLift 2093420
  have htrace : WordTrace (prefixWord ++ tailWord_2093420) baseStart_2093420 baseEnd_2093420 := by
    simpa [prefixWord, tailWord_2093420, baseEnd_2093420] using wordTrace_append hprefix tailTrace_2093420
  have hstable : (prefixWord ++ tailWord_2093420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093420).length < 2 ^ (prefixWord ++ tailWord_2093420).sum := by decide
  have hdescent : baseEnd_2093420 < baseStart_2093420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093430 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2093430 : Nat := 118140960795 + 2093430 * 2 ^ 59
def prefixEnd_2093430 : Nat := 4983230072969 + 3 ^ 40 * 2093430 * 2
def baseEnd_2093430 : Nat := 1074935806541849679197497

theorem tailTrace_2093430 : CollatzResearch.WordTrace tailWord_2093430 prefixEnd_2093430 1074935806541849679197497 := by
  unfold tailWord_2093430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4772104050366757139046359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50902443203912076149827829 4772104050366757139046359)
  ·
    refine ⟨7158156075550135708569539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4772104050366757139046359 7158156075550135708569539)
    ·
      refine ⟨10737234113325203562854309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7158156075550135708569539 10737234113325203562854309)
      ·
        refine ⟨2013231396248475668035183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10737234113325203562854309 2013231396248475668035183)
        ·
          refine ⟨3019847094372713502052775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013231396248475668035183 3019847094372713502052775)
          ·
            refine ⟨4529770641559070253079163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019847094372713502052775 4529770641559070253079163)
            ·
              refine ⟨6794655962338605379618745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529770641559070253079163 6794655962338605379618745)
              ·
                refine ⟨5095991971753954034714059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6794655962338605379618745 5095991971753954034714059)
                ·
                  refine ⟨7643987957630931052071089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095991971753954034714059 7643987957630931052071089)
                  ·
                    refine ⟨5732990968223198289053317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7643987957630931052071089 5732990968223198289053317)
                    ·
                      refine ⟨1074935806541849679197497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5732990968223198289053317 1074935806541849679197497)
                      ·
                        rfl

theorem cell23_2093430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2093430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093430 prefixEnd_2093430 := by exact prefixLift 2093430
  have htrace : WordTrace (prefixWord ++ tailWord_2093430) baseStart_2093430 baseEnd_2093430 := by
    simpa [prefixWord, tailWord_2093430, baseEnd_2093430] using wordTrace_append hprefix tailTrace_2093430
  have hstable : (prefixWord ++ tailWord_2093430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093430).length < 2 ^ (prefixWord ++ tailWord_2093430).sum := by decide
  have hdescent : baseEnd_2093430 < baseStart_2093430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093466 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 2, 6]
def baseStart_2093466 : Nat := 118140960795 + 2093466 * 2 ^ 59
def prefixEnd_2093466 : Nat := 4983230072969 + 3 ^ 40 * 2093466 * 2
def baseEnd_2093466 : Nat := 358318097281803846115777

theorem tailTrace_2093466 : CollatzResearch.WordTrace tailWord_2093466 prefixEnd_2093466 358318097281803846115777 := by
  unfold tailWord_2093466
  simp only [CollatzResearch.WordTrace]
  refine ⟨19088744458434423093263063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50903318555825128248701501 19088744458434423093263063)
  ·
    refine ⟨28633116687651634639894595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19088744458434423093263063 28633116687651634639894595)
    ·
      refine ⟨42949675031477451959841893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28633116687651634639894595 42949675031477451959841893)
      ·
        refine ⟨8053064068402022242470355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42949675031477451959841893 8053064068402022242470355)
        ·
          refine ⟨12079596102603033363705533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8053064068402022242470355 12079596102603033363705533)
          ·
            refine ⟨4529848538476137511389575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12079596102603033363705533 4529848538476137511389575)
            ·
              refine ⟨6794772807714206267084363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529848538476137511389575 6794772807714206267084363)
              ·
                refine ⟨10192159211571309400626545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6794772807714206267084363 10192159211571309400626545)
                ·
                  refine ⟨7644119408678482050469909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10192159211571309400626545 7644119408678482050469909)
                  ·
                    refine ⟨358318097281803846115777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7644119408678482050469909 358318097281803846115777)
                    ·
                      rfl

theorem cell23_2093466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_2093466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093466 prefixEnd_2093466 := by exact prefixLift 2093466
  have htrace : WordTrace (prefixWord ++ tailWord_2093466) baseStart_2093466 baseEnd_2093466 := by
    simpa [prefixWord, tailWord_2093466, baseEnd_2093466] using wordTrace_append hprefix tailTrace_2093466
  have hstable : (prefixWord ++ tailWord_2093466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093466).length < 2 ^ (prefixWord ++ tailWord_2093466).sum := by decide
  have hdescent : baseEnd_2093466 < baseStart_2093466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093519 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 7]
def baseStart_2093519 : Nat := 118140960795 + 2093519 * 2 ^ 59
def prefixEnd_2093519 : Nat := 4983230072969 + 3 ^ 40 * 2093519 * 2
def baseEnd_2093519 : Nat := 1074981506320099830984587

theorem tailTrace_2093519 : CollatzResearch.WordTrace tailWord_2093519 prefixEnd_2093519 1074981506320099830984587 := by
  unfold tailWord_2093519
  simp only [CollatzResearch.WordTrace]
  refine ⟨76356910902545682424731611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50904607268363788283154407 76356910902545682424731611)
  ·
    refine ⟨114535366353818523637097417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76356910902545682424731611 114535366353818523637097417)
    ·
      refine ⟨85901524765363892727823063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114535366353818523637097417 85901524765363892727823063)
      ·
        refine ⟨128852287148045839091734595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85901524765363892727823063 128852287148045839091734595)
        ·
          refine ⟨193278430722068758637601893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128852287148045839091734595 193278430722068758637601893)
          ·
            refine ⟨36239705760387892244550355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193278430722068758637601893 36239705760387892244550355)
            ·
              refine ⟨54359558640581838366825533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36239705760387892244550355 54359558640581838366825533)
              ·
                refine ⟨20384834490218189387559575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54359558640581838366825533 20384834490218189387559575)
                ·
                  refine ⟨30577251735327284081339363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20384834490218189387559575 30577251735327284081339363)
                  ·
                    refine ⟨45865877602990926122009045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30577251735327284081339363 45865877602990926122009045)
                    ·
                      refine ⟨1074981506320099830984587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45865877602990926122009045 1074981506320099830984587)
                      ·
                        rfl

theorem cell23_2093519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_2093519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093519 prefixEnd_2093519 := by exact prefixLift 2093519
  have htrace : WordTrace (prefixWord ++ tailWord_2093519) baseStart_2093519 baseEnd_2093519 := by
    simpa [prefixWord, tailWord_2093519, baseEnd_2093519] using wordTrace_append hprefix tailTrace_2093519
  have hstable : (prefixWord ++ tailWord_2093519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093519).length < 2 ^ (prefixWord ++ tailWord_2093519).sum := by decide
  have hdescent : baseEnd_2093519 < baseStart_2093519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093524 : List Nat := [2, 4, 1, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_2093524 : Nat := 118140960795 + 2093524 * 2 ^ 59
def prefixEnd_2093524 : Nat := 4983230072969 + 3 ^ 40 * 2093524 * 2
def baseEnd_2093524 : Nat := 1074984073723372311422065

theorem tailTrace_2093524 : CollatzResearch.WordTrace tailWord_2093524 prefixEnd_2093524 1074984073723372311422065 := by
  unfold tailWord_2093524
  simp only [CollatzResearch.WordTrace]
  refine ⟨38178546633763784139331813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50904728845018378852442417 38178546633763784139331813)
  ·
    refine ⟨7158477493830709526124715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38178546633763784139331813 7158477493830709526124715)
    ·
      refine ⟨10737716240746064289187073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7158477493830709526124715 10737716240746064289187073)
      ·
        refine ⟨8053287180559548216890305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10737716240746064289187073 8053287180559548216890305)
        ·
          refine ⟨6039965385419661162667729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8053287180559548216890305 6039965385419661162667729)
          ·
            refine ⟨4529974039064745872000797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6039965385419661162667729 4529974039064745872000797)
            ·
              refine ⟨1698740264649279702000299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4529974039064745872000797 1698740264649279702000299)
              ·
                refine ⟨2548110396973919553000449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1698740264649279702000299 2548110396973919553000449)
                ·
                  refine ⟨1911082797730439664750337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2548110396973919553000449 1911082797730439664750337)
                  ·
                    refine ⟨1433312098297829748562753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1911082797730439664750337 1433312098297829748562753)
                    ·
                      refine ⟨1074984073723372311422065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1433312098297829748562753 1074984073723372311422065)
                      ·
                        rfl

theorem cell23_2093524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_2093524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093524 prefixEnd_2093524 := by exact prefixLift 2093524
  have htrace : WordTrace (prefixWord ++ tailWord_2093524) baseStart_2093524 baseEnd_2093524 := by
    simpa [prefixWord, tailWord_2093524, baseEnd_2093524] using wordTrace_append hprefix tailTrace_2093524
  have hstable : (prefixWord ++ tailWord_2093524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093524).length < 2 ^ (prefixWord ++ tailWord_2093524).sum := by decide
  have hdescent : baseEnd_2093524 < baseStart_2093524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093570 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2093570 : Nat := 118140960795 + 2093570 * 2 ^ 59
def prefixEnd_2093570 : Nat := 4983230072969 + 3 ^ 40 * 2093570 * 2
def baseEnd_2093570 : Nat := 1075007693833479131446853

theorem tailTrace_2093570 : CollatzResearch.WordTrace tailWord_2093570 prefixEnd_2093570 1075007693833479131446853 := by
  unfold tailWord_2093570
  simp only [CollatzResearch.WordTrace]
  refine ⟨19089692756340229533709541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50905847350240612089892109 19089692756340229533709541)
  ·
    refine ⟨3579317391813793037570539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19089692756340229533709541 3579317391813793037570539)
    ·
      refine ⟨5368976087720689556355809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3579317391813793037570539 5368976087720689556355809)
      ·
        refine ⟨4026732065790517167266857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5368976087720689556355809 4026732065790517167266857)
        ·
          refine ⟨3020049049342887875450143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4026732065790517167266857 3020049049342887875450143)
          ·
            refine ⟨4530073574014331813175215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3020049049342887875450143 4530073574014331813175215)
            ·
              refine ⟨6795110361021497719762823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4530073574014331813175215 6795110361021497719762823)
              ·
                refine ⟨10192665541532246579644235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6795110361021497719762823 10192665541532246579644235)
                ·
                  refine ⟨15288998312298369869466353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10192665541532246579644235 15288998312298369869466353)
                  ·
                    refine ⟨11466748734223777402099765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15288998312298369869466353 11466748734223777402099765)
                    ·
                      refine ⟨1075007693833479131446853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11466748734223777402099765 1075007693833479131446853)
                      ·
                        rfl

theorem cell23_2093570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2093570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093570 prefixEnd_2093570 := by exact prefixLift 2093570
  have htrace : WordTrace (prefixWord ++ tailWord_2093570) baseStart_2093570 baseEnd_2093570 := by
    simpa [prefixWord, tailWord_2093570, baseEnd_2093570] using wordTrace_append hprefix tailTrace_2093570
  have hstable : (prefixWord ++ tailWord_2093570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093570).length < 2 ^ (prefixWord ++ tailWord_2093570).sum := by decide
  have hdescent : baseEnd_2093570 < baseStart_2093570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093573 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 3, 4]
def baseStart_2093573 : Nat := 118140960795 + 2093573 * 2 ^ 59
def prefixEnd_2093573 : Nat := 4983230072969 + 3 ^ 40 * 2093573 * 2
def baseEnd_2093573 : Nat := 358336411425147539903113

theorem tailTrace_2093573 : CollatzResearch.WordTrace tailWord_2093573 prefixEnd_2093573 358336411425147539903113 := by
  unfold tailWord_2093573
  simp only [CollatzResearch.WordTrace]
  refine ⟨76358880444350049647197373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50905920296233366431464915 76358880444350049647197373)
  ·
    refine ⟨28634580166631268617699015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76358880444350049647197373 28634580166631268617699015)
    ·
      refine ⟨42951870249946902926548523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28634580166631268617699015 42951870249946902926548523)
      ·
        refine ⟨64427805374920354389822785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42951870249946902926548523 64427805374920354389822785)
        ·
          refine ⟨48320854031190265792367089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64427805374920354389822785 48320854031190265792367089)
          ·
            refine ⟨36240640523392699344275317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48320854031190265792367089 36240640523392699344275317)
            ·
              refine ⟨3397560049068065563525811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36240640523392699344275317 3397560049068065563525811)
              ·
                refine ⟨5096340073602098345288717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3397560049068065563525811 5096340073602098345288717)
                ·
                  refine ⟨1911127527600786879483269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5096340073602098345288717 1911127527600786879483269)
                  ·
                    refine ⟨358336411425147539903113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1911127527600786879483269 358336411425147539903113)
                    ·
                      rfl

theorem cell23_2093573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_2093573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093573 prefixEnd_2093573 := by exact prefixLift 2093573
  have htrace : WordTrace (prefixWord ++ tailWord_2093573) baseStart_2093573 baseEnd_2093573 := by
    simpa [prefixWord, tailWord_2093573, baseEnd_2093573] using wordTrace_append hprefix tailTrace_2093573
  have hstable : (prefixWord ++ tailWord_2093573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093573).length < 2 ^ (prefixWord ++ tailWord_2093573).sum := by decide
  have hdescent : baseEnd_2093573 < baseStart_2093573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093633 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2093633 : Nat := 118140960795 + 2093633 * 2 ^ 59
def prefixEnd_2093633 : Nat := 4983230072969 + 3 ^ 40 * 2093633 * 2
def baseEnd_2093633 : Nat := 358346681038237461653021

theorem tailTrace_2093633 : CollatzResearch.WordTrace tailWord_2093633 prefixEnd_2093633 358346681038237461653021 := by
  unfold tailWord_2093633
  simp only [CollatzResearch.WordTrace]
  refine ⟨76361068824132679894381553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50907379216088453262921035 76361068824132679894381553)
  ·
    refine ⟨57270801618099509920786165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76361068824132679894381553 57270801618099509920786165)
    ·
      refine ⟨5369137651696829055073703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57270801618099509920786165 5369137651696829055073703)
      ·
        refine ⟨8053706477545243582610555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5369137651696829055073703 8053706477545243582610555)
        ·
          refine ⟨12080559716317865373915833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8053706477545243582610555 12080559716317865373915833)
          ·
            refine ⟨9060419787238399030436875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12080559716317865373915833 9060419787238399030436875)
            ·
              refine ⟨13590629680857598545655313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9060419787238399030436875 13590629680857598545655313)
              ·
                refine ⟨10192972260643198909241485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13590629680857598545655313 10192972260643198909241485)
                ·
                  refine ⟨3822364597741199590965557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10192972260643198909241485 3822364597741199590965557)
                  ·
                    refine ⟨358346681038237461653021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3822364597741199590965557 358346681038237461653021)
                    ·
                      rfl

theorem cell23_2093633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2093633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093633 prefixEnd_2093633 := by exact prefixLift 2093633
  have htrace : WordTrace (prefixWord ++ tailWord_2093633) baseStart_2093633 baseEnd_2093633 := by
    simpa [prefixWord, tailWord_2093633, baseEnd_2093633] using wordTrace_append hprefix tailTrace_2093633
  have hstable : (prefixWord ++ tailWord_2093633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093633).length < 2 ^ (prefixWord ++ tailWord_2093633).sum := by decide
  have hdescent : baseEnd_2093633 < baseStart_2093633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093653 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_2093653 : Nat := 118140960795 + 2093653 * 2 ^ 59
def prefixEnd_2093653 : Nat := 4983230072969 + 3 ^ 40 * 2093653 * 2
def baseEnd_2093653 : Nat := 1075050312727802306708971

theorem tailTrace_2093653 : CollatzResearch.WordTrace tailWord_2093653 prefixEnd_2093653 1075050312727802306708971 := by
  unfold tailWord_2093653
  simp only [CollatzResearch.WordTrace]
  refine ⟨76361798284060223310109613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50907865522706815540073075 76361798284060223310109613)
  ·
    refine ⟨28635674356522583741291105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76361798284060223310109613 28635674356522583741291105)
    ·
      refine ⟨21476755767391937805968329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28635674356522583741291105 21476755767391937805968329)
      ·
        refine ⟨16107566825543953354476247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21476755767391937805968329 16107566825543953354476247)
        ·
          refine ⟨24161350238315930031714371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16107566825543953354476247 24161350238315930031714371)
          ·
            refine ⟨36242025357473895047571557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24161350238315930031714371 36242025357473895047571557)
            ·
              refine ⟨6795379754526355321419667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36242025357473895047571557 6795379754526355321419667)
              ·
                refine ⟨10193069631789532982129501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6795379754526355321419667 10193069631789532982129501)
                ·
                  refine ⟨3822401111921074868298563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10193069631789532982129501 3822401111921074868298563)
                  ·
                    refine ⟨5733601667881612302447845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3822401111921074868298563 5733601667881612302447845)
                    ·
                      refine ⟨1075050312727802306708971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5733601667881612302447845 1075050312727802306708971)
                      ·
                        rfl

theorem cell23_2093653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_2093653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093653 prefixEnd_2093653 := by exact prefixLift 2093653
  have htrace : WordTrace (prefixWord ++ tailWord_2093653) baseStart_2093653 baseEnd_2093653 := by
    simpa [prefixWord, tailWord_2093653, baseEnd_2093653] using wordTrace_append hprefix tailTrace_2093653
  have hstable : (prefixWord ++ tailWord_2093653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093653).length < 2 ^ (prefixWord ++ tailWord_2093653).sum := by decide
  have hdescent : baseEnd_2093653 < baseStart_2093653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093680 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 4, 4]
def baseStart_2093680 : Nat := 118140960795 + 2093680 * 2 ^ 59
def prefixEnd_2093680 : Nat := 4983230072969 + 3 ^ 40 * 2093680 * 2
def baseEnd_2093680 : Nat := 358354725568491233690449

theorem tailTrace_2093680 : CollatzResearch.WordTrace tailWord_2093680 prefixEnd_2093680 358354725568491233690449 := by
  unfold tailWord_2093680
  simp only [CollatzResearch.WordTrace]
  refine ⟨38181391527481203460671247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50908522036641604614228329 38181391527481203460671247)
  ·
    refine ⟨57272087291221805191006871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38181391527481203460671247 57272087291221805191006871)
    ·
      refine ⟨85908130936832707786510307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57272087291221805191006871 85908130936832707786510307)
      ·
        refine ⟨128862196405249061679765461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85908130936832707786510307 128862196405249061679765461)
        ·
          refine ⟨3020207728248024883119503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 128862196405249061679765461 3020207728248024883119503)
          ·
            refine ⟨4530311592372037324679255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3020207728248024883119503 4530311592372037324679255)
            ·
              refine ⟨6795467388558055987018883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4530311592372037324679255 6795467388558055987018883)
              ·
                refine ⟨10193201082837083980528325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6795467388558055987018883 10193201082837083980528325)
                ·
                  refine ⟨1911225203031953246349061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10193201082837083980528325 1911225203031953246349061)
                  ·
                    refine ⟨358354725568491233690449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1911225203031953246349061 358354725568491233690449)
                    ·
                      rfl

theorem cell23_2093680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 4, 4].length) (baseStart_2093680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093680 prefixEnd_2093680 := by exact prefixLift 2093680
  have htrace : WordTrace (prefixWord ++ tailWord_2093680) baseStart_2093680 baseEnd_2093680 := by
    simpa [prefixWord, tailWord_2093680, baseEnd_2093680] using wordTrace_append hprefix tailTrace_2093680
  have hstable : (prefixWord ++ tailWord_2093680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093680).length < 2 ^ (prefixWord ++ tailWord_2093680).sum := by decide
  have hdescent : baseEnd_2093680 < baseStart_2093680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093697 : List Nat := [1, 2, 4, 2, 1, 1, 5, 1, 2, 4]
def baseStart_2093697 : Nat := 118140960795 + 2093697 * 2 ^ 59
def prefixEnd_2093697 : Nat := 4983230072969 + 3 ^ 40 * 2093697 * 2
def baseEnd_2093697 : Nat := 358357635292200044852923

theorem tailTrace_2093697 : CollatzResearch.WordTrace tailWord_2093697 prefixEnd_2093697 358357635292200044852923 := by
  unfold tailWord_2093697
  simp only [CollatzResearch.WordTrace]
  refine ⟨76363403095900818824711345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50908935397267212549807563 76363403095900818824711345)
  ·
    refine ⟨57272552321925614118533509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76363403095900818824711345 57272552321925614118533509)
    ·
      refine ⟨10738603560361052647225033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57272552321925614118533509 10738603560361052647225033)
      ·
        refine ⟨8053952670270789485418775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10738603560361052647225033 8053952670270789485418775)
        ·
          refine ⟨12080929005406184228128163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8053952670270789485418775 12080929005406184228128163)
          ·
            refine ⟨18121393508109276342192245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12080929005406184228128163 18121393508109276342192245)
            ·
              refine ⟨1698880641385244657080523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18121393508109276342192245 1698880641385244657080523)
              ·
                refine ⟨2548320962077866985620785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1698880641385244657080523 2548320962077866985620785)
                ·
                  refine ⟨1911240721558400239215589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2548320962077866985620785 1911240721558400239215589)
                  ·
                    refine ⟨358357635292200044852923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1911240721558400239215589 358357635292200044852923)
                    ·
                      rfl

theorem cell23_2093697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_2093697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093697 prefixEnd_2093697 := by exact prefixLift 2093697
  have htrace : WordTrace (prefixWord ++ tailWord_2093697) baseStart_2093697 baseEnd_2093697 := by
    simpa [prefixWord, tailWord_2093697, baseEnd_2093697] using wordTrace_append hprefix tailTrace_2093697
  have hstable : (prefixWord ++ tailWord_2093697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093697).length < 2 ^ (prefixWord ++ tailWord_2093697).sum := by decide
  have hdescent : baseEnd_2093697 < baseStart_2093697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093700 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_2093700 : Nat := 118140960795 + 2093700 * 2 ^ 59
def prefixEnd_2093700 : Nat := 4983230072969 + 3 ^ 40 * 2093700 * 2
def baseEnd_2093700 : Nat := 1075074446318563622821255

theorem tailTrace_2093700 : CollatzResearch.WordTrace tailWord_2093700 prefixEnd_2093700 1075074446318563622821255 := by
  unfold tailWord_2093700
  simp only [CollatzResearch.WordTrace]
  refine ⟨38181756257444975168535277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50909008343259966891380369 38181756257444975168535277)
  ·
    refine ⟨14318158596541865688200729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38181756257444975168535277 14318158596541865688200729)
    ·
      refine ⟨10738618947406399266150547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14318158596541865688200729 10738618947406399266150547)
      ·
        refine ⟨16107928421109598899225821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10738618947406399266150547 16107928421109598899225821)
        ·
          refine ⟨6040473157916099587209683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16107928421109598899225821 6040473157916099587209683)
          ·
            refine ⟨9060709736874149380814525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6040473157916099587209683 9060709736874149380814525)
            ·
              refine ⟨3397766151327806017805447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9060709736874149380814525 3397766151327806017805447)
              ·
                refine ⟨5096649226991709026708171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3397766151327806017805447 5096649226991709026708171)
                ·
                  refine ⟨7644973840487563540062257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5096649226991709026708171 7644973840487563540062257)
                  ·
                    refine ⟨5733730380365672655046693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7644973840487563540062257 5733730380365672655046693)
                    ·
                      refine ⟨1075074446318563622821255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5733730380365672655046693 1075074446318563622821255)
                      ·
                        rfl

theorem cell23_2093700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_2093700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093700 prefixEnd_2093700 := by exact prefixLift 2093700
  have htrace : WordTrace (prefixWord ++ tailWord_2093700) baseStart_2093700 baseEnd_2093700 := by
    simpa [prefixWord, tailWord_2093700, baseEnd_2093700] using wordTrace_append hprefix tailTrace_2093700
  have hstable : (prefixWord ++ tailWord_2093700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093700).length < 2 ^ (prefixWord ++ tailWord_2093700).sum := by decide
  have hdescent : baseEnd_2093700 < baseStart_2093700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093720 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 6, 1, 3]
def baseStart_2093720 : Nat := 118140960795 + 2093720 * 2 ^ 59
def prefixEnd_2093720 : Nat := 4983230072969 + 3 ^ 40 * 2093720 * 2
def baseEnd_2093720 : Nat := 1075084715931653544571163

theorem tailTrace_2093720 : CollatzResearch.WordTrace tailWord_2093720 prefixEnd_2093720 1075084715931653544571163 := by
  unfold tailWord_2093720
  simp only [CollatzResearch.WordTrace]
  refine ⟨38182120987408746876399307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50909494649878329168532409 38182120987408746876399307)
  ·
    refine ⟨57273181481113120314598961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38182120987408746876399307 57273181481113120314598961)
    ·
      refine ⟨42954886110834840235949221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57273181481113120314598961 42954886110834840235949221)
      ·
        refine ⟨8054041145781532544240479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42954886110834840235949221 8054041145781532544240479)
        ·
          refine ⟨12081061718672298816360719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054041145781532544240479 12081061718672298816360719)
          ·
            refine ⟨18121592578008448224541079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12081061718672298816360719 18121592578008448224541079)
            ·
              refine ⟨27182388867012672336811619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18121592578008448224541079 27182388867012672336811619)
              ·
                refine ⟨40773583300519008505217429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27182388867012672336811619 40773583300519008505217429)
                ·
                  refine ⟨1911261717211828523682067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40773583300519008505217429 1911261717211828523682067)
                  ·
                    refine ⟨2866892575817742785523101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1911261717211828523682067 2866892575817742785523101)
                    ·
                      refine ⟨1075084715931653544571163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2866892575817742785523101 1075084715931653544571163)
                      ·
                        rfl

theorem cell23_2093720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_2093720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093720 prefixEnd_2093720 := by exact prefixLift 2093720
  have htrace : WordTrace (prefixWord ++ tailWord_2093720) baseStart_2093720 baseEnd_2093720 := by
    simpa [prefixWord, tailWord_2093720, baseEnd_2093720] using wordTrace_append hprefix tailTrace_2093720
  have hstable : (prefixWord ++ tailWord_2093720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093720).length < 2 ^ (prefixWord ++ tailWord_2093720).sum := by decide
  have hdescent : baseEnd_2093720 < baseStart_2093720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093738 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_2093738 : Nat := 118140960795 + 2093738 * 2 ^ 59
def prefixEnd_2093738 : Nat := 4983230072969 + 3 ^ 40 * 2093738 * 2
def baseEnd_2093738 : Nat := 1075093958583434474146081

theorem tailTrace_2093738 : CollatzResearch.WordTrace tailWord_2093738 prefixEnd_2093738 1075093958583434474146081 := by
  unfold tailWord_2093738
  simp only [CollatzResearch.WordTrace]
  refine ⟨19091224622188070706738467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50909932325834855217969245 19091224622188070706738467)
  ·
    refine ⟨28636836933282106060107701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19091224622188070706738467 28636836933282106060107701)
    ·
      refine ⟨2684703462495197443135097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28636836933282106060107701 2684703462495197443135097)
      ·
        refine ⟨2013527596871398082351323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2684703462495197443135097 2013527596871398082351323)
        ·
          refine ⟨3020291395307097123526985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013527596871398082351323 3020291395307097123526985)
          ·
            refine ⟨2265218546480322842645239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3020291395307097123526985 2265218546480322842645239)
            ·
              refine ⟨3397827819720484263967859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265218546480322842645239 3397827819720484263967859)
              ·
                refine ⟨5096741729580726395951789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3397827819720484263967859 5096741729580726395951789)
                ·
                  refine ⟨1911278148592772398481921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5096741729580726395951789 1911278148592772398481921)
                  ·
                    refine ⟨1433458611444579298861441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1911278148592772398481921 1433458611444579298861441)
                    ·
                      refine ⟨1075093958583434474146081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1433458611444579298861441 1075093958583434474146081)
                      ·
                        rfl

theorem cell23_2093738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_2093738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093738 prefixEnd_2093738 := by exact prefixLift 2093738
  have htrace : WordTrace (prefixWord ++ tailWord_2093738) baseStart_2093738 baseEnd_2093738 := by
    simpa [prefixWord, tailWord_2093738, baseEnd_2093738] using wordTrace_append hprefix tailTrace_2093738
  have hstable : (prefixWord ++ tailWord_2093738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093738).length < 2 ^ (prefixWord ++ tailWord_2093738).sum := by decide
  have hdescent : baseEnd_2093738 < baseStart_2093738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093764 : List Nat := [2, 3, 3, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_2093764 : Nat := 118140960795 + 2093764 * 2 ^ 59
def prefixEnd_2093764 : Nat := 4983230072969 + 3 ^ 40 * 2093764 * 2
def baseEnd_2093764 : Nat := 1075107309080451372420961

theorem tailTrace_2093764 : CollatzResearch.WordTrace tailWord_2093764 prefixEnd_2093764 1075107309080451372420961 := by
  unfold tailWord_2093764
  simp only [CollatzResearch.WordTrace]
  refine ⟨38182923393329044633700173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50910564524438726178266897 38182923393329044633700173)
  ·
    refine ⟨14318596272498391737637565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38182923393329044633700173 14318596272498391737637565)
    ·
      refine ⟨5369473602186896901614087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14318596272498391737637565 5369473602186896901614087)
      ·
        refine ⟨8054210403280345352421131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5369473602186896901614087 8054210403280345352421131)
        ·
          refine ⟨12081315604920518028631697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054210403280345352421131 12081315604920518028631697)
          ·
            refine ⟨9060986703690388521473773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12081315604920518028631697 9060986703690388521473773)
            ·
              refine ⟨3397870013883895695552665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9060986703690388521473773 3397870013883895695552665)
              ·
                refine ⟨2548402510412921771664499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3397870013883895695552665 2548402510412921771664499)
                ·
                  refine ⟨3822603765619382657496749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2548402510412921771664499 3822603765619382657496749)
                  ·
                    refine ⟨1433476412107268496561281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3822603765619382657496749 1433476412107268496561281)
                    ·
                      refine ⟨1075107309080451372420961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1433476412107268496561281 1075107309080451372420961)
                      ·
                        rfl

theorem cell23_2093764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_2093764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093764 prefixEnd_2093764 := by exact prefixLift 2093764
  have htrace : WordTrace (prefixWord ++ tailWord_2093764) baseStart_2093764 baseEnd_2093764 := by
    simpa [prefixWord, tailWord_2093764, baseEnd_2093764] using wordTrace_append hprefix tailTrace_2093764
  have hstable : (prefixWord ++ tailWord_2093764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093764).length < 2 ^ (prefixWord ++ tailWord_2093764).sum := by decide
  have hdescent : baseEnd_2093764 < baseStart_2093764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093810 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_2093810 : Nat := 118140960795 + 2093810 * 2 ^ 59
def prefixEnd_2093810 : Nat := 4983230072969 + 3 ^ 40 * 2093810 * 2
def baseEnd_2093810 : Nat := 1075130929190558192445749

theorem tailTrace_2093810 : CollatzResearch.WordTrace tailWord_2093810 prefixEnd_2093810 1075130929190558192445749 := by
  unfold tailWord_2093810
  simp only [CollatzResearch.WordTrace]
  refine ⟨19091881136122859780893721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50911683029660959415716589 19091881136122859780893721)
  ·
    refine ⟨14318910852092144835670291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19091881136122859780893721 14318910852092144835670291)
    ·
      refine ⟨21478366278138217253505437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14318910852092144835670291 21478366278138217253505437)
      ·
        refine ⟨8054387354301831470064539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21478366278138217253505437 8054387354301831470064539)
        ·
          refine ⟨12081581031452747205096809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054387354301831470064539 12081581031452747205096809)
          ·
            refine ⟨9061185773589560403822607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12081581031452747205096809 9061185773589560403822607)
            ·
              refine ⟨13591778660384340605733911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9061185773589560403822607 13591778660384340605733911)
              ·
                refine ⟨20387667990576510908600867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13591778660384340605733911 20387667990576510908600867)
                ·
                  refine ⟨30581501985864766362901301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20387667990576510908600867 30581501985864766362901301)
                  ·
                    refine ⟨2867015811174821846521997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30581501985864766362901301 2867015811174821846521997)
                    ·
                      refine ⟨1075130929190558192445749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2867015811174821846521997 1075130929190558192445749)
                      ·
                        rfl

theorem cell23_2093810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_2093810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093810 prefixEnd_2093810 := by exact prefixLift 2093810
  have htrace : WordTrace (prefixWord ++ tailWord_2093810) baseStart_2093810 baseEnd_2093810 := by
    simpa [prefixWord, tailWord_2093810, baseEnd_2093810] using wordTrace_append hprefix tailTrace_2093810
  have hstable : (prefixWord ++ tailWord_2093810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093810).length < 2 ^ (prefixWord ++ tailWord_2093810).sum := by decide
  have hdescent : baseEnd_2093810 < baseStart_2093810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093850 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4]
def baseStart_2093850 : Nat := 118140960795 + 2093850 * 2 ^ 59
def prefixEnd_2093850 : Nat := 4983230072969 + 3 ^ 40 * 2093850 * 2
def baseEnd_2093850 : Nat := 1075151468416738035945565

theorem tailTrace_2093850 : CollatzResearch.WordTrace tailWord_2093850 prefixEnd_2093850 1075151468416738035945565 := by
  unfold tailWord_2093850
  simp only [CollatzResearch.WordTrace]
  refine ⟨19092245866086631488757751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50912655642897683970020669 19092245866086631488757751)
  ·
    refine ⟨28638368799129947233136627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19092245866086631488757751 28638368799129947233136627)
    ·
      refine ⟨42957553198694920849704941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28638368799129947233136627 42957553198694920849704941)
      ·
        refine ⟨16109082449510595318639353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42957553198694920849704941 16109082449510595318639353)
        ·
          refine ⟨12081811837132946488979515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16109082449510595318639353 12081811837132946488979515)
          ·
            refine ⟨18122717755699419733469273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12081811837132946488979515 18122717755699419733469273)
            ·
              refine ⟨13592038316774564800101955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18122717755699419733469273 13592038316774564800101955)
              ·
                refine ⟨20388057475161847200152933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13592038316774564800101955 20388057475161847200152933)
                ·
                  refine ⟨3822760776592846350028675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20388057475161847200152933 3822760776592846350028675)
                  ·
                    refine ⟨5734141164889269525043013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3822760776592846350028675 5734141164889269525043013)
                    ·
                      refine ⟨1075151468416738035945565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5734141164889269525043013 1075151468416738035945565)
                      ·
                        rfl

theorem cell23_2093850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_2093850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093850 prefixEnd_2093850 := by exact prefixLift 2093850
  have htrace : WordTrace (prefixWord ++ tailWord_2093850) baseStart_2093850 baseEnd_2093850 := by
    simpa [prefixWord, tailWord_2093850, baseEnd_2093850] using wordTrace_append hprefix tailTrace_2093850
  have hstable : (prefixWord ++ tailWord_2093850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093850).length < 2 ^ (prefixWord ++ tailWord_2093850).sum := by decide
  have hdescent : baseEnd_2093850 < baseStart_2093850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093877 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 3, 4]
def baseStart_2093877 : Nat := 118140960795 + 2093877 * 2 ^ 59
def prefixEnd_2093877 : Nat := 4983230072969 + 3 ^ 40 * 2093877 * 2
def baseEnd_2093877 : Nat := 358388444131469810102647

theorem tailTrace_2093877 : CollatzResearch.WordTrace tailWord_2093877 prefixEnd_2093877 358388444131469810102647 := by
  unfold tailWord_2093877
  simp only [CollatzResearch.WordTrace]
  refine ⟨76369968235248709566263885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50913312156832473044175923 76369968235248709566263885)
  ·
    refine ⟨28638738088218266087348957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76369968235248709566263885 28638738088218266087348957)
    ·
      refine ⟨10739526783081849782755859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28638738088218266087348957 10739526783081849782755859)
      ·
        refine ⟨16109290174622774674133789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10739526783081849782755859 16109290174622774674133789)
        ·
          refine ⟨6040983815483540502800171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16109290174622774674133789 6040983815483540502800171)
          ·
            refine ⟨9061475723225310754200257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6040983815483540502800171 9061475723225310754200257)
            ·
              refine ⟨6796106792418983065650193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9061475723225310754200257 6796106792418983065650193)
              ·
                refine ⟨5097080094314237299237645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6796106792418983065650193 5097080094314237299237645)
                ·
                  refine ⟨1911405035367838987214117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5097080094314237299237645 1911405035367838987214117)
                  ·
                    refine ⟨358388444131469810102647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1911405035367838987214117 358388444131469810102647)
                    ·
                      rfl

theorem cell23_2093877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_2093877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093877 prefixEnd_2093877 := by exact prefixLift 2093877
  have htrace : WordTrace (prefixWord ++ tailWord_2093877) baseStart_2093877 baseEnd_2093877 := by
    simpa [prefixWord, tailWord_2093877, baseEnd_2093877] using wordTrace_append hprefix tailTrace_2093877
  have hstable : (prefixWord ++ tailWord_2093877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093877).length < 2 ^ (prefixWord ++ tailWord_2093877).sum := by decide
  have hdescent : baseEnd_2093877 < baseStart_2093877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093893 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_2093893 : Nat := 118140960795 + 2093893 * 2 ^ 59
def prefixEnd_2093893 : Nat := 4983230072969 + 3 ^ 40 * 2093893 * 2
def baseEnd_2093893 : Nat := 1075173548084881367707867

theorem tailTrace_2093893 : CollatzResearch.WordTrace tailWord_2093893 prefixEnd_2093893 1075173548084881367707867 := by
  unfold tailWord_2093893
  simp only [CollatzResearch.WordTrace]
  refine ⟨76370551803190744298846333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50913701202127162865897555 76370551803190744298846333)
  ·
    refine ⟨28638956926196529112067375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76370551803190744298846333 28638956926196529112067375)
    ·
      refine ⟨42958435389294793668101063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28638956926196529112067375 42958435389294793668101063)
      ·
        refine ⟨64437653083942190502151595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42958435389294793668101063 64437653083942190502151595)
        ·
          refine ⟨96656479625913285753227393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64437653083942190502151595 96656479625913285753227393)
          ·
            refine ⟨72492359719434964314920545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96656479625913285753227393 72492359719434964314920545)
            ·
              refine ⟨54369269789576223236190409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72492359719434964314920545 54369269789576223236190409)
              ·
                refine ⟨40776952342182167427142807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54369269789576223236190409 40776952342182167427142807)
                ·
                  refine ⟨61165428513273251140714211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40776952342182167427142807 61165428513273251140714211)
                  ·
                    refine ⟨91748142769909876711071317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61165428513273251140714211 91748142769909876711071317)
                    ·
                      refine ⟨1075173548084881367707867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 91748142769909876711071317 1075173548084881367707867)
                      ·
                        rfl

theorem cell23_2093893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_2093893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093893 prefixEnd_2093893 := by exact prefixLift 2093893
  have htrace : WordTrace (prefixWord ++ tailWord_2093893) baseStart_2093893 baseEnd_2093893 := by
    simpa [prefixWord, tailWord_2093893, baseEnd_2093893] using wordTrace_append hprefix tailTrace_2093893
  have hstable : (prefixWord ++ tailWord_2093893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093893).length < 2 ^ (prefixWord ++ tailWord_2093893).sum := by decide
  have hdescent : baseEnd_2093893 < baseStart_2093893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093911 : List Nat := [1, 1, 3, 2, 4, 2, 3, 2, 1, 4]
def baseStart_2093911 : Nat := 118140960795 + 2093911 * 2 ^ 59
def prefixEnd_2093911 : Nat := 4983230072969 + 3 ^ 40 * 2093911 * 2
def baseEnd_2093911 : Nat := 358394263578887432427595

theorem tailTrace_2093911 : CollatzResearch.WordTrace tailWord_2093911 prefixEnd_2093911 358394263578887432427595 := by
  unfold tailWord_2093911
  simp only [CollatzResearch.WordTrace]
  refine ⟨76371208317125533373001587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50914138878083688915334391 76371208317125533373001587)
  ·
    refine ⟨114556812475688300059502381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76371208317125533373001587 114556812475688300059502381)
    ·
      refine ⟨42958804678383112522313393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114556812475688300059502381 42958804678383112522313393)
      ·
        refine ⟨32219103508787334391735045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42958804678383112522313393 32219103508787334391735045)
        ·
          refine ⟨6041081907897625198450321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32219103508787334391735045 6041081907897625198450321)
          ·
            refine ⟨4530811430923218898837741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6041081907897625198450321 4530811430923218898837741)
            ·
              refine ⟨1699054286596207087064153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4530811430923218898837741 1699054286596207087064153)
              ·
                refine ⟨1274290714947155315298115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1699054286596207087064153 1274290714947155315298115)
                ·
                  refine ⟨1911436072420732972947173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274290714947155315298115 1911436072420732972947173)
                  ·
                    refine ⟨358394263578887432427595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1911436072420732972947173 358394263578887432427595)
                    ·
                      rfl

theorem cell23_2093911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_2093911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093911 prefixEnd_2093911 := by exact prefixLift 2093911
  have htrace : WordTrace (prefixWord ++ tailWord_2093911) baseStart_2093911 baseEnd_2093911 := by
    simpa [prefixWord, tailWord_2093911, baseEnd_2093911] using wordTrace_append hprefix tailTrace_2093911
  have hstable : (prefixWord ++ tailWord_2093911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093911).length < 2 ^ (prefixWord ++ tailWord_2093911).sum := by decide
  have hdescent : baseEnd_2093911 < baseStart_2093911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093920 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 3, 5]
def baseStart_2093920 : Nat := 118140960795 + 2093920 * 2 ^ 59
def prefixEnd_2093920 : Nat := 4983230072969 + 3 ^ 40 * 2093920 * 2
def baseEnd_2093920 : Nat := 358395804020850920690081

theorem tailTrace_2093920 : CollatzResearch.WordTrace tailWord_2093920 prefixEnd_2093920 358395804020850920690081 := by
  unfold tailWord_2093920
  simp only [CollatzResearch.WordTrace]
  refine ⟨38185768287046463955039607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50914357716061951940052809 38185768287046463955039607)
  ·
    refine ⟨57278652430569695932559411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38185768287046463955039607 57278652430569695932559411)
    ·
      refine ⟨85917978645854543898839117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57278652430569695932559411 85917978645854543898839117)
      ·
        refine ⟨32219241992195453962064669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85917978645854543898839117 32219241992195453962064669)
        ·
          refine ⟨12082215747073295235774251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32219241992195453962064669 12082215747073295235774251)
          ·
            refine ⟨18123323620609942853661377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12082215747073295235774251 18123323620609942853661377)
            ·
              refine ⟨13592492715457457140246033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18123323620609942853661377 13592492715457457140246033)
              ·
                refine ⟨10194369536593092855184525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13592492715457457140246033 10194369536593092855184525)
                ·
                  refine ⟨3822888576222409820694197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10194369536593092855184525 3822888576222409820694197)
                  ·
                    refine ⟨358395804020850920690081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3822888576222409820694197 358395804020850920690081)
                    ·
                      rfl

theorem cell23_2093920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 3, 5].length) (baseStart_2093920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093920 prefixEnd_2093920 := by exact prefixLift 2093920
  have htrace : WordTrace (prefixWord ++ tailWord_2093920) baseStart_2093920 baseEnd_2093920 := by
    simpa [prefixWord, tailWord_2093920, baseEnd_2093920] using wordTrace_append hprefix tailTrace_2093920
  have hstable : (prefixWord ++ tailWord_2093920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093920).length < 2 ^ (prefixWord ++ tailWord_2093920).sum := by decide
  have hdescent : baseEnd_2093920 < baseStart_2093920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093924 : List Nat := [2, 3, 1, 1, 4, 3, 2, 1, 6]
def baseStart_2093924 : Nat := 118140960795 + 2093924 * 2 ^ 59
def prefixEnd_2093924 : Nat := 4983230072969 + 3 ^ 40 * 2093924 * 2
def baseEnd_2093924 : Nat := 119465496220574527380025

theorem tailTrace_2093924 : CollatzResearch.WordTrace tailWord_2093924 prefixEnd_2093924 119465496220574527380025 := by
  unfold tailWord_2093924
  simp only [CollatzResearch.WordTrace]
  refine ⟨38185841233039218296612413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50914454977385624395483217 38185841233039218296612413)
  ·
    refine ⟨14319690462389706861229655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38185841233039218296612413 14319690462389706861229655)
    ·
      refine ⟨21479535693584560291844483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14319690462389706861229655 21479535693584560291844483)
      ·
        refine ⟨32219303540376840437766725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21479535693584560291844483 32219303540376840437766725)
        ·
          refine ⟨6041119413820657582081261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32219303540376840437766725 6041119413820657582081261)
          ·
            refine ⟨2265419780182746593280473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6041119413820657582081261 2265419780182746593280473)
            ·
              refine ⟨1699064835137059944960355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2265419780182746593280473 1699064835137059944960355)
              ·
                refine ⟨2548597252705589917440533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699064835137059944960355 2548597252705589917440533)
                ·
                  refine ⟨119465496220574527380025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2548597252705589917440533 119465496220574527380025)
                  ·
                    rfl

theorem cell23_2093924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_2093924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093924 prefixEnd_2093924 := by exact prefixLift 2093924
  have htrace : WordTrace (prefixWord ++ tailWord_2093924) baseStart_2093924 baseEnd_2093924 := by
    simpa [prefixWord, tailWord_2093924, baseEnd_2093924] using wordTrace_append hprefix tailTrace_2093924
  have hstable : (prefixWord ++ tailWord_2093924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093924).length < 2 ^ (prefixWord ++ tailWord_2093924).sum := by decide
  have hdescent : baseEnd_2093924 < baseStart_2093924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093937 : List Nat := [1, 2, 2, 2, 1, 4, 3, 2, 1, 5]
def baseStart_2093937 : Nat := 118140960795 + 2093937 * 2 ^ 59
def prefixEnd_2093937 : Nat := 4983230072969 + 3 ^ 40 * 2093937 * 2
def baseEnd_2093937 : Nat := 358398713744559731852555

theorem tailTrace_2093937 : CollatzResearch.WordTrace tailWord_2093937 prefixEnd_2093937 358398713744559731852555 := by
  unfold tailWord_2093937
  simp only [CollatzResearch.WordTrace]
  refine ⟨76372156615031339813448065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50914771076687559875632043 76372156615031339813448065)
  ·
    refine ⟨57279117461273504860086049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76372156615031339813448065 57279117461273504860086049)
    ·
      refine ⟨42959338095955128645064537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57279117461273504860086049 42959338095955128645064537)
      ·
        refine ⟨32219503571966346483798403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42959338095955128645064537 32219503571966346483798403)
        ·
          refine ⟨48329255357949519725697605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32219503571966346483798403 48329255357949519725697605)
          ·
            refine ⟨9061735379615534948568301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48329255357949519725697605 9061735379615534948568301)
            ·
              refine ⟨3398150767355825605713113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9061735379615534948568301 3398150767355825605713113)
              ·
                refine ⟨2548613075516869204284835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3398150767355825605713113 2548613075516869204284835)
                ·
                  refine ⟨3822919613275303806427253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2548613075516869204284835 3822919613275303806427253)
                  ·
                    refine ⟨358398713744559731852555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3822919613275303806427253 358398713744559731852555)
                    ·
                      rfl

theorem cell23_2093937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_2093937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2093937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2093937 prefixEnd_2093937 := by exact prefixLift 2093937
  have htrace : WordTrace (prefixWord ++ tailWord_2093937) baseStart_2093937 baseEnd_2093937 := by
    simpa [prefixWord, tailWord_2093937, baseEnd_2093937] using wordTrace_append hprefix tailTrace_2093937
  have hstable : (prefixWord ++ tailWord_2093937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093937).length < 2 ^ (prefixWord ++ tailWord_2093937).sum := by decide
  have hdescent : baseEnd_2093937 < baseStart_2093937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094007 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 3]
def baseStart_2094007 : Nat := 118140960795 + 2094007 * 2 ^ 59
def prefixEnd_2094007 : Nat := 4983230072969 + 3 ^ 40 * 2094007 * 2
def baseEnd_2094007 : Nat := 1075232084879493921682343

theorem tailTrace_2094007 : CollatzResearch.WordTrace tailWord_2094007 prefixEnd_2094007 1075232084879493921682343 := by
  unfold tailWord_2094007
  simp only [CollatzResearch.WordTrace]
  refine ⟨76374709724777741768496275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50916473149851827845664183 76374709724777741768496275)
  ·
    refine ⟨114562064587166612652744413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76374709724777741768496275 114562064587166612652744413)
    ·
      refine ⟨42960774220187479744779155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114562064587166612652744413 42960774220187479744779155)
      ·
        refine ⟨64441161330281219617168733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42960774220187479744779155 64441161330281219617168733)
        ·
          refine ⟨24165435498855457356438275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64441161330281219617168733 24165435498855457356438275)
          ·
            refine ⟨36248153248283186034657413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24165435498855457356438275 36248153248283186034657413)
            ·
              refine ⟨6796528734053097381498265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36248153248283186034657413 6796528734053097381498265)
              ·
                refine ⟨5097396550539823036123699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6796528734053097381498265 5097396550539823036123699)
                ·
                  refine ⟨7646094825809734554185549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5097396550539823036123699 7646094825809734554185549)
                  ·
                    refine ⟨2867285559678650457819581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7646094825809734554185549 2867285559678650457819581)
                    ·
                      refine ⟨1075232084879493921682343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2867285559678650457819581 1075232084879493921682343)
                      ·
                        rfl

theorem cell23_2094007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_2094007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094007 prefixEnd_2094007 := by exact prefixLift 2094007
  have htrace : WordTrace (prefixWord ++ tailWord_2094007) baseStart_2094007 baseEnd_2094007 := by
    simpa [prefixWord, tailWord_2094007, baseEnd_2094007] using wordTrace_append hprefix tailTrace_2094007
  have hstable : (prefixWord ++ tailWord_2094007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094007).length < 2 ^ (prefixWord ++ tailWord_2094007).sum := by decide
  have hdescent : baseEnd_2094007 < baseStart_2094007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094008 : List Nat := [2, 1, 2, 1, 2, 5, 2, 3, 1, 2, 2]
def baseStart_2094008 : Nat := 118140960795 + 2094008 * 2 ^ 59
def prefixEnd_2094008 : Nat := 4983230072969 + 3 ^ 40 * 2094008 * 2
def baseEnd_2094008 : Nat := 1075232598360148417769839

theorem tailTrace_2094008 : CollatzResearch.WordTrace tailWord_2094008 prefixEnd_2094008 1075232598360148417769839 := by
  unfold tailWord_2094008
  simp only [CollatzResearch.WordTrace]
  refine ⟨38187373098887059469641339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50916497465182745959521785 38187373098887059469641339)
  ·
    refine ⟨57281059648330589204462009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38187373098887059469641339 57281059648330589204462009)
    ·
      refine ⟨42960794736247941903346507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57281059648330589204462009 42960794736247941903346507)
      ·
        refine ⟨64441192104371912855019761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42960794736247941903346507 64441192104371912855019761)
        ·
          refine ⟨48330894078278934641264821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64441192104371912855019761 48330894078278934641264821)
          ·
            refine ⟨4531021319838650122618577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48330894078278934641264821 4531021319838650122618577)
            ·
              refine ⟨3398265989878987591963933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4531021319838650122618577 3398265989878987591963933)
              ·
                refine ⟨1274349746204620346986475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3398265989878987591963933 1274349746204620346986475)
                ·
                  refine ⟨1911524619306930520479713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274349746204620346986475 1911524619306930520479713)
                  ·
                    refine ⟨1433643464480197890359785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1911524619306930520479713 1433643464480197890359785)
                    ·
                      refine ⟨1075232598360148417769839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1433643464480197890359785 1075232598360148417769839)
                      ·
                        rfl

theorem cell23_2094008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 1, 2, 2].length) (baseStart_2094008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094008 prefixEnd_2094008 := by exact prefixLift 2094008
  have htrace : WordTrace (prefixWord ++ tailWord_2094008) baseStart_2094008 baseEnd_2094008 := by
    simpa [prefixWord, tailWord_2094008, baseEnd_2094008] using wordTrace_append hprefix tailTrace_2094008
  have hstable : (prefixWord ++ tailWord_2094008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094008).length < 2 ^ (prefixWord ++ tailWord_2094008).sum := by decide
  have hdescent : baseEnd_2094008 < baseStart_2094008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094051 : List Nat := [1, 1, 1, 6, 1, 1, 4, 2, 1, 3, 2]
def baseStart_2094051 : Nat := 118140960795 + 2094051 * 2 ^ 59
def prefixEnd_2094051 : Nat := 4983230072969 + 3 ^ 40 * 2094051 * 2
def baseEnd_2094051 : Nat := 1075254678028291749532141

theorem tailTrace_2094051 : CollatzResearch.WordTrace tailWord_2094051 prefixEnd_2094051 1075254678028291749532141 := by
  unfold tailWord_2094051
  simp only [CollatzResearch.WordTrace]
  refine ⟨76376314536618337283098007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50917543024412224855398671 76376314536618337283098007)
  ·
    refine ⟨114564471804927505924647011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76376314536618337283098007 114564471804927505924647011)
    ·
      refine ⟨171846707707391258886970517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114564471804927505924647011 171846707707391258886970517)
      ·
        refine ⟨8055314423783965260326743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171846707707391258886970517 8055314423783965260326743)
        ·
          refine ⟨12082971635675947890490115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8055314423783965260326743 12082971635675947890490115)
          ·
            refine ⟨18124457453513921835735173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12082971635675947890490115 18124457453513921835735173)
            ·
              refine ⟨3398335772533860344200345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18124457453513921835735173 3398335772533860344200345)
              ·
                refine ⟨2548751829400395258150259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3398335772533860344200345 2548751829400395258150259)
                ·
                  refine ⟨3823127744100592887225389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2548751829400395258150259 3823127744100592887225389)
                  ·
                    refine ⟨1433672904037722332709521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3823127744100592887225389 1433672904037722332709521)
                    ·
                      refine ⟨1075254678028291749532141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1433672904037722332709521 1075254678028291749532141)
                      ·
                        rfl

theorem cell23_2094051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_2094051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094051 prefixEnd_2094051 := by exact prefixLift 2094051
  have htrace : WordTrace (prefixWord ++ tailWord_2094051) baseStart_2094051 baseEnd_2094051 := by
    simpa [prefixWord, tailWord_2094051, baseEnd_2094051] using wordTrace_append hprefix tailTrace_2094051
  have hstable : (prefixWord ++ tailWord_2094051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094051).length < 2 ^ (prefixWord ++ tailWord_2094051).sum := by decide
  have hdescent : baseEnd_2094051 < baseStart_2094051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094081 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_2094081 : Nat := 118140960795 + 2094081 * 2 ^ 59
def prefixEnd_2094081 : Nat := 4983230072969 + 3 ^ 40 * 2094081 * 2
def baseEnd_2094081 : Nat := 1075270082447926632157003

theorem tailTrace_2094081 : CollatzResearch.WordTrace tailWord_2094081 prefixEnd_2094081 1075270082447926632157003 := by
  unfold tailWord_2094081
  simp only [CollatzResearch.WordTrace]
  refine ⟨76377408726509652406690097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50918272484339768271126731 76377408726509652406690097)
  ·
    refine ⟨57283056544882239305017573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76377408726509652406690097 57283056544882239305017573)
    ·
      refine ⟨10740573102165419869690795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57283056544882239305017573 10740573102165419869690795)
      ·
        refine ⟨16110859653248129804536193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10740573102165419869690795 16110859653248129804536193)
        ·
          refine ⟨12083144739936097353402145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16110859653248129804536193 12083144739936097353402145)
          ·
            refine ⟨9062358554952073015051609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12083144739936097353402145 9062358554952073015051609)
            ·
              refine ⟨6796768916214054761288707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9062358554952073015051609 6796768916214054761288707)
              ·
                refine ⟨10195153374321082141933061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6796768916214054761288707 10195153374321082141933061)
                ·
                  refine ⟨1911591257685202901612449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10195153374321082141933061 1911591257685202901612449)
                  ·
                    refine ⟨1433693443263902176209337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1911591257685202901612449 1433693443263902176209337)
                    ·
                      refine ⟨1075270082447926632157003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1433693443263902176209337 1075270082447926632157003)
                      ·
                        rfl

theorem cell23_2094081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_2094081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094081 prefixEnd_2094081 := by exact prefixLift 2094081
  have htrace : WordTrace (prefixWord ++ tailWord_2094081) baseStart_2094081 baseEnd_2094081 := by
    simpa [prefixWord, tailWord_2094081, baseEnd_2094081] using wordTrace_append hprefix tailTrace_2094081
  have hstable : (prefixWord ++ tailWord_2094081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094081).length < 2 ^ (prefixWord ++ tailWord_2094081).sum := by decide
  have hdescent : baseEnd_2094081 < baseStart_2094081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094097 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 3]
def baseStart_2094097 : Nat := 118140960795 + 2094097 * 2 ^ 59
def prefixEnd_2094097 : Nat := 4983230072969 + 3 ^ 40 * 2094097 * 2
def baseEnd_2094097 : Nat := 1075278298138398569556929

theorem tailTrace_2094097 : CollatzResearch.WordTrace tailWord_2094097 prefixEnd_2094097 1075278298138398569556929 := by
  unfold tailWord_2094097
  simp only [CollatzResearch.WordTrace]
  refine ⟨76377992294451687139272545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50918661529634458092848363 76377992294451687139272545)
  ·
    refine ⟨57283494220838765354454409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76377992294451687139272545 57283494220838765354454409)
    ·
      refine ⟨42962620665629074015840807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57283494220838765354454409 42962620665629074015840807)
      ·
        refine ⟨64443930998443611023761211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42962620665629074015840807 64443930998443611023761211)
        ·
          refine ⟨96665896497665416535641817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64443930998443611023761211 96665896497665416535641817)
          ·
            refine ⟨72499422373249062401731363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96665896497665416535641817 72499422373249062401731363)
            ·
              refine ⟨108749133559873593602597045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72499422373249062401731363 108749133559873593602597045)
              ·
                refine ⟨10195231271238149400243473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108749133559873593602597045 10195231271238149400243473)
                ·
                  refine ⟨7646423453428612050182605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10195231271238149400243473 7646423453428612050182605)
                  ·
                    refine ⟨2867408795035729518818477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7646423453428612050182605 2867408795035729518818477)
                    ·
                      refine ⟨1075278298138398569556929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2867408795035729518818477 1075278298138398569556929)
                      ·
                        rfl

theorem cell23_2094097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_2094097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094097 prefixEnd_2094097 := by exact prefixLift 2094097
  have htrace : WordTrace (prefixWord ++ tailWord_2094097) baseStart_2094097 baseEnd_2094097 := by
    simpa [prefixWord, tailWord_2094097, baseEnd_2094097] using wordTrace_append hprefix tailTrace_2094097
  have hstable : (prefixWord ++ tailWord_2094097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094097).length < 2 ^ (prefixWord ++ tailWord_2094097).sum := by decide
  have hdescent : baseEnd_2094097 < baseStart_2094097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094154 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 1, 6, 2]
def baseStart_2094154 : Nat := 118140960795 + 2094154 * 2 ^ 59
def prefixEnd_2094154 : Nat := 4983230072969 + 3 ^ 40 * 2094154 * 2
def baseEnd_2094154 : Nat := 1075307566535704846544167

theorem tailTrace_2094154 : CollatzResearch.WordTrace tailWord_2094154 prefixEnd_2094154 1075307566535704846544167 := by
  unfold tailWord_2094154
  simp only [CollatzResearch.WordTrace]
  refine ⟨19095017813811296468524379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50920047503496790582731677 19095017813811296468524379)
  ·
    refine ⟨28642526720716944702786569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19095017813811296468524379 28642526720716944702786569)
    ·
      refine ⟨21481895040537708527089927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28642526720716944702786569 21481895040537708527089927)
      ·
        refine ⟨32222842560806562790634891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21481895040537708527089927 32222842560806562790634891)
        ·
          refine ⟨48334263841209844185952337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32222842560806562790634891 48334263841209844185952337)
          ·
            refine ⟨36250697880907383139464253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48334263841209844185952337 36250697880907383139464253)
            ·
              refine ⟨13594011705340268677299095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36250697880907383139464253 13594011705340268677299095)
              ·
                refine ⟨20391017558010403015948643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13594011705340268677299095 20391017558010403015948643)
                ·
                  refine ⟨30586526337015604523922965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20391017558010403015948643 30586526337015604523922965)
                  ·
                    refine ⟨1433743422047606462058889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30586526337015604523922965 1433743422047606462058889)
                    ·
                      refine ⟨1075307566535704846544167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1433743422047606462058889 1075307566535704846544167)
                      ·
                        rfl

theorem cell23_2094154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_2094154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094154 prefixEnd_2094154 := by exact prefixLift 2094154
  have htrace : WordTrace (prefixWord ++ tailWord_2094154) baseStart_2094154 baseEnd_2094154 := by
    simpa [prefixWord, tailWord_2094154, baseEnd_2094154] using wordTrace_append hprefix tailTrace_2094154
  have hstable : (prefixWord ++ tailWord_2094154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094154).length < 2 ^ (prefixWord ++ tailWord_2094154).sum := by decide
  have hdescent : baseEnd_2094154 < baseStart_2094154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094164 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_2094164 : Nat := 118140960795 + 2094164 * 2 ^ 59
def prefixEnd_2094164 : Nat := 4983230072969 + 3 ^ 40 * 2094164 * 2
def baseEnd_2094164 : Nat := 358437567114083269139707

theorem tailTrace_2094164 : CollatzResearch.WordTrace tailWord_2094164 prefixEnd_2094164 358437567114083269139707 := by
  unfold tailWord_2094164
  simp only [CollatzResearch.WordTrace]
  refine ⟨38190217992604478790980773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50920290656805971721307697 38190217992604478790980773)
  ·
    refine ⟨7160665873613339773308895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38190217992604478790980773 7160665873613339773308895)
    ·
      refine ⟨10740998810420009659963343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7160665873613339773308895 10740998810420009659963343)
      ·
        refine ⟨16111498215630014489945015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10740998810420009659963343 16111498215630014489945015)
        ·
          refine ⟨24167247323445021734917523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16111498215630014489945015 24167247323445021734917523)
          ·
            refine ⟨36250870985167532602376285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24167247323445021734917523 36250870985167532602376285)
            ·
              refine ⟨13594076619437824725891107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36250870985167532602376285 13594076619437824725891107)
              ·
                refine ⟨20391114929156737088836661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13594076619437824725891107 20391114929156737088836661)
                ·
                  refine ⟨1911667024608444102078437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20391114929156737088836661 1911667024608444102078437)
                  ·
                    refine ⟨358437567114083269139707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1911667024608444102078437 358437567114083269139707)
                    ·
                      rfl

theorem cell23_2094164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_2094164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094164 prefixEnd_2094164 := by exact prefixLift 2094164
  have htrace : WordTrace (prefixWord ++ tailWord_2094164) baseStart_2094164 baseEnd_2094164 := by
    simpa [prefixWord, tailWord_2094164, baseEnd_2094164] using wordTrace_append hprefix tailTrace_2094164
  have hstable : (prefixWord ++ tailWord_2094164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094164).length < 2 ^ (prefixWord ++ tailWord_2094164).sum := by decide
  have hdescent : baseEnd_2094164 < baseStart_2094164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094187 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 3]
def baseStart_2094187 : Nat := 118140960795 + 2094187 * 2 ^ 59
def prefixEnd_2094187 : Nat := 4983230072969 + 3 ^ 40 * 2094187 * 2
def baseEnd_2094187 : Nat := 1075324511397303217431515

theorem tailTrace_2094187 : CollatzResearch.WordTrace tailWord_2094187 prefixEnd_2094187 1075324511397303217431515 := by
  unfold tailWord_2094187
  simp only [CollatzResearch.WordTrace]
  refine ⟨76381274864125632510048815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50920849909417088340032543 76381274864125632510048815)
  ·
    refine ⟨114571912296188448765073223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76381274864125632510048815 114571912296188448765073223)
    ·
      refine ⟨171857868444282673147609835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114571912296188448765073223 171857868444282673147609835)
      ·
        refine ⟨257786802666424009721414753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171857868444282673147609835 257786802666424009721414753)
        ·
          refine ⟨193340101999818007291061065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257786802666424009721414753 193340101999818007291061065)
          ·
            refine ⟨145005076499863505468295799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193340101999818007291061065 145005076499863505468295799)
            ·
              refine ⟨217507614749795258202443699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145005076499863505468295799 217507614749795258202443699)
              ·
                refine ⟨326261422124692887303665549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217507614749795258202443699 326261422124692887303665549)
                ·
                  refine ⟨122348033296759832738874581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326261422124692887303665549 122348033296759832738874581)
                  ·
                    refine ⟨2867532030392808579817373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 122348033296759832738874581 2867532030392808579817373)
                    ·
                      refine ⟨1075324511397303217431515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2867532030392808579817373 1075324511397303217431515)
                      ·
                        rfl

theorem cell23_2094187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 3].length) (baseStart_2094187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094187 prefixEnd_2094187 := by exact prefixLift 2094187
  have htrace : WordTrace (prefixWord ++ tailWord_2094187) baseStart_2094187 baseEnd_2094187 := by
    simpa [prefixWord, tailWord_2094187, baseEnd_2094187] using wordTrace_append hprefix tailTrace_2094187
  have hstable : (prefixWord ++ tailWord_2094187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094187).length < 2 ^ (prefixWord ++ tailWord_2094187).sum := by decide
  have hdescent : baseEnd_2094187 < baseStart_2094187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094198 : List Nat := [5, 1, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_2094198 : Nat := 118140960795 + 2094198 * 2 ^ 59
def prefixEnd_2094198 : Nat := 4983230072969 + 3 ^ 40 * 2094198 * 2
def baseEnd_2094198 : Nat := 358443386561500891464655

theorem tailTrace_2094198 : CollatzResearch.WordTrace tailWord_2094198 prefixEnd_2094198 358443386561500891464655 := by
  unfold tailWord_2094198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4773854754192861336793703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50921117378057187592466165 4773854754192861336793703)
  ·
    refine ⟨7160782131289292005190555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4773854754192861336793703 7160782131289292005190555)
    ·
      refine ⟨10741173196933938007785833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7160782131289292005190555 10741173196933938007785833)
      ·
        refine ⟨8055879897700453505839375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10741173196933938007785833 8055879897700453505839375)
        ·
          refine ⟨12083819846550680258759063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8055879897700453505839375 12083819846550680258759063)
          ·
            refine ⟨18125729769826020388138595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12083819846550680258759063 18125729769826020388138595)
            ·
              refine ⟨27188594654739030582207893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18125729769826020388138595 27188594654739030582207893)
              ·
                refine ⟨1274465374440892058540995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27188594654739030582207893 1274465374440892058540995)
                ·
                  refine ⟨1911698061661338087811493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274465374440892058540995 1911698061661338087811493)
                  ·
                    refine ⟨358443386561500891464655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1911698061661338087811493 358443386561500891464655)
                    ·
                      rfl

theorem cell23_2094198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_2094198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094198 prefixEnd_2094198 := by exact prefixLift 2094198
  have htrace : WordTrace (prefixWord ++ tailWord_2094198) baseStart_2094198 baseEnd_2094198 := by
    simpa [prefixWord, tailWord_2094198, baseEnd_2094198] using wordTrace_append hprefix tailTrace_2094198
  have hstable : (prefixWord ++ tailWord_2094198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094198).length < 2 ^ (prefixWord ++ tailWord_2094198).sum := by decide
  have hdescent : baseEnd_2094198 < baseStart_2094198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094231 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 1, 5, 2]
def baseStart_2094231 : Nat := 118140960795 + 2094231 * 2 ^ 59
def prefixEnd_2094231 : Nat := 4983230072969 + 3 ^ 40 * 2094231 * 2
def baseEnd_2094231 : Nat := 1075347104546101045281313

theorem tailTrace_2094231 : CollatzResearch.WordTrace tailWord_2094231 prefixEnd_2094231 1075347104546101045281313 := by
  unfold tailWord_2094231
  simp only [CollatzResearch.WordTrace]
  refine ⟨76382879675966228024650547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50921919783977485349767031 76382879675966228024650547)
  ·
    refine ⟨114574319513949342036975821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76382879675966228024650547 114574319513949342036975821)
    ·
      refine ⟨42965369817731003263865933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114574319513949342036975821 42965369817731003263865933)
      ·
        refine ⟨16112013681649126223949725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42965369817731003263865933 16112013681649126223949725)
        ·
          refine ⟨6042005130618422333981147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16112013681649126223949725 6042005130618422333981147)
          ·
            refine ⟨9063007695927633500971721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042005130618422333981147 9063007695927633500971721)
            ·
              refine ⟨6797255771945725125728791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9063007695927633500971721 6797255771945725125728791)
              ·
                refine ⟨10195883657918587688593187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6797255771945725125728791 10195883657918587688593187)
                ·
                  refine ⟨15293825486877881532889781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10195883657918587688593187 15293825486877881532889781)
                  ·
                    refine ⟨1433796139394801393708417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15293825486877881532889781 1433796139394801393708417)
                    ·
                      refine ⟨1075347104546101045281313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1433796139394801393708417 1075347104546101045281313)
                      ·
                        rfl

theorem cell23_2094231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_2094231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094231 prefixEnd_2094231 := by exact prefixLift 2094231
  have htrace : WordTrace (prefixWord ++ tailWord_2094231) baseStart_2094231 baseEnd_2094231 := by
    simpa [prefixWord, tailWord_2094231, baseEnd_2094231] using wordTrace_append hprefix tailTrace_2094231
  have hstable : (prefixWord ++ tailWord_2094231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094231).length < 2 ^ (prefixWord ++ tailWord_2094231).sum := by decide
  have hdescent : baseEnd_2094231 < baseStart_2094231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094262 : List Nat := [5, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_2094262 : Nat := 118140960795 + 2094262 * 2 ^ 59
def prefixEnd_2094262 : Nat := 4983230072969 + 3 ^ 40 * 2094262 * 2
def baseEnd_2094262 : Nat := 119484780271821158221519

theorem tailTrace_2094262 : CollatzResearch.WordTrace tailWord_2094262 prefixEnd_2094262 119484780271821158221519 := by
  unfold tailWord_2094262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4774000646178370019939315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50922673559235946879352693 4774000646178370019939315)
  ·
    refine ⟨7161000969267555029908973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4774000646178370019939315 7161000969267555029908973)
    ·
      refine ⟨2685375363475333136215865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7161000969267555029908973 2685375363475333136215865)
      ·
        refine ⟨2014031522606499852161899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2685375363475333136215865 2014031522606499852161899)
        ·
          refine ⟨3021047283909749778242849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014031522606499852161899 3021047283909749778242849)
          ·
            refine ⟨2265785462932312333682137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3021047283909749778242849 2265785462932312333682137)
            ·
              refine ⟨1699339097199234250261603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2265785462932312333682137 1699339097199234250261603)
              ·
                refine ⟨2549008645798851375392405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699339097199234250261603 2549008645798851375392405)
                ·
                  refine ⟨119484780271821158221519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2549008645798851375392405 119484780271821158221519)
                  ·
                    rfl

theorem cell23_2094262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_2094262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094262 prefixEnd_2094262 := by exact prefixLift 2094262
  have htrace : WordTrace (prefixWord ++ tailWord_2094262) baseStart_2094262 baseEnd_2094262 := by
    simpa [prefixWord, tailWord_2094262, baseEnd_2094262] using wordTrace_append hprefix tailTrace_2094262
  have hstable : (prefixWord ++ tailWord_2094262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094262).length < 2 ^ (prefixWord ++ tailWord_2094262).sum := by decide
  have hdescent : baseEnd_2094262 < baseStart_2094262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094301 : List Nat := [1, 4, 3, 2, 3, 10]
def baseStart_2094301 : Nat := 118140960795 + 2094301 * 2 ^ 59
def prefixEnd_2094301 : Nat := 4983230072969 + 3 ^ 40 * 2094301 * 2
def baseEnd_2094301 : Nat := 4425444642765085479037

theorem tailTrace_2094301 : CollatzResearch.WordTrace tailWord_2094301 prefixEnd_2094301 4425444642765085479037 := by
  unfold tailWord_2094301
  simp only [CollatzResearch.WordTrace]
  refine ⟨76385432785712629979698757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50923621857141753319799171 76385432785712629979698757)
  ·
    refine ⟨14322268647321118121193517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76385432785712629979698757 14322268647321118121193517)
    ·
      refine ⟨5370850742745419295447569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14322268647321118121193517 5370850742745419295447569)
      ·
        refine ⟨4028138057059064471585677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5370850742745419295447569 4028138057059064471585677)
        ·
          refine ⟨1510551771397149176844629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4028138057059064471585677 1510551771397149176844629)
          ·
            refine ⟨4425444642765085479037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1510551771397149176844629 4425444642765085479037)
            ·
              rfl

theorem cell23_2094301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 10].length) (baseStart_2094301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094301 prefixEnd_2094301 := by exact prefixLift 2094301
  have htrace : WordTrace (prefixWord ++ tailWord_2094301) baseStart_2094301 baseEnd_2094301 := by
    simpa [prefixWord, tailWord_2094301, baseEnd_2094301] using wordTrace_append hprefix tailTrace_2094301
  have hstable : (prefixWord ++ tailWord_2094301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094301).length < 2 ^ (prefixWord ++ tailWord_2094301).sum := by decide
  have hdescent : baseEnd_2094301 < baseStart_2094301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094314 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 2, 7]
def baseStart_2094314 : Nat := 118140960795 + 2094314 * 2 ^ 59
def prefixEnd_2094314 : Nat := 4983230072969 + 3 ^ 40 * 2094314 * 2
def baseEnd_2094314 : Nat := 358463241146808073514477

theorem tailTrace_2094314 : CollatzResearch.WordTrace tailWord_2094314 prefixEnd_2094314 358463241146808073514477 := by
  unfold tailWord_2094314
  simp only [CollatzResearch.WordTrace]
  refine ⟨19096476733666383299980499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50923937956443688799947997 19096476733666383299980499)
  ·
    refine ⟨28644715100499574949970749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19096476733666383299980499 28644715100499574949970749)
    ·
      refine ⟨10741768162687340606239031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28644715100499574949970749 10741768162687340606239031)
      ·
        refine ⟨16112652244031010909358547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10741768162687340606239031 16112652244031010909358547)
        ·
          refine ⟨24168978366046516364037821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16112652244031010909358547 24168978366046516364037821)
          ·
            refine ⟨9063366887267443636514183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24168978366046516364037821 9063366887267443636514183)
            ·
              refine ⟨13595050330901165454771275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9063366887267443636514183 13595050330901165454771275)
              ·
                refine ⟨20392575496351748182156913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13595050330901165454771275 20392575496351748182156913)
                ·
                  refine ⟨15294431622263811136617685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20392575496351748182156913 15294431622263811136617685)
                  ·
                    refine ⟨358463241146808073514477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15294431622263811136617685 358463241146808073514477)
                    ·
                      rfl

theorem cell23_2094314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_2094314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094314 prefixEnd_2094314 := by exact prefixLift 2094314
  have htrace : WordTrace (prefixWord ++ tailWord_2094314) baseStart_2094314 baseEnd_2094314 := by
    simpa [prefixWord, tailWord_2094314, baseEnd_2094314] using wordTrace_append hprefix tailTrace_2094314
  have hstable : (prefixWord ++ tailWord_2094314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094314).length < 2 ^ (prefixWord ++ tailWord_2094314).sum := by decide
  have hdescent : baseEnd_2094314 < baseStart_2094314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094385 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 1, 4, 2]
def baseStart_2094385 : Nat := 118140960795 + 2094385 * 2 ^ 59
def prefixEnd_2094385 : Nat := 4983230072969 + 3 ^ 40 * 2094385 * 2
def baseEnd_2094385 : Nat := 1075426180566893442755605

theorem tailTrace_2094385 : CollatzResearch.WordTrace tailWord_2094385 prefixEnd_2094385 1075426180566893442755605 := by
  unfold tailWord_2094385
  simp only [CollatzResearch.WordTrace]
  refine ⟨76388496517408312325756609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50925664344938874883837739 76388496517408312325756609)
  ·
    refine ⟨57291372388056234244317457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76388496517408312325756609 57291372388056234244317457)
    ·
      refine ⟨42968529291042175683238093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57291372388056234244317457 42968529291042175683238093)
      ·
        refine ⟨16113198484140815881214285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42968529291042175683238093 16113198484140815881214285)
        ·
          refine ⟨6042449431552805955455357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16113198484140815881214285 6042449431552805955455357)
          ·
            refine ⟨2265918536832302233295759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6042449431552805955455357 2265918536832302233295759)
            ·
              refine ⟨3398877805248453349943639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265918536832302233295759 3398877805248453349943639)
              ·
                refine ⟨5098316707872680024915459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3398877805248453349943639 5098316707872680024915459)
                ·
                  refine ⟨7647475061809020037373189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098316707872680024915459 7647475061809020037373189)
                  ·
                    refine ⟨1433901574089191257007473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7647475061809020037373189 1433901574089191257007473)
                    ·
                      refine ⟨1075426180566893442755605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1433901574089191257007473 1075426180566893442755605)
                      ·
                        rfl

theorem cell23_2094385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_2094385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094385 prefixEnd_2094385 := by exact prefixLift 2094385
  have htrace : WordTrace (prefixWord ++ tailWord_2094385) baseStart_2094385 baseEnd_2094385 := by
    simpa [prefixWord, tailWord_2094385, baseEnd_2094385] using wordTrace_append hprefix tailTrace_2094385
  have hstable : (prefixWord ++ tailWord_2094385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094385).length < 2 ^ (prefixWord ++ tailWord_2094385).sum := by decide
  have hdescent : baseEnd_2094385 < baseStart_2094385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094421 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 4, 5]
def baseStart_2094421 : Nat := 118140960795 + 2094421 * 2 ^ 59
def prefixEnd_2094421 : Nat := 4983230072969 + 3 ^ 40 * 2094421 * 2
def baseEnd_2094421 : Nat := 358481555290151767301813

theorem tailTrace_2094421 : CollatzResearch.WordTrace tailWord_2094421 prefixEnd_2094421 358481555290151767301813 := by
  unfold tailWord_2094421
  simp only [CollatzResearch.WordTrace]
  refine ⟨76389809545277890474067117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50926539696851926982711411 76389809545277890474067117)
  ·
    refine ⟨28646178579479208927775169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76389809545277890474067117 28646178579479208927775169)
    ·
      refine ⟨21484633934609406695831377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28646178579479208927775169 21484633934609406695831377)
      ·
        refine ⟨16113475450957055021873533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21484633934609406695831377 16113475450957055021873533)
        ·
          refine ⟨6042553294108895633202575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16113475450957055021873533 6042553294108895633202575)
          ·
            refine ⟨9063829941163343449803863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042553294108895633202575 9063829941163343449803863)
            ·
              refine ⟨13595744911745015174705795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9063829941163343449803863 13595744911745015174705795)
              ·
                refine ⟨20393617367617522762058693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13595744911745015174705795 20393617367617522762058693)
                ·
                  refine ⟨3823803256428285517886005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20393617367617522762058693 3823803256428285517886005)
                  ·
                    refine ⟨358481555290151767301813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3823803256428285517886005 358481555290151767301813)
                    ·
                      rfl

theorem cell23_2094421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_2094421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094421 prefixEnd_2094421 := by exact prefixLift 2094421
  have htrace : WordTrace (prefixWord ++ tailWord_2094421) baseStart_2094421 baseEnd_2094421 := by
    simpa [prefixWord, tailWord_2094421, baseEnd_2094421] using wordTrace_append hprefix tailTrace_2094421
  have hstable : (prefixWord ++ tailWord_2094421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094421).length < 2 ^ (prefixWord ++ tailWord_2094421).sum := by decide
  have hdescent : baseEnd_2094421 < baseStart_2094421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094464 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 10]
def baseStart_2094464 : Nat := 118140960795 + 2094464 * 2 ^ 59
def prefixEnd_2094464 : Nat := 4983230072969 + 3 ^ 40 * 2094464 * 2
def baseEnd_2094464 : Nat := 119496305059844292629749

theorem tailTrace_2094464 : CollatzResearch.WordTrace tailWord_2094464 prefixEnd_2094464 119496305059844292629749 := by
  unfold tailWord_2094464
  simp only [CollatzResearch.WordTrace]
  refine ⟨38195688942061054408941223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50927585256081405878588297 38195688942061054408941223)
  ·
    refine ⟨57293533413091581613411835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38195688942061054408941223 57293533413091581613411835)
    ·
      refine ⟨85940300119637372420117753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57293533413091581613411835 85940300119637372420117753)
      ·
        refine ⟨64455225089728029315088315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85940300119637372420117753 64455225089728029315088315)
        ·
          refine ⟨96682837634592043972632473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64455225089728029315088315 96682837634592043972632473)
          ·
            refine ⟨72512128225944032979474355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96682837634592043972632473 72512128225944032979474355)
            ·
              refine ⟨108768192338916049469211533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72512128225944032979474355 108768192338916049469211533)
              ·
                refine ⟨40788072127093518550954325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108768192338916049469211533 40788072127093518550954325)
                ·
                  refine ⟨119496305059844292629749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 40788072127093518550954325 119496305059844292629749)
                  ·
                    rfl

theorem cell23_2094464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 10].length) (baseStart_2094464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094464 prefixEnd_2094464 := by exact prefixLift 2094464
  have htrace : WordTrace (prefixWord ++ tailWord_2094464) baseStart_2094464 baseEnd_2094464 := by
    simpa [prefixWord, tailWord_2094464, baseEnd_2094464] using wordTrace_append hprefix tailTrace_2094464
  have hstable : (prefixWord ++ tailWord_2094464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094464).length < 2 ^ (prefixWord ++ tailWord_2094464).sum := by decide
  have hdescent : baseEnd_2094464 < baseStart_2094464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094492 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2094492 : Nat := 118140960795 + 2094492 * 2 ^ 59
def prefixEnd_2094492 : Nat := 4983230072969 + 3 ^ 40 * 2094492 * 2
def baseEnd_2094492 : Nat := 1075481122996924524117613

theorem tailTrace_2094492 : CollatzResearch.WordTrace tailWord_2094492 prefixEnd_2094492 1075481122996924524117613 := by
  unfold tailWord_2094492
  simp only [CollatzResearch.WordTrace]
  refine ⟨38196199564010334799950865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50928266085347113066601153 38196199564010334799950865)
  ·
    refine ⟨28647149673007751099963149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38196199564010334799950865 28647149673007751099963149)
    ·
      refine ⟨10742681127377906662486181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28647149673007751099963149 10742681127377906662486181)
      ·
        refine ⟨2014252711383357499216159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10742681127377906662486181 2014252711383357499216159)
        ·
          refine ⟨3021379067075036248824239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014252711383357499216159 3021379067075036248824239)
          ·
            refine ⟨4532068600612554373236359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021379067075036248824239 4532068600612554373236359)
            ·
              refine ⟨6798102900918831559854539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4532068600612554373236359 6798102900918831559854539)
              ·
                refine ⟨10197154351378247339781809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6798102900918831559854539 10197154351378247339781809)
                ·
                  refine ⟨7647865763533685504836357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10197154351378247339781809 7647865763533685504836357)
                  ·
                    refine ⟨1433974830662566032156817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7647865763533685504836357 1433974830662566032156817)
                    ·
                      refine ⟨1075481122996924524117613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1433974830662566032156817 1075481122996924524117613)
                      ·
                        rfl

theorem cell23_2094492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2094492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094492 prefixEnd_2094492 := by exact prefixLift 2094492
  have htrace : WordTrace (prefixWord ++ tailWord_2094492) baseStart_2094492 baseEnd_2094492 := by
    simpa [prefixWord, tailWord_2094492, baseEnd_2094492] using wordTrace_append hprefix tailTrace_2094492
  have hstable : (prefixWord ++ tailWord_2094492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094492).length < 2 ^ (prefixWord ++ tailWord_2094492).sum := by decide
  have hdescent : baseEnd_2094492 < baseStart_2094492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094498 : List Nat := [3, 3, 1, 2, 1, 2, 2, 3, 6]
def baseStart_2094498 : Nat := 118140960795 + 2094498 * 2 ^ 59
def prefixEnd_2094498 : Nat := 4983230072969 + 3 ^ 40 * 2094498 * 2
def baseEnd_2094498 : Nat := 119498244875650166738065

theorem tailTrace_2094498 : CollatzResearch.WordTrace tailWord_2094498 prefixEnd_2094498 119498244875650166738065 := by
  unfold tailWord_2094498
  simp only [CollatzResearch.WordTrace]
  refine ⟨19098154491499733156155037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50928411977332621749746765 19098154491499733156155037)
  ·
    refine ⟨7161807934312399933558139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19098154491499733156155037 7161807934312399933558139)
    ·
      refine ⟨10742711901468599900337209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7161807934312399933558139 10742711901468599900337209)
      ·
        refine ⟨8057033926101449925252907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10742711901468599900337209 8057033926101449925252907)
        ·
          refine ⟨12085550889152174887879361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057033926101449925252907 12085550889152174887879361)
          ·
            refine ⟨9064163166864131165909521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12085550889152174887879361 9064163166864131165909521)
            ·
              refine ⟨6798122375148098374432141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9064163166864131165909521 6798122375148098374432141)
              ·
                refine ⟨2549295890680536890412053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6798122375148098374432141 2549295890680536890412053)
                ·
                  refine ⟨119498244875650166738065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2549295890680536890412053 119498244875650166738065)
                  ·
                    rfl

theorem cell23_2094498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_2094498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094498 prefixEnd_2094498 := by exact prefixLift 2094498
  have htrace : WordTrace (prefixWord ++ tailWord_2094498) baseStart_2094498 baseEnd_2094498 := by
    simpa [prefixWord, tailWord_2094498, baseEnd_2094498] using wordTrace_append hprefix tailTrace_2094498
  have hstable : (prefixWord ++ tailWord_2094498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094498).length < 2 ^ (prefixWord ++ tailWord_2094498).sum := by decide
  have hdescent : baseEnd_2094498 < baseStart_2094498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094508 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 3]
def baseStart_2094508 : Nat := 118140960795 + 2094508 * 2 ^ 59
def prefixEnd_2094508 : Nat := 4983230072969 + 3 ^ 40 * 2094508 * 2
def baseEnd_2094508 : Nat := 1075489338687396461517539

theorem tailTrace_2094508 : CollatzResearch.WordTrace tailWord_2094508 prefixEnd_2094508 1075489338687396461517539 := by
  unfold tailWord_2094508
  simp only [CollatzResearch.WordTrace]
  refine ⟨38196491347981352166242089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50928655130641802888322785 38196491347981352166242089)
  ·
    refine ⟨28647368510986014124681567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38196491347981352166242089 28647368510986014124681567)
    ·
      refine ⟨42971052766479021187022351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28647368510986014124681567 42971052766479021187022351)
      ·
        refine ⟨64456579149718531780533527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42971052766479021187022351 64456579149718531780533527)
        ·
          refine ⟨96684868724577797670800291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64456579149718531780533527 96684868724577797670800291)
          ·
            refine ⟨145027303086866696506200437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96684868724577797670800291 145027303086866696506200437)
            ·
              refine ⟨13596309664393752797456291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145027303086866696506200437 13596309664393752797456291)
              ·
                refine ⟨20394464496590629196184437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13596309664393752797456291 20394464496590629196184437)
                ·
                  refine ⟨1911981046555371487142291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20394464496590629196184437 1911981046555371487142291)
                  ·
                    refine ⟨2867971569833057230713437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1911981046555371487142291 2867971569833057230713437)
                    ·
                      refine ⟨1075489338687396461517539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2867971569833057230713437 1075489338687396461517539)
                      ·
                        rfl

theorem cell23_2094508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_2094508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094508 prefixEnd_2094508 := by exact prefixLift 2094508
  have htrace : WordTrace (prefixWord ++ tailWord_2094508) baseStart_2094508 baseEnd_2094508 := by
    simpa [prefixWord, tailWord_2094508, baseEnd_2094508] using wordTrace_append hprefix tailTrace_2094508
  have hstable : (prefixWord ++ tailWord_2094508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094508).length < 2 ^ (prefixWord ++ tailWord_2094508).sum := by decide
  have hdescent : baseEnd_2094508 < baseStart_2094508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094542 : List Nat := [4, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3]
def baseStart_2094542 : Nat := 118140960795 + 2094542 * 2 ^ 59
def prefixEnd_2094542 : Nat := 4983230072969 + 3 ^ 40 * 2094542 * 2
def baseEnd_2094542 : Nat := 1075506797029649328492383

theorem tailTrace_2094542 : CollatzResearch.WordTrace tailWord_2094542 prefixEnd_2094542 1075506797029649328492383 := by
  unfold tailWord_2094542
  simp only [CollatzResearch.WordTrace]
  refine ⟨9549277847229941017402735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50929481851893018759481253 9549277847229941017402735)
  ·
    refine ⟨14323916770844911526104103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9549277847229941017402735 14323916770844911526104103)
    ·
      refine ⟨21485875156267367289156155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14323916770844911526104103 21485875156267367289156155)
      ·
        refine ⟨32228812734401050933734233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21485875156267367289156155 32228812734401050933734233)
        ·
          refine ⟨24171609550800788200300675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32228812734401050933734233 24171609550800788200300675)
          ·
            refine ⟨36257414326201182300451013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24171609550800788200300675 36257414326201182300451013)
            ·
              refine ⟨6798265186162721681334565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36257414326201182300451013 6798265186162721681334565)
              ·
                refine ⟨1274674722405510315250231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6798265186162721681334565 1274674722405510315250231)
                ·
                  refine ⟨1912012083608265472875347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274674722405510315250231 1912012083608265472875347)
                  ·
                    refine ⟨2868018125412398209313021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1912012083608265472875347 2868018125412398209313021)
                    ·
                      refine ⟨1075506797029649328492383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2868018125412398209313021 1075506797029649328492383)
                      ·
                        rfl

theorem cell23_2094542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_2094542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094542 prefixEnd_2094542 := by exact prefixLift 2094542
  have htrace : WordTrace (prefixWord ++ tailWord_2094542) baseStart_2094542 baseEnd_2094542 := by
    simpa [prefixWord, tailWord_2094542, baseEnd_2094542] using wordTrace_append hprefix tailTrace_2094542
  have hstable : (prefixWord ++ tailWord_2094542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094542).length < 2 ^ (prefixWord ++ tailWord_2094542).sum := by decide
  have hdescent : baseEnd_2094542 < baseStart_2094542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094565 : List Nat := [1, 3, 1, 5, 1, 1, 1, 4, 1, 1, 4]
def baseStart_2094565 : Nat := 118140960795 + 2094565 * 2 ^ 59
def prefixEnd_2094565 : Nat := 4983230072969 + 3 ^ 40 * 2094565 * 2
def baseEnd_2094565 : Nat := 1075518607084702738504777

theorem tailTrace_2094565 : CollatzResearch.WordTrace tailWord_2094565 prefixEnd_2094565 1075518607084702738504777 := by
  unfold tailWord_2094565
  simp only [CollatzResearch.WordTrace]
  refine ⟨76395061656756203067309149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50930041104504135378206099 76395061656756203067309149)
  ·
    refine ⟨28648148121283576150240931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76395061656756203067309149 28648148121283576150240931)
    ·
      refine ⟨42972222181925364225361397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28648148121283576150240931 42972222181925364225361397)
      ·
        refine ⟨4028645829555502896127631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42972222181925364225361397 4028645829555502896127631)
        ·
          refine ⟨6042968744333254344191447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4028645829555502896127631 6042968744333254344191447)
          ·
            refine ⟨9064453116499881516287171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042968744333254344191447 9064453116499881516287171)
            ·
              refine ⟨13596679674749822274430757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9064453116499881516287171 13596679674749822274430757)
              ·
                refine ⟨2549377439015591676455767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13596679674749822274430757 2549377439015591676455767)
                ·
                  refine ⟨3824066158523387514683651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549377439015591676455767 3824066158523387514683651)
                  ·
                    refine ⟨5736099237785081272025477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3824066158523387514683651 5736099237785081272025477)
                    ·
                      refine ⟨1075518607084702738504777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5736099237785081272025477 1075518607084702738504777)
                      ·
                        rfl

theorem cell23_2094565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_2094565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094565 prefixEnd_2094565 := by exact prefixLift 2094565
  have htrace : WordTrace (prefixWord ++ tailWord_2094565) baseStart_2094565 baseEnd_2094565 := by
    simpa [prefixWord, tailWord_2094565, baseEnd_2094565] using wordTrace_append hprefix tailTrace_2094565
  have hstable : (prefixWord ++ tailWord_2094565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094565).length < 2 ^ (prefixWord ++ tailWord_2094565).sum := by decide
  have hdescent : baseEnd_2094565 < baseStart_2094565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094599 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 3, 2, 2]
def baseStart_2094599 : Nat := 118140960795 + 2094599 * 2 ^ 59
def prefixEnd_2094599 : Nat := 4983230072969 + 3 ^ 40 * 2094599 * 2
def baseEnd_2094599 : Nat := 1075536065426955605479621

theorem tailTrace_2094599 : CollatzResearch.WordTrace tailWord_2094599 prefixEnd_2094599 1075536065426955605479621 := by
  unfold tailWord_2094599
  simp only [CollatzResearch.WordTrace]
  refine ⟨76396301738633026874046851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50930867825755351249364567 76396301738633026874046851)
  ·
    refine ⟨114594452607949540311070277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76396301738633026874046851 114594452607949540311070277)
    ·
      refine ⟨21486459863990538808325677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114594452607949540311070277 21486459863990538808325677)
      ·
        refine ⟨8057422448996452053122129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21486459863990538808325677 8057422448996452053122129)
        ·
          refine ⟨6043066836747339039841597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8057422448996452053122129 6043066836747339039841597)
          ·
            refine ⟨2266150063780252139940599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6043066836747339039841597 2266150063780252139940599)
            ·
              refine ⟨3399225095670378209910899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266150063780252139940599 3399225095670378209910899)
              ·
                refine ⟨5098837643505567314866349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399225095670378209910899 5098837643505567314866349)
                ·
                  refine ⟨1912064116314587743074881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5098837643505567314866349 1912064116314587743074881)
                  ·
                    refine ⟨1434048087235940807306161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1912064116314587743074881 1434048087235940807306161)
                    ·
                      refine ⟨1075536065426955605479621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1434048087235940807306161 1075536065426955605479621)
                      ·
                        rfl

theorem cell23_2094599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_2094599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094599 prefixEnd_2094599 := by exact prefixLift 2094599
  have htrace : WordTrace (prefixWord ++ tailWord_2094599) baseStart_2094599 baseEnd_2094599 := by
    simpa [prefixWord, tailWord_2094599, baseEnd_2094599] using wordTrace_append hprefix tailTrace_2094599
  have hstable : (prefixWord ++ tailWord_2094599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094599).length < 2 ^ (prefixWord ++ tailWord_2094599).sum := by decide
  have hdescent : baseEnd_2094599 < baseStart_2094599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094601 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 2, 7]
def baseStart_2094601 : Nat := 118140960795 + 2094601 * 2 ^ 59
def prefixEnd_2094601 : Nat := 4983230072969 + 3 ^ 40 * 2094601 * 2
def baseEnd_2094601 : Nat := 358512364129421532551537

theorem tailTrace_2094601 : CollatzResearch.WordTrace tailWord_2094601 prefixEnd_2094601 358512364129421532551537 := by
  unfold tailWord_2094601
  simp only [CollatzResearch.WordTrace]
  refine ⟨76396374684625781215619657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50930916456417187477079771 76396374684625781215619657)
  ·
    refine ⟨57297281013469335911714743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76396374684625781215619657 57297281013469335911714743)
    ·
      refine ⟨85945921520204003867572115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57297281013469335911714743 85945921520204003867572115)
      ·
        refine ⟨128918882280306005801358173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85945921520204003867572115 128918882280306005801358173)
        ·
          refine ⟨48344580855114752175509315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128918882280306005801358173 48344580855114752175509315)
          ·
            refine ⟨72516871282672128263263973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48344580855114752175509315 72516871282672128263263973)
            ·
              refine ⟨13596913365501024049361995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72516871282672128263263973 13596913365501024049361995)
              ·
                refine ⟨20395370048251536074042993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13596913365501024049361995 20395370048251536074042993)
                ·
                  refine ⟨15296527536188652055532245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20395370048251536074042993 15296527536188652055532245)
                  ·
                    refine ⟨358512364129421532551537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15296527536188652055532245 358512364129421532551537)
                    ·
                      rfl

theorem cell23_2094601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_2094601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2094601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2094601 prefixEnd_2094601 := by exact prefixLift 2094601
  have htrace : WordTrace (prefixWord ++ tailWord_2094601) baseStart_2094601 baseEnd_2094601 := by
    simpa [prefixWord, tailWord_2094601, baseEnd_2094601] using wordTrace_append hprefix tailTrace_2094601
  have hstable : (prefixWord ++ tailWord_2094601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094601).length < 2 ^ (prefixWord ++ tailWord_2094601).sum := by decide
  have hdescent : baseEnd_2094601 < baseStart_2094601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
