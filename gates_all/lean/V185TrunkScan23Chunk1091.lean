import V185TrunkScan23Chunk1090

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6459231 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 9]
def baseStart_6459231 : Nat := 118140960795 + 6459231 * 2 ^ 59
def prefixEnd_6459231 : Nat := 4983230072969 + 3 ^ 40 * 6459231 * 2
def baseEnd_6459231 : Nat := 368521129046835884745227

theorem tailTrace_6459231 : CollatzResearch.WordTrace tailWord_6459231 prefixEnd_6459231 368521129046835884745227 := by
  unfold tailWord_6459231
  simp only [CollatzResearch.WordTrace]
  refine ⟨235587508862316710673745547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157058339241544473782497031 235587508862316710673745547)
  ·
    refine ⟨353381263293475066010618321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235587508862316710673745547 353381263293475066010618321)
    ·
      refine ⟨265035947470106299507963741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353381263293475066010618321 265035947470106299507963741)
      ·
        refine ⟨99388480301289862315486403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265035947470106299507963741 99388480301289862315486403)
        ·
          refine ⟨149082720451934793473229605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99388480301289862315486403 149082720451934793473229605)
          ·
            refine ⟨27953010084737773776230551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149082720451934793473229605 27953010084737773776230551)
            ·
              refine ⟨41929515127106660664345827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27953010084737773776230551 41929515127106660664345827)
              ·
                refine ⟨62894272690659990996518741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41929515127106660664345827 62894272690659990996518741)
                ·
                  refine ⟨368521129046835884745227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62894272690659990996518741 368521129046835884745227)
                  ·
                    rfl

theorem cell23_6459231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 9].length) (baseStart_6459231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459231 prefixEnd_6459231 := by exact prefixLift 6459231
  have htrace : WordTrace (prefixWord ++ tailWord_6459231) baseStart_6459231 baseEnd_6459231 := by
    simpa [prefixWord, tailWord_6459231, baseEnd_6459231] using wordTrace_append hprefix tailTrace_6459231
  have hstable : (prefixWord ++ tailWord_6459231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459231).length < 2 ^ (prefixWord ++ tailWord_6459231).sum := by decide
  have hdescent : baseEnd_6459231 < baseStart_6459231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459246 : List Nat := [4, 1, 2, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_6459246 : Nat := 118140960795 + 6459246 * 2 ^ 59
def prefixEnd_6459246 : Nat := 4983230072969 + 3 ^ 40 * 6459246 * 2
def baseEnd_6459246 : Nat := 3316697863631340404019475

theorem tailTrace_6459246 : CollatzResearch.WordTrace tailWord_6459246 prefixEnd_6459246 3316697863631340404019475 := by
  unfold tailWord_6459246
  simp only [CollatzResearch.WordTrace]
  refine ⟨29448506994657796029442699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157058703971508245490361061 29448506994657796029442699)
  ·
    refine ⟨44172760491986694044164049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29448506994657796029442699 44172760491986694044164049)
    ·
      refine ⟨33129570368990020533123037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44172760491986694044164049 33129570368990020533123037)
      ·
        refine ⟨12423588888371257699921139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33129570368990020533123037 12423588888371257699921139)
        ·
          refine ⟨18635383332556886549881709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12423588888371257699921139 18635383332556886549881709)
          ·
            refine ⟨6988268749708832456205641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18635383332556886549881709 6988268749708832456205641)
            ·
              refine ⟨5241201562281624342154231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6988268749708832456205641 5241201562281624342154231)
              ·
                refine ⟨7861802343422436513231347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241201562281624342154231 7861802343422436513231347)
                ·
                  refine ⟨11792703515133654769847021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7861802343422436513231347 11792703515133654769847021)
                  ·
                    refine ⟨4422263818175120538692633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11792703515133654769847021 4422263818175120538692633)
                    ·
                      refine ⟨3316697863631340404019475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422263818175120538692633 3316697863631340404019475)
                      ·
                        rfl

theorem cell23_6459246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_6459246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459246 prefixEnd_6459246 := by exact prefixLift 6459246
  have htrace : WordTrace (prefixWord ++ tailWord_6459246) baseStart_6459246 baseEnd_6459246 := by
    simpa [prefixWord, tailWord_6459246, baseEnd_6459246] using wordTrace_append hprefix tailTrace_6459246
  have hstable : (prefixWord ++ tailWord_6459246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459246).length < 2 ^ (prefixWord ++ tailWord_6459246).sum := by decide
  have hdescent : baseEnd_6459246 < baseStart_6459246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459258 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3]
def baseStart_6459258 : Nat := 118140960795 + 6459258 * 2 ^ 59
def prefixEnd_6459258 : Nat := 4983230072969 + 3 ^ 40 * 6459258 * 2
def baseEnd_6459258 : Nat := 3316704025399194357069419

theorem tailTrace_6459258 : CollatzResearch.WordTrace tailWord_6459258 prefixEnd_6459258 3316704025399194357069419 := by
  unfold tailWord_6459258
  simp only [CollatzResearch.WordTrace]
  refine ⟨58897123408304723571244607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157058995755479262856652285 58897123408304723571244607)
  ·
    refine ⟨88345685112457085356866911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58897123408304723571244607 88345685112457085356866911)
    ·
      refine ⟨132518527668685628035300367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88345685112457085356866911 132518527668685628035300367)
      ·
        refine ⟨198777791503028442052950551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132518527668685628035300367 198777791503028442052950551)
        ·
          refine ⟨298166687254542663079425827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198777791503028442052950551 298166687254542663079425827)
          ·
            refine ⟨447250030881813994619138741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298166687254542663079425827 447250030881813994619138741)
            ·
              refine ⟨41929690395170061995544257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 447250030881813994619138741 41929690395170061995544257)
              ·
                refine ⟨31447267796377546496658193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41929690395170061995544257 31447267796377546496658193)
                ·
                  refine ⟨23585450847283159872493645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31447267796377546496658193 23585450847283159872493645)
                  ·
                    refine ⟨8844544067731184952185117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23585450847283159872493645 8844544067731184952185117)
                    ·
                      refine ⟨3316704025399194357069419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8844544067731184952185117 3316704025399194357069419)
                      ·
                        rfl

theorem cell23_6459258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_6459258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459258 prefixEnd_6459258 := by exact prefixLift 6459258
  have htrace : WordTrace (prefixWord ++ tailWord_6459258) baseStart_6459258 baseEnd_6459258 := by
    simpa [prefixWord, tailWord_6459258, baseEnd_6459258] using wordTrace_append hprefix tailTrace_6459258
  have hstable : (prefixWord ++ tailWord_6459258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459258).length < 2 ^ (prefixWord ++ tailWord_6459258).sum := by decide
  have hdescent : baseEnd_6459258 < baseStart_6459258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459316 : List Nat := [2, 5, 2, 1, 2, 1, 3, 2, 5]
def baseStart_6459316 : Nat := 118140960795 + 6459316 * 2 ^ 59
def prefixEnd_6459316 : Nat := 4983230072969 + 3 ^ 40 * 6459316 * 2
def baseEnd_6459316 : Nat := 368525978586350570016017

theorem tailTrace_6459316 : CollatzResearch.WordTrace tailWord_6459316 prefixEnd_6459316 368525978586350570016017 := by
  unfold tailWord_6459316
  simp only [CollatzResearch.WordTrace]
  refine ⟨117795304533504385095294901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157060406044672513460393201 117795304533504385095294901)
  ·
    refine ⟨11043309800016036102683897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117795304533504385095294901 11043309800016036102683897)
    ·
      refine ⟨8282482350012027077012923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11043309800016036102683897 8282482350012027077012923)
      ·
        refine ⟨12423723525018040615519385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8282482350012027077012923 12423723525018040615519385)
        ·
          refine ⟨9317792643763530461639539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12423723525018040615519385 9317792643763530461639539)
          ·
            refine ⟨13976688965645295692459309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9317792643763530461639539 13976688965645295692459309)
            ·
              refine ⟨5241258362116985884672241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13976688965645295692459309 5241258362116985884672241)
              ·
                refine ⟨3930943771587739413504181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5241258362116985884672241 3930943771587739413504181)
                ·
                  refine ⟨368525978586350570016017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3930943771587739413504181 368525978586350570016017)
                  ·
                    rfl

theorem cell23_6459316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_6459316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459316 prefixEnd_6459316 := by exact prefixLift 6459316
  have htrace : WordTrace (prefixWord ++ tailWord_6459316) baseStart_6459316 baseEnd_6459316 := by
    simpa [prefixWord, tailWord_6459316, baseEnd_6459316] using wordTrace_append hprefix tailTrace_6459316
  have hstable : (prefixWord ++ tailWord_6459316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459316).length < 2 ^ (prefixWord ++ tailWord_6459316).sum := by decide
  have hdescent : baseEnd_6459316 < baseStart_6459316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459408 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 5]
def baseStart_6459408 : Nat := 118140960795 + 6459408 * 2 ^ 59
def prefixEnd_6459408 : Nat := 4983230072969 + 3 ^ 40 * 6459408 * 2
def baseEnd_6459408 : Nat := 3316781047497368770193729

theorem tailTrace_6459408 : CollatzResearch.WordTrace tailWord_6459408 prefixEnd_6459408 3316781047497368770193729 := by
  unfold tailWord_6459408
  simp only [CollatzResearch.WordTrace]
  refine ⟨117796982291337734951469439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157062643055116979935292585 117796982291337734951469439)
  ·
    refine ⟨176695473437006602427204159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117796982291337734951469439 176695473437006602427204159)
    ·
      refine ⟨265043210155509903640806239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176695473437006602427204159 265043210155509903640806239)
      ·
        refine ⟨397564815233264855461209359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265043210155509903640806239 397564815233264855461209359)
        ·
          refine ⟨596347222849897283191814039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397564815233264855461209359 596347222849897283191814039)
          ·
            refine ⟨894520834274845924787721059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596347222849897283191814039 894520834274845924787721059)
            ·
              refine ⟨1341781251412268887181581589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894520834274845924787721059 1341781251412268887181581589)
              ·
                refine ⟨62895996159950104086636637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1341781251412268887181581589 62895996159950104086636637)
                ·
                  refine ⟨23585998559981289032488739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62895996159950104086636637 23585998559981289032488739)
                  ·
                    refine ⟨35378997839971933548733109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23585998559981289032488739 35378997839971933548733109)
                    ·
                      refine ⟨3316781047497368770193729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35378997839971933548733109 3316781047497368770193729)
                      ·
                        rfl

theorem cell23_6459408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_6459408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459408 prefixEnd_6459408 := by exact prefixLift 6459408
  have htrace : WordTrace (prefixWord ++ tailWord_6459408) baseStart_6459408 baseEnd_6459408 := by
    simpa [prefixWord, tailWord_6459408, baseEnd_6459408] using wordTrace_append hprefix tailTrace_6459408
  have hstable : (prefixWord ++ tailWord_6459408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459408).length < 2 ^ (prefixWord ++ tailWord_6459408).sum := by decide
  have hdescent : baseEnd_6459408 < baseStart_6459408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459449 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 1, 6]
def baseStart_6459449 : Nat := 118140960795 + 6459449 * 2 ^ 59
def prefixEnd_6459449 : Nat := 4983230072969 + 3 ^ 40 * 6459449 * 2
def baseEnd_6459449 : Nat := 1105600700068067703260347

theorem tailTrace_6459449 : CollatzResearch.WordTrace tailWord_6459449 prefixEnd_6459449 1105600700068067703260347 := by
  unfold tailWord_6459449
  simp only [CollatzResearch.WordTrace]
  refine ⟨235595459975526933905181401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157063639983684622603454267 235595459975526933905181401)
  ·
    refine ⟨176696594981645200428886051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235595459975526933905181401 176696594981645200428886051)
    ·
      refine ⟨265044892472467800643329077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176696594981645200428886051 265044892472467800643329077)
      ·
        refine ⟨24847958669293856310312101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 265044892472467800643329077 24847958669293856310312101)
        ·
          refine ⟨4658992250492598058183519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24847958669293856310312101 4658992250492598058183519)
          ·
            refine ⟨6988488375738897087275279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658992250492598058183519 6988488375738897087275279)
            ·
              refine ⟨10482732563608345630912919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6988488375738897087275279 10482732563608345630912919)
              ·
                refine ⟨15724098845412518446369379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10482732563608345630912919 15724098845412518446369379)
                ·
                  refine ⟨23586148268118777669554069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15724098845412518446369379 23586148268118777669554069)
                  ·
                    refine ⟨1105600700068067703260347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23586148268118777669554069 1105600700068067703260347)
                    ·
                      rfl

theorem cell23_6459449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 1, 6].length) (baseStart_6459449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459449 prefixEnd_6459449 := by exact prefixLift 6459449
  have htrace : WordTrace (prefixWord ++ tailWord_6459449) baseStart_6459449 baseEnd_6459449 := by
    simpa [prefixWord, tailWord_6459449, baseEnd_6459449] using wordTrace_append hprefix tailTrace_6459449
  have hstable : (prefixWord ++ tailWord_6459449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459449).length < 2 ^ (prefixWord ++ tailWord_6459449).sum := by decide
  have hdescent : baseEnd_6459449 < baseStart_6459449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459462 : List Nat := [6, 1, 1, 1, 1, 1, 3, 9]
def baseStart_6459462 : Nat := 118140960795 + 6459462 * 2 ^ 59
def prefixEnd_6459462 : Nat := 4983230072969 + 3 ^ 40 * 6459462 * 2
def baseEnd_6459462 : Nat := 122844769461211539219203

theorem tailTrace_6459462 : CollatzResearch.WordTrace tailWord_6459462 prefixEnd_6459462 122844769461211539219203 := by
  unfold tailWord_6459462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7362372941389994910168895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157063956082986558083603093 7362372941389994910168895)
  ·
    refine ⟨11043559412084992365253343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7362372941389994910168895 11043559412084992365253343)
    ·
      refine ⟨16565339118127488547880015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11043559412084992365253343 16565339118127488547880015)
      ·
        refine ⟨24848008677191232821820023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16565339118127488547880015 24848008677191232821820023)
        ·
          refine ⟨37272013015786849232730035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24848008677191232821820023 37272013015786849232730035)
          ·
            refine ⟨55908019523680273849095053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37272013015786849232730035 55908019523680273849095053)
            ·
              refine ⟨20965507321380102693410645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55908019523680273849095053 20965507321380102693410645)
              ·
                refine ⟨122844769461211539219203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20965507321380102693410645 122844769461211539219203)
                ·
                  rfl

theorem cell23_6459462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_6459462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459462 prefixEnd_6459462 := by exact prefixLift 6459462
  have htrace : WordTrace (prefixWord ++ tailWord_6459462) baseStart_6459462 baseEnd_6459462 := by
    simpa [prefixWord, tailWord_6459462, baseEnd_6459462] using wordTrace_append hprefix tailTrace_6459462
  have hstable : (prefixWord ++ tailWord_6459462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459462).length < 2 ^ (prefixWord ++ tailWord_6459462).sum := by decide
  have hdescent : baseEnd_6459462 < baseStart_6459462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459490 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_6459490 : Nat := 118140960795 + 6459490 * 2 ^ 59
def prefixEnd_6459490 : Nat := 4983230072969 + 3 ^ 40 * 6459490 * 2
def baseEnd_6459490 : Nat := 3316823152911037449368353

theorem tailTrace_6459490 : CollatzResearch.WordTrace tailWord_6459490 prefixEnd_6459490 3316823152911037449368353 := by
  unfold tailWord_6459490
  simp only [CollatzResearch.WordTrace]
  refine ⟨58899238842094599476855981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157064636912252265271615949 58899238842094599476855981)
  ·
    refine ⟨22087214565785474803820993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58899238842094599476855981 22087214565785474803820993)
    ·
      refine ⟨16565410924339106102865745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22087214565785474803820993 16565410924339106102865745)
      ·
        refine ⟨12424058193254329577149309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16565410924339106102865745 12424058193254329577149309)
        ·
          refine ⟨4659021822470373591430991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12424058193254329577149309 4659021822470373591430991)
          ·
            refine ⟨6988532733705560387146487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659021822470373591430991 6988532733705560387146487)
            ·
              refine ⟨10482799100558340580719731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6988532733705560387146487 10482799100558340580719731)
              ·
                refine ⟨15724198650837510871079597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10482799100558340580719731 15724198650837510871079597)
                ·
                  refine ⟨5896574494064066576654849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15724198650837510871079597 5896574494064066576654849)
                  ·
                    refine ⟨4422430870548049932491137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5896574494064066576654849 4422430870548049932491137)
                    ·
                      refine ⟨3316823152911037449368353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422430870548049932491137 3316823152911037449368353)
                      ·
                        rfl

theorem cell23_6459490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_6459490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459490 prefixEnd_6459490 := by exact prefixLift 6459490
  have htrace : WordTrace (prefixWord ++ tailWord_6459490) baseStart_6459490 baseEnd_6459490 := by
    simpa [prefixWord, tailWord_6459490, baseEnd_6459490] using wordTrace_append hprefix tailTrace_6459490
  have hstable : (prefixWord ++ tailWord_6459490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459490).length < 2 ^ (prefixWord ++ tailWord_6459490).sum := by decide
  have hdescent : baseEnd_6459490 < baseStart_6459490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459495 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_6459495 : Nat := 118140960795 + 6459495 * 2 ^ 59
def prefixEnd_6459495 : Nat := 4983230072969 + 3 ^ 40 * 6459495 * 2
def baseEnd_6459495 : Nat := 3316825720314309929805829

theorem tailTrace_6459495 : CollatzResearch.WordTrace tailWord_6459495 prefixEnd_6459495 3316825720314309929805829 := by
  unfold tailWord_6459495
  simp only [CollatzResearch.WordTrace]
  refine ⟨235597137733360283761355939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157064758488906855840903959 235597137733360283761355939)
  ·
    refine ⟨353395706600040425642033909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235597137733360283761355939 353395706600040425642033909)
    ·
      refine ⟨33130847493753789903940679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 353395706600040425642033909 33130847493753789903940679)
      ·
        refine ⟨49696271240630684855911019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33130847493753789903940679 49696271240630684855911019)
        ·
          refine ⟨74544406860946027283866529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49696271240630684855911019 74544406860946027283866529)
          ·
            refine ⟨55908305145709520462899897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74544406860946027283866529 55908305145709520462899897)
            ·
              refine ⟨41931228859282140347174923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55908305145709520462899897 41931228859282140347174923)
              ·
                refine ⟨62896843288923210520762385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41931228859282140347174923 62896843288923210520762385)
                ·
                  refine ⟨47172632466692407890571789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62896843288923210520762385 47172632466692407890571789)
                  ·
                    refine ⟨17689737175009652958964421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47172632466692407890571789 17689737175009652958964421)
                    ·
                      refine ⟨3316825720314309929805829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17689737175009652958964421 3316825720314309929805829)
                      ·
                        rfl

theorem cell23_6459495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_6459495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459495 prefixEnd_6459495 := by exact prefixLift 6459495
  have htrace : WordTrace (prefixWord ++ tailWord_6459495) baseStart_6459495 baseEnd_6459495 := by
    simpa [prefixWord, tailWord_6459495, baseEnd_6459495] using wordTrace_append hprefix tailTrace_6459495
  have hstable : (prefixWord ++ tailWord_6459495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459495).length < 2 ^ (prefixWord ++ tailWord_6459495).sum := by decide
  have hdescent : baseEnd_6459495 < baseStart_6459495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459506 : List Nat := [3, 2, 1, 2, 2, 2, 4, 1, 2, 1, 3]
def baseStart_6459506 : Nat := 118140960795 + 6459506 * 2 ^ 59
def prefixEnd_6459506 : Nat := 4983230072969 + 3 ^ 40 * 6459506 * 2
def baseEnd_6459506 : Nat := 3316831368601509386768279

theorem tailTrace_6459506 : CollatzResearch.WordTrace tailWord_6459506 prefixEnd_6459506 3316831368601509386768279 := by
  unfold tailWord_6459506
  simp only [CollatzResearch.WordTrace]
  refine ⟨58899384734080108160001593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157065025957546955093337581 58899384734080108160001593)
  ·
    refine ⟨44174538550560081120001195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58899384734080108160001593 44174538550560081120001195)
    ·
      refine ⟨66261807825840121680001793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44174538550560081120001195 66261807825840121680001793)
      ·
        refine ⟨49696355869380091260001345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66261807825840121680001793 49696355869380091260001345)
        ·
          refine ⟨37272266902035068445001009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49696355869380091260001345 37272266902035068445001009)
          ·
            refine ⟨27954200176526301333750757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37272266902035068445001009 27954200176526301333750757)
            ·
              refine ⟨5241412533098681500078267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27954200176526301333750757 5241412533098681500078267)
              ·
                refine ⟨7862118799648022250117401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241412533098681500078267 7862118799648022250117401)
                ·
                  refine ⟨5896589099736016687588051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7862118799648022250117401 5896589099736016687588051)
                  ·
                    refine ⟨8844883649604025031382077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5896589099736016687588051 8844883649604025031382077)
                    ·
                      refine ⟨3316831368601509386768279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8844883649604025031382077 3316831368601509386768279)
                      ·
                        rfl

theorem cell23_6459506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_6459506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459506 prefixEnd_6459506 := by exact prefixLift 6459506
  have htrace : WordTrace (prefixWord ++ tailWord_6459506) baseStart_6459506 baseEnd_6459506 := by
    simpa [prefixWord, tailWord_6459506, baseEnd_6459506] using wordTrace_append hprefix tailTrace_6459506
  have hstable : (prefixWord ++ tailWord_6459506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459506).length < 2 ^ (prefixWord ++ tailWord_6459506).sum := by decide
  have hdescent : baseEnd_6459506 < baseStart_6459506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459512 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 1, 4, 2]
def baseStart_6459512 : Nat := 118140960795 + 6459512 * 2 ^ 59
def prefixEnd_6459512 : Nat := 4983230072969 + 3 ^ 40 * 6459512 * 2
def baseEnd_6459512 : Nat := 3316834449485436363293251

theorem tailTrace_6459512 : CollatzResearch.WordTrace tailWord_6459512 prefixEnd_6459512 3316834449485436363293251 := by
  unfold tailWord_6459512
  simp only [CollatzResearch.WordTrace]
  refine ⟨117798878887149347832362395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157065171849532463776483193 117798878887149347832362395)
  ·
    refine ⟨176698318330724021748543593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117798878887149347832362395 176698318330724021748543593)
    ·
      refine ⟨132523738748043016311407695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176698318330724021748543593 132523738748043016311407695)
      ·
        refine ⟨198785608122064524467111543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132523738748043016311407695 198785608122064524467111543)
        ·
          refine ⟨298178412183096786700667315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198785608122064524467111543 298178412183096786700667315)
          ·
            refine ⟨447267618274645180051000973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298178412183096786700667315 447267618274645180051000973)
            ·
              refine ⟨167725356852991942519125365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 447267618274645180051000973 167725356852991942519125365)
              ·
                refine ⟨15724252204967994611168003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167725356852991942519125365 15724252204967994611168003)
                ·
                  refine ⟨23586378307451991916752005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15724252204967994611168003 23586378307451991916752005)
                  ·
                    refine ⟨4422445932647248484391001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23586378307451991916752005 4422445932647248484391001)
                    ·
                      refine ⟨3316834449485436363293251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422445932647248484391001 3316834449485436363293251)
                      ·
                        rfl

theorem cell23_6459512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 1, 4, 2].length) (baseStart_6459512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459512 prefixEnd_6459512 := by exact prefixLift 6459512
  have htrace : WordTrace (prefixWord ++ tailWord_6459512) baseStart_6459512 baseEnd_6459512 := by
    simpa [prefixWord, tailWord_6459512, baseEnd_6459512] using wordTrace_append hprefix tailTrace_6459512
  have hstable : (prefixWord ++ tailWord_6459512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459512).length < 2 ^ (prefixWord ++ tailWord_6459512).sum := by decide
  have hdescent : baseEnd_6459512 < baseStart_6459512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459516 : List Nat := [2, 2, 2, 1, 1, 6, 1, 2, 1, 3, 2]
def baseStart_6459516 : Nat := 118140960795 + 6459516 * 2 ^ 59
def prefixEnd_6459516 : Nat := 4983230072969 + 3 ^ 40 * 6459516 * 2
def baseEnd_6459516 : Nat := 3316836503408054347643233

theorem tailTrace_6459516 : CollatzResearch.WordTrace tailWord_6459516 prefixEnd_6459516 3316836503408054347643233 := by
  unfold tailWord_6459516
  simp only [CollatzResearch.WordTrace]
  refine ⟨117798951833142102173935201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157065269110856136231913601 117798951833142102173935201)
  ·
    refine ⟨88349213874856576630451401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117798951833142102173935201 88349213874856576630451401)
    ·
      refine ⟨66261910406142432472838551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88349213874856576630451401 66261910406142432472838551)
      ·
        refine ⟨99392865609213648709257827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66261910406142432472838551 99392865609213648709257827)
        ·
          refine ⟨149089298413820473063886741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99392865609213648709257827 149089298413820473063886741)
          ·
            refine ⟨6988560863147834674869691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149089298413820473063886741 6988560863147834674869691)
            ·
              refine ⟨10482841294721752012304537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6988560863147834674869691 10482841294721752012304537)
              ·
                refine ⟨7862130971041314009228403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10482841294721752012304537 7862130971041314009228403)
                ·
                  refine ⟨11793196456561971013842605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7862130971041314009228403 11793196456561971013842605)
                  ·
                    refine ⟨4422448671210739130190977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11793196456561971013842605 4422448671210739130190977)
                    ·
                      refine ⟨3316836503408054347643233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422448671210739130190977 3316836503408054347643233)
                      ·
                        rfl

theorem cell23_6459516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_6459516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459516 prefixEnd_6459516 := by exact prefixLift 6459516
  have htrace : WordTrace (prefixWord ++ tailWord_6459516) baseStart_6459516 baseEnd_6459516 := by
    simpa [prefixWord, tailWord_6459516, baseEnd_6459516] using wordTrace_append hprefix tailTrace_6459516
  have hstable : (prefixWord ++ tailWord_6459516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459516).length < 2 ^ (prefixWord ++ tailWord_6459516).sum := by decide
  have hdescent : baseEnd_6459516 < baseStart_6459516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459545 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 3, 5, 3]
def baseStart_6459545 : Nat := 118140960795 + 6459545 * 2 ^ 59
def prefixEnd_6459545 : Nat := 4983230072969 + 3 ^ 40 * 6459545 * 2
def baseEnd_6459545 : Nat := 3316851394347034734180599

theorem tailTrace_6459545 : CollatzResearch.WordTrace tailWord_6459545 prefixEnd_6459545 3316851394347034734180599 := by
  unfold tailWord_6459545
  simp only [CollatzResearch.WordTrace]
  refine ⟨235598961383179142300676089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157065974255452761533784059 235598961383179142300676089)
  ·
    refine ⟨176699221037384356725507067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235598961383179142300676089 176699221037384356725507067)
    ·
      refine ⟨265048831556076535088260601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176699221037384356725507067 265048831556076535088260601)
      ·
        refine ⟨198786623667057401316195451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265048831556076535088260601 198786623667057401316195451)
        ·
          refine ⟨298179935500586101974293177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198786623667057401316195451 298179935500586101974293177)
          ·
            refine ⟨223634951625439576480719883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298179935500586101974293177 223634951625439576480719883)
            ·
              refine ⟨335452427438159364721079825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223634951625439576480719883 335452427438159364721079825)
              ·
                refine ⟨251589320578619523540809869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335452427438159364721079825 251589320578619523540809869)
                ·
                  refine ⟨94345995216982321327803701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251589320578619523540809869 94345995216982321327803701)
                  ·
                    refine ⟨8844937051592092624481597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94345995216982321327803701 8844937051592092624481597)
                    ·
                      refine ⟨3316851394347034734180599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8844937051592092624481597 3316851394347034734180599)
                      ·
                        rfl

theorem cell23_6459545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_6459545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459545 prefixEnd_6459545 := by exact prefixLift 6459545
  have htrace : WordTrace (prefixWord ++ tailWord_6459545) baseStart_6459545 baseEnd_6459545 := by
    simpa [prefixWord, tailWord_6459545, baseEnd_6459545] using wordTrace_append hprefix tailTrace_6459545
  have hstable : (prefixWord ++ tailWord_6459545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459545).length < 2 ^ (prefixWord ++ tailWord_6459545).sum := by decide
  have hdescent : baseEnd_6459545 < baseStart_6459545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459559 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_6459559 : Nat := 118140960795 + 6459559 * 2 ^ 59
def prefixEnd_6459559 : Nat := 4983230072969 + 3 ^ 40 * 6459559 * 2
def baseEnd_6459559 : Nat := 3316858583076197679405535

theorem tailTrace_6459559 : CollatzResearch.WordTrace tailWord_6459559 prefixEnd_6459559 3316858583076197679405535 := by
  unfold tailWord_6459559
  simp only [CollatzResearch.WordTrace]
  refine ⟨235599472005128422691685731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157066314670085615127790487 235599472005128422691685731)
  ·
    refine ⟨353399208007692634037528597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235599472005128422691685731 353399208007692634037528597)
    ·
      refine ⟨16565587875360592220509153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 353399208007692634037528597 16565587875360592220509153)
      ·
        refine ⟨12424190906520444165381865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16565587875360592220509153 12424190906520444165381865)
        ·
          refine ⟨9318143179890333124036399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12424190906520444165381865 9318143179890333124036399)
          ·
            refine ⟨13977214769835499686054599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9318143179890333124036399 13977214769835499686054599)
            ·
              refine ⟨20965822154753249529081899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13977214769835499686054599 20965822154753249529081899)
              ·
                refine ⟨31448733232129874293622849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20965822154753249529081899 31448733232129874293622849)
                ·
                  refine ⟨23586549924097405720217137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31448733232129874293622849 23586549924097405720217137)
                  ·
                    refine ⟨17689912443073054290162853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23586549924097405720217137 17689912443073054290162853)
                    ·
                      refine ⟨3316858583076197679405535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17689912443073054290162853 3316858583076197679405535)
                      ·
                        rfl

theorem cell23_6459559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_6459559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459559 prefixEnd_6459559 := by exact prefixLift 6459559
  have htrace : WordTrace (prefixWord ++ tailWord_6459559) baseStart_6459559 baseEnd_6459559 := by
    simpa [prefixWord, tailWord_6459559, baseEnd_6459559] using wordTrace_append hprefix tailTrace_6459559
  have hstable : (prefixWord ++ tailWord_6459559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459559).length < 2 ^ (prefixWord ++ tailWord_6459559).sum := by decide
  have hdescent : baseEnd_6459559 < baseStart_6459559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459615 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 6]
def baseStart_6459615 : Nat := 118140960795 + 6459615 * 2 ^ 59
def prefixEnd_6459615 : Nat := 4983230072969 + 3 ^ 40 * 6459615 * 2
def baseEnd_6459615 : Nat := 3316887337992849460305277

theorem tailTrace_6459615 : CollatzResearch.WordTrace tailWord_6459615 prefixEnd_6459615 3316887337992849460305277 := by
  unfold tailWord_6459615
  simp only [CollatzResearch.WordTrace]
  refine ⟨235601514492925544255724299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157067676328617029503816199 235601514492925544255724299)
  ·
    refine ⟨353402271739388316383586449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235601514492925544255724299 353402271739388316383586449)
    ·
      refine ⟨265051703804541237287689837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353402271739388316383586449 265051703804541237287689837)
      ·
        refine ⟨99394388926702963982883689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265051703804541237287689837 99394388926702963982883689)
        ·
          refine ⟨74545791695027222987162767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99394388926702963982883689 74545791695027222987162767)
          ·
            refine ⟨111818687542540834480744151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74545791695027222987162767 111818687542540834480744151)
            ·
              refine ⟨167728031313811251721116227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111818687542540834480744151 167728031313811251721116227)
              ·
                refine ⟨251592046970716877581674341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167728031313811251721116227 251592046970716877581674341)
                ·
                  refine ⟨47173508807009414546563939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251592046970716877581674341 47173508807009414546563939)
                  ·
                    refine ⟨70760263210514121819845909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47173508807009414546563939 70760263210514121819845909)
                    ·
                      refine ⟨3316887337992849460305277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70760263210514121819845909 3316887337992849460305277)
                      ·
                        rfl

theorem cell23_6459615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_6459615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459615 prefixEnd_6459615 := by exact prefixLift 6459615
  have htrace : WordTrace (prefixWord ++ tailWord_6459615) baseStart_6459615 baseEnd_6459615 := by
    simpa [prefixWord, tailWord_6459615, baseEnd_6459615] using wordTrace_append hprefix tailTrace_6459615
  have hstable : (prefixWord ++ tailWord_6459615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459615).length < 2 ^ (prefixWord ++ tailWord_6459615).sum := by decide
  have hdescent : baseEnd_6459615 < baseStart_6459615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459672 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 3, 5]
def baseStart_6459672 : Nat := 118140960795 + 6459672 * 2 ^ 59
def prefixEnd_6459672 : Nat := 4983230072969 + 3 ^ 40 * 6459672 * 2
def baseEnd_6459672 : Nat := 1105638868796718579097505

theorem tailTrace_6459672 : CollatzResearch.WordTrace tailWord_6459672 prefixEnd_6459672 1105638868796718579097505 := by
  unfold tailWord_6459672
  simp only [CollatzResearch.WordTrace]
  refine ⟨117801796726859521495274635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157069062302479361993699513 117801796726859521495274635)
  ·
    refine ⟨176702695090289282242911953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117801796726859521495274635 176702695090289282242911953)
    ·
      refine ⟨132527021317716961682183965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176702695090289282242911953 132527021317716961682183965)
      ·
        refine ⟨49697632994143860630818987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132527021317716961682183965 49697632994143860630818987)
        ·
          refine ⟨74546449491215790946228481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49697632994143860630818987 74546449491215790946228481)
          ·
            refine ⟨55909837118411843209671361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74546449491215790946228481 55909837118411843209671361)
            ·
              refine ⟨41932377838808882407253521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55909837118411843209671361 41932377838808882407253521)
              ·
                refine ⟨31449283379106661805440141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41932377838808882407253521 31449283379106661805440141)
                ·
                  refine ⟨11793481267164998177040053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31449283379106661805440141 11793481267164998177040053)
                  ·
                    refine ⟨1105638868796718579097505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11793481267164998177040053 1105638868796718579097505)
                    ·
                      rfl

theorem cell23_6459672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_6459672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459672 prefixEnd_6459672 := by exact prefixLift 6459672
  have htrace : WordTrace (prefixWord ++ tailWord_6459672) baseStart_6459672 baseEnd_6459672 := by
    simpa [prefixWord, tailWord_6459672, baseEnd_6459672] using wordTrace_append hprefix tailTrace_6459672
  have hstable : (prefixWord ++ tailWord_6459672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459672).length < 2 ^ (prefixWord ++ tailWord_6459672).sum := by decide
  have hdescent : baseEnd_6459672 < baseStart_6459672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459706 : List Nat := [3, 1, 1, 1, 4, 3, 3, 1, 1, 5]
def baseStart_6459706 : Nat := 118140960795 + 6459706 * 2 ^ 59
def prefixEnd_6459706 : Nat := 4983230072969 + 3 ^ 40 * 6459706 * 2
def baseEnd_6459706 : Nat := 1105644688244136201422453

theorem tailTrace_6459706 : CollatzResearch.WordTrace tailWord_6459706 prefixEnd_6459706 1105644688244136201422453 := by
  unfold tailWord_6459706
  simp only [CollatzResearch.WordTrace]
  refine ⟨58901208383898966699321743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157069889023730577864857981 58901208383898966699321743)
  ·
    refine ⟨88351812575848450048982615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58901208383898966699321743 88351812575848450048982615)
    ·
      refine ⟨132527718863772675073473923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88351812575848450048982615 132527718863772675073473923)
      ·
        refine ⟨198791578295659012610210885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132527718863772675073473923 198791578295659012610210885)
        ·
          refine ⟨37273420930436064864414541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198791578295659012610210885 37273420930436064864414541)
          ·
            refine ⟨13977532848913524324155453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37273420930436064864414541 13977532848913524324155453)
            ·
              refine ⟨5241574818342571621558295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13977532848913524324155453 5241574818342571621558295)
              ·
                refine ⟨7862362227513857432337443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241574818342571621558295 7862362227513857432337443)
                ·
                  refine ⟨11793543341270786148506165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7862362227513857432337443 11793543341270786148506165)
                  ·
                    refine ⟨1105644688244136201422453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11793543341270786148506165 1105644688244136201422453)
                    ·
                      rfl

theorem cell23_6459706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_6459706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459706 prefixEnd_6459706 := by exact prefixLift 6459706
  have htrace : WordTrace (prefixWord ++ tailWord_6459706) baseStart_6459706 baseEnd_6459706 := by
    simpa [prefixWord, tailWord_6459706, baseEnd_6459706] using wordTrace_append hprefix tailTrace_6459706
  have hstable : (prefixWord ++ tailWord_6459706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459706).length < 2 ^ (prefixWord ++ tailWord_6459706).sum := by decide
  have hdescent : baseEnd_6459706 < baseStart_6459706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459712 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 5]
def baseStart_6459712 : Nat := 118140960795 + 6459712 * 2 ^ 59
def prefixEnd_6459712 : Nat := 4983230072969 + 3 ^ 40 * 6459712 * 2
def baseEnd_6459712 : Nat := 3316937145616335580792331

theorem tailTrace_6459712 : CollatzResearch.WordTrace tailWord_6459712 prefixEnd_6459712 3316937145616335580792331 := by
  unfold tailWord_6459712
  simp only [CollatzResearch.WordTrace]
  refine ⟨117802526186787064911002695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157070034915716086548003593 117802526186787064911002695)
  ·
    refine ⟨176703789280180597366504043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117802526186787064911002695 176703789280180597366504043)
    ·
      refine ⟨265055683920270896049756065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176703789280180597366504043 265055683920270896049756065)
      ·
        refine ⟨198791762940203172037317049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265055683920270896049756065 198791762940203172037317049)
        ·
          refine ⟨149093822205152379027987787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198791762940203172037317049 149093822205152379027987787)
          ·
            refine ⟨223640733307728568541981681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149093822205152379027987787 223640733307728568541981681)
            ·
              refine ⟨167730549980796426406486261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223640733307728568541981681 167730549980796426406486261)
              ·
                refine ⟨15724739060699664975608087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167730549980796426406486261 15724739060699664975608087)
                ·
                  refine ⟨23587108591049497463412131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15724739060699664975608087 23587108591049497463412131)
                  ·
                    refine ⟨35380662886574246195118197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23587108591049497463412131 35380662886574246195118197)
                    ·
                      refine ⟨3316937145616335580792331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35380662886574246195118197 3316937145616335580792331)
                      ·
                        rfl

theorem cell23_6459712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_6459712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459712 prefixEnd_6459712 := by exact prefixLift 6459712
  have htrace : WordTrace (prefixWord ++ tailWord_6459712) baseStart_6459712 baseEnd_6459712 := by
    simpa [prefixWord, tailWord_6459712, baseEnd_6459712] using wordTrace_append hprefix tailTrace_6459712
  have hstable : (prefixWord ++ tailWord_6459712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459712).length < 2 ^ (prefixWord ++ tailWord_6459712).sum := by decide
  have hdescent : baseEnd_6459712 < baseStart_6459712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459729 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 3, 2, 3]
def baseStart_6459729 : Nat := 118140960795 + 6459729 * 2 ^ 59
def prefixEnd_6459729 : Nat := 4983230072969 + 3 ^ 40 * 6459729 * 2
def baseEnd_6459729 : Nat := 3316945874787462014279753

theorem tailTrace_6459729 : CollatzResearch.WordTrace tailWord_6459729 prefixEnd_6459729 3316945874787462014279753 := by
  unfold tailWord_6459729
  simp only [CollatzResearch.WordTrace]
  refine ⟨235605672414512541725374241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157070448276341694483582827 235605672414512541725374241)
  ·
    refine ⟨176704254310884406294030681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235605672414512541725374241 176704254310884406294030681)
    ·
      refine ⟨132528190733163304720523011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176704254310884406294030681 132528190733163304720523011)
      ·
        refine ⟨198792286099744957080784517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132528190733163304720523011 198792286099744957080784517)
        ·
          refine ⟨37273553643702179452647097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198792286099744957080784517 37273553643702179452647097)
          ·
            refine ⟨27955165232776634589485323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37273553643702179452647097 27955165232776634589485323)
            ·
              refine ⟨41932747849164951884227985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27955165232776634589485323 41932747849164951884227985)
              ·
                refine ⟨31449560886873713913170989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41932747849164951884227985 31449560886873713913170989)
                ·
                  refine ⟨11793585332577642717439121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31449560886873713913170989 11793585332577642717439121)
                  ·
                    refine ⟨8845188999433232038079341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11793585332577642717439121 8845188999433232038079341)
                    ·
                      refine ⟨3316945874787462014279753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8845188999433232038079341 3316945874787462014279753)
                      ·
                        rfl

theorem cell23_6459729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_6459729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459729 prefixEnd_6459729 := by exact prefixLift 6459729
  have htrace : WordTrace (prefixWord ++ tailWord_6459729) baseStart_6459729 baseEnd_6459729 := by
    simpa [prefixWord, tailWord_6459729, baseEnd_6459729] using wordTrace_append hprefix tailTrace_6459729
  have hstable : (prefixWord ++ tailWord_6459729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459729).length < 2 ^ (prefixWord ++ tailWord_6459729).sum := by decide
  have hdescent : baseEnd_6459729 < baseStart_6459729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459746 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_6459746 : Nat := 118140960795 + 6459746 * 2 ^ 59
def prefixEnd_6459746 : Nat := 4983230072969 + 3 ^ 40 * 6459746 * 2
def baseEnd_6459746 : Nat := 3316954603958588447767175

theorem tailTrace_6459746 : CollatzResearch.WordTrace tailWord_6459746 prefixEnd_6459746 3316954603958588447767175 := by
  unfold tailWord_6459746
  simp only [CollatzResearch.WordTrace]
  refine ⟨58901573113862738407185773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157070861636967302419162061 58901573113862738407185773)
  ·
    refine ⟨22088089917698526902694665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58901573113862738407185773 22088089917698526902694665)
    ·
      refine ⟨16566067438273895177020999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22088089917698526902694665 16566067438273895177020999)
      ·
        refine ⟨24849101157410842765531499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16566067438273895177020999 24849101157410842765531499)
        ·
          refine ⟨37273651736116264148297249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24849101157410842765531499 37273651736116264148297249)
          ·
            refine ⟨27955238802087198111222937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37273651736116264148297249 27955238802087198111222937)
            ·
              refine ⟨20966429101565398583417203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27955238802087198111222937 20966429101565398583417203)
              ·
                refine ⟨31449643652348097875125805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20966429101565398583417203 31449643652348097875125805)
                ·
                  refine ⟨11793616369630536703172177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31449643652348097875125805 11793616369630536703172177)
                  ·
                    refine ⟨8845212277222902527379133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11793616369630536703172177 8845212277222902527379133)
                    ·
                      refine ⟨3316954603958588447767175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8845212277222902527379133 3316954603958588447767175)
                      ·
                        rfl

theorem cell23_6459746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_6459746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459746 prefixEnd_6459746 := by exact prefixLift 6459746
  have htrace : WordTrace (prefixWord ++ tailWord_6459746) baseStart_6459746 baseEnd_6459746 := by
    simpa [prefixWord, tailWord_6459746, baseEnd_6459746] using wordTrace_append hprefix tailTrace_6459746
  have hstable : (prefixWord ++ tailWord_6459746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459746).length < 2 ^ (prefixWord ++ tailWord_6459746).sum := by decide
  have hdescent : baseEnd_6459746 < baseStart_6459746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459749 : List Nat := [1, 3, 1, 3, 1, 4, 3, 7]
def baseStart_6459749 : Nat := 118140960795 + 6459749 * 2 ^ 59
def prefixEnd_6459749 : Nat := 4983230072969 + 3 ^ 40 * 6459749 * 2
def baseEnd_6459749 : Nat := 122850227570390812445543

theorem tailTrace_6459749 : CollatzResearch.WordTrace tailWord_6459749 prefixEnd_6459749 122850227570390812445543 := by
  unfold tailWord_6459749
  simp only [CollatzResearch.WordTrace]
  refine ⟨235606401874440085141102301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157070934582960056760734867 235606401874440085141102301)
  ·
    refine ⟨88352400702915031927913363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235606401874440085141102301 88352400702915031927913363)
    ·
      refine ⟨132528601054372547891870045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88352400702915031927913363 132528601054372547891870045)
      ·
        refine ⟨49698225395389705459451267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132528601054372547891870045 49698225395389705459451267)
        ·
          refine ⟨74547338093084558189176901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49698225395389705459451267 74547338093084558189176901)
          ·
            refine ⟨13977625892453354660470669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74547338093084558189176901 13977625892453354660470669)
            ·
              refine ⟨5241609709670007997676501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13977625892453354660470669 5241609709670007997676501)
              ·
                refine ⟨122850227570390812445543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5241609709670007997676501 122850227570390812445543)
                ·
                  rfl

theorem cell23_6459749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 7].length) (baseStart_6459749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459749 prefixEnd_6459749 := by exact prefixLift 6459749
  have htrace : WordTrace (prefixWord ++ tailWord_6459749) baseStart_6459749 baseEnd_6459749 := by
    simpa [prefixWord, tailWord_6459749, baseEnd_6459749] using wordTrace_append hprefix tailTrace_6459749
  have hstable : (prefixWord ++ tailWord_6459749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459749).length < 2 ^ (prefixWord ++ tailWord_6459749).sum := by decide
  have hdescent : baseEnd_6459749 < baseStart_6459749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459760 : List Nat := [2, 1, 1, 1, 4, 4, 2, 3, 1, 2, 2]
def baseStart_6459760 : Nat := 118140960795 + 6459760 * 2 ^ 59
def prefixEnd_6459760 : Nat := 4983230072969 + 3 ^ 40 * 6459760 * 2
def baseEnd_6459760 : Nat := 3316961792687751392992111

theorem tailTrace_6459760 : CollatzResearch.WordTrace tailWord_6459760 prefixEnd_6459760 3316961792687751392992111 := by
  unfold tailWord_6459760
  simp only [CollatzResearch.WordTrace]
  refine ⟨117803401538700117009876367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157071202051600156013168489 117803401538700117009876367)
  ·
    refine ⟨176705102308050175514814551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117803401538700117009876367 176705102308050175514814551)
    ·
      refine ⟨265057653462075263272221827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176705102308050175514814551 265057653462075263272221827)
      ·
        refine ⟨397586480193112894908332741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265057653462075263272221827 397586480193112894908332741)
        ·
          refine ⟨74547465036208667795312389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397586480193112894908332741 74547465036208667795312389)
          ·
            refine ⟨13977649694289125211621073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74547465036208667795312389 13977649694289125211621073)
            ·
              refine ⟨10483237270716843908715805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13977649694289125211621073 10483237270716843908715805)
              ·
                refine ⟨3931213976518816465768427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10483237270716843908715805 3931213976518816465768427)
                ·
                  refine ⟨5896820964778224698652641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3931213976518816465768427 5896820964778224698652641)
                  ·
                    refine ⟨4422615723583668523989481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5896820964778224698652641 4422615723583668523989481)
                    ·
                      refine ⟨3316961792687751392992111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422615723583668523989481 3316961792687751392992111)
                      ·
                        rfl

theorem cell23_6459760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 1, 2, 2].length) (baseStart_6459760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459760 prefixEnd_6459760 := by exact prefixLift 6459760
  have htrace : WordTrace (prefixWord ++ tailWord_6459760) baseStart_6459760 baseEnd_6459760 := by
    simpa [prefixWord, tailWord_6459760, baseEnd_6459760] using wordTrace_append hprefix tailTrace_6459760
  have hstable : (prefixWord ++ tailWord_6459760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459760).length < 2 ^ (prefixWord ++ tailWord_6459760).sum := by decide
  have hdescent : baseEnd_6459760 < baseStart_6459760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459766 : List Nat := [5, 1, 1, 4, 1, 1, 10]
def baseStart_6459766 : Nat := 118140960795 + 6459766 * 2 ^ 59
def prefixEnd_6459766 : Nat := 4983230072969 + 3 ^ 40 * 6459766 * 2
def baseEnd_6459766 : Nat := 40950183624341708265643

theorem tailTrace_6459766 : CollatzResearch.WordTrace tailWord_6459766 prefixEnd_6459766 40950183624341708265643 := by
  unfold tailWord_6459766
  simp only [CollatzResearch.WordTrace]
  refine ⟨14725438869711156065279447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157071347943585664696314101 14725438869711156065279447)
  ·
    refine ⟨22088158304566734097919171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14725438869711156065279447 22088158304566734097919171)
    ·
      refine ⟨33132237456850101146878757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22088158304566734097919171 33132237456850101146878757)
      ·
        refine ⟨6212294523159393965039767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33132237456850101146878757 6212294523159393965039767)
        ·
          refine ⟨9318441784739090947559651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6212294523159393965039767 9318441784739090947559651)
          ·
            refine ⟨13977662677108636421339477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9318441784739090947559651 13977662677108636421339477)
            ·
              refine ⟨40950183624341708265643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13977662677108636421339477 40950183624341708265643)
              ·
                rfl

theorem cell23_6459766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 10].length) (baseStart_6459766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459766 prefixEnd_6459766 := by exact prefixLift 6459766
  have htrace : WordTrace (prefixWord ++ tailWord_6459766) baseStart_6459766 baseEnd_6459766 := by
    simpa [prefixWord, tailWord_6459766, baseEnd_6459766] using wordTrace_append hprefix tailTrace_6459766
  have hstable : (prefixWord ++ tailWord_6459766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459766).length < 2 ^ (prefixWord ++ tailWord_6459766).sum := by decide
  have hdescent : baseEnd_6459766 < baseStart_6459766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459772 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_6459772 : Nat := 118140960795 + 6459772 * 2 ^ 59
def prefixEnd_6459772 : Nat := 4983230072969 + 3 ^ 40 * 6459772 * 2
def baseEnd_6459772 : Nat := 3316967954455605346042055

theorem tailTrace_6459772 : CollatzResearch.WordTrace tailWord_6459772 prefixEnd_6459772 3316967954455605346042055 := by
  unfold tailWord_6459772
  simp only [CollatzResearch.WordTrace]
  refine ⟨117803620376678380034594785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157071493835571173379459713 117803620376678380034594785)
  ·
    refine ⟨88352715282508785025946089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117803620376678380034594785 88352715282508785025946089)
    ·
      refine ⟨66264536461881588769459567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88352715282508785025946089 66264536461881588769459567)
      ·
        refine ⟨99396804692822383154189351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66264536461881588769459567 99396804692822383154189351)
        ·
          refine ⟨149095207039233574731284027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99396804692822383154189351 149095207039233574731284027)
          ·
            refine ⟨223642810558850362096926041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149095207039233574731284027 223642810558850362096926041)
            ·
              refine ⟨167732107919137771572694531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223642810558850362096926041 167732107919137771572694531)
              ·
                refine ⟨251598161878706657359041797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167732107919137771572694531 251598161878706657359041797)
                ·
                  refine ⟨47174655352257498254820337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251598161878706657359041797 47174655352257498254820337)
                  ·
                    refine ⟨35380991514193123691115253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47174655352257498254820337 35380991514193123691115253)
                    ·
                      refine ⟨3316967954455605346042055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35380991514193123691115253 3316967954455605346042055)
                      ·
                        rfl

theorem cell23_6459772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_6459772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459772 prefixEnd_6459772 := by exact prefixLift 6459772
  have htrace : WordTrace (prefixWord ++ tailWord_6459772) baseStart_6459772 baseEnd_6459772 := by
    simpa [prefixWord, tailWord_6459772, baseEnd_6459772] using wordTrace_append hprefix tailTrace_6459772
  have hstable : (prefixWord ++ tailWord_6459772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459772).length < 2 ^ (prefixWord ++ tailWord_6459772).sum := by decide
  have hdescent : baseEnd_6459772 < baseStart_6459772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459806 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_6459806 : Nat := 118140960795 + 6459806 * 2 ^ 59
def prefixEnd_6459806 : Nat := 4983230072969 + 3 ^ 40 * 6459806 * 2
def baseEnd_6459806 : Nat := 3316985412797858213016899

theorem tailTrace_6459806 : CollatzResearch.WordTrace tailWord_6459806 prefixEnd_6459806 3316985412797858213016899 := by
  unfold tailWord_6459806
  simp only [CollatzResearch.WordTrace]
  refine ⟨29451060104404197984490909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157072320556822389250618181 29451060104404197984490909)
  ·
    refine ⟨11044147539151574244184091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29451060104404197984490909 11044147539151574244184091)
    ·
      refine ⟨16566221308727361366276137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11044147539151574244184091 16566221308727361366276137)
      ·
        refine ⟨12424665981545521024707103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16566221308727361366276137 12424665981545521024707103)
        ·
          refine ⟨18636998972318281537060655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12424665981545521024707103 18636998972318281537060655)
          ·
            refine ⟨27955498458477422305590983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18636998972318281537060655 27955498458477422305590983)
            ·
              refine ⟨41933247687716133458386475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27955498458477422305590983 41933247687716133458386475)
              ·
                refine ⟨62899871531574200187579713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41933247687716133458386475 62899871531574200187579713)
                ·
                  refine ⟨47174903648680650140684785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62899871531574200187579713 47174903648680650140684785)
                  ·
                    refine ⟨35381177736510487605513589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47174903648680650140684785 35381177736510487605513589)
                    ·
                      refine ⟨3316985412797858213016899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35381177736510487605513589 3316985412797858213016899)
                      ·
                        rfl

theorem cell23_6459806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_6459806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459806 prefixEnd_6459806 := by exact prefixLift 6459806
  have htrace : WordTrace (prefixWord ++ tailWord_6459806) baseStart_6459806 baseEnd_6459806 := by
    simpa [prefixWord, tailWord_6459806, baseEnd_6459806] using wordTrace_append hprefix tailTrace_6459806
  have hstable : (prefixWord ++ tailWord_6459806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459806).length < 2 ^ (prefixWord ++ tailWord_6459806).sum := by decide
  have hdescent : baseEnd_6459806 < baseStart_6459806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459832 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_6459832 : Nat := 118140960795 + 6459832 * 2 ^ 59
def prefixEnd_6459832 : Nat := 4983230072969 + 3 ^ 40 * 6459832 * 2
def baseEnd_6459832 : Nat := 3316998763294875111291779

theorem tailTrace_6459832 : CollatzResearch.WordTrace tailWord_6459832 prefixEnd_6459832 3316998763294875111291779 := by
  unfold tailWord_6459832
  simp only [CollatzResearch.WordTrace]
  refine ⟨117804714566569695158186875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157072952755426260210915833 117804714566569695158186875)
  ·
    refine ⟨176707071849854542737280313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117804714566569695158186875 176707071849854542737280313)
    ·
      refine ⟨132530303887390907052960235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176707071849854542737280313 132530303887390907052960235)
      ·
        refine ⟨198795455831086360579440353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132530303887390907052960235 198795455831086360579440353)
        ·
          refine ⟨149096591873314770434580265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198795455831086360579440353 149096591873314770434580265)
          ·
            refine ⟨111822443904986077825935199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149096591873314770434580265 111822443904986077825935199)
            ·
              refine ⟨167733665857479116738902799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111822443904986077825935199 167733665857479116738902799)
              ·
                refine ⟨251600498786218675108354199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167733665857479116738902799 251600498786218675108354199)
                ·
                  refine ⟨377400748179328012662531299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251600498786218675108354199 377400748179328012662531299)
                  ·
                    refine ⟨566101122268992018993796949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 377400748179328012662531299 566101122268992018993796949)
                    ·
                      refine ⟨3316998763294875111291779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 566101122268992018993796949 3316998763294875111291779)
                      ·
                        rfl

theorem cell23_6459832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_6459832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459832 prefixEnd_6459832 := by exact prefixLift 6459832
  have htrace : WordTrace (prefixWord ++ tailWord_6459832) baseStart_6459832 baseEnd_6459832 := by
    simpa [prefixWord, tailWord_6459832, baseEnd_6459832] using wordTrace_append hprefix tailTrace_6459832
  have hstable : (prefixWord ++ tailWord_6459832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459832).length < 2 ^ (prefixWord ++ tailWord_6459832).sum := by decide
  have hdescent : baseEnd_6459832 < baseStart_6459832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459833 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 4, 2, 2]
def baseStart_6459833 : Nat := 118140960795 + 6459833 * 2 ^ 59
def prefixEnd_6459833 : Nat := 4983230072969 + 3 ^ 40 * 6459833 * 2
def baseEnd_6459833 : Nat := 3316999276775529607379275

theorem tailTrace_6459833 : CollatzResearch.WordTrace tailWord_6459833 prefixEnd_6459833 3316999276775529607379275 := by
  unfold tailWord_6459833
  simp only [CollatzResearch.WordTrace]
  refine ⟨235609465606135767487160153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157072977070757178324773435 235609465606135767487160153)
  ·
    refine ⟨176707099204601825615370115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235609465606135767487160153 176707099204601825615370115)
    ·
      refine ⟨265060648806902738423055173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176707099204601825615370115 265060648806902738423055173)
      ·
        refine ⟨49698871651294263454322845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265060648806902738423055173 49698871651294263454322845)
        ·
          refine ⟨18637076869235348795371067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49698871651294263454322845 18637076869235348795371067)
          ·
            refine ⟨27955615303853023193056601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18637076869235348795371067 27955615303853023193056601)
            ·
              refine ⟨20966711477889767394792451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27955615303853023193056601 20966711477889767394792451)
              ·
                refine ⟨31450067216834651092188677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20966711477889767394792451 31450067216834651092188677)
                ·
                  refine ⟨5896887603156497079785377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31450067216834651092188677 5896887603156497079785377)
                  ·
                    refine ⟨4422665702367372809839033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5896887603156497079785377 4422665702367372809839033)
                    ·
                      refine ⟨3316999276775529607379275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422665702367372809839033 3316999276775529607379275)
                      ·
                        rfl

theorem cell23_6459833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_6459833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459833 prefixEnd_6459833 := by exact prefixLift 6459833
  have htrace : WordTrace (prefixWord ++ tailWord_6459833) baseStart_6459833 baseEnd_6459833 := by
    simpa [prefixWord, tailWord_6459833, baseEnd_6459833] using wordTrace_append hprefix tailTrace_6459833
  have hstable : (prefixWord ++ tailWord_6459833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459833).length < 2 ^ (prefixWord ++ tailWord_6459833).sum := by decide
  have hdescent : baseEnd_6459833 < baseStart_6459833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459844 : List Nat := [2, 3, 3, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_6459844 : Nat := 118140960795 + 6459844 * 2 ^ 59
def prefixEnd_6459844 : Nat := 4983230072969 + 3 ^ 40 * 6459844 * 2
def baseEnd_6459844 : Nat := 3317004925062729064341725

theorem tailTrace_6459844 : CollatzResearch.WordTrace tailWord_6459844 prefixEnd_6459844 3317004925062729064341725 := by
  unfold tailWord_6459844
  simp only [CollatzResearch.WordTrace]
  refine ⟨117804933404547958182905293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157073244539397277577207057 117804933404547958182905293)
  ·
    refine ⟨44176850026705484318589485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117804933404547958182905293 44176850026705484318589485)
    ·
      refine ⟨16566318760014556619471057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44176850026705484318589485 16566318760014556619471057)
      ·
        refine ⟨12424739070010917464603293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16566318760014556619471057 12424739070010917464603293)
        ·
          refine ⟨4659277151254094049226235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12424739070010917464603293 4659277151254094049226235)
          ·
            refine ⟨6988915726881141073839353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659277151254094049226235 6988915726881141073839353)
            ·
              refine ⟨5241686795160855805379515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6988915726881141073839353 5241686795160855805379515)
              ·
                refine ⟨7862530192741283708069273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241686795160855805379515 7862530192741283708069273)
                ·
                  refine ⟨5896897644555962781051955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7862530192741283708069273 5896897644555962781051955)
                  ·
                    refine ⟨8845346466833944171577933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5896897644555962781051955 8845346466833944171577933)
                    ·
                      refine ⟨3317004925062729064341725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8845346466833944171577933 3317004925062729064341725)
                      ·
                        rfl

theorem cell23_6459844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_6459844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459844 prefixEnd_6459844 := by exact prefixLift 6459844
  have htrace : WordTrace (prefixWord ++ tailWord_6459844) baseStart_6459844 baseEnd_6459844 := by
    simpa [prefixWord, tailWord_6459844, baseEnd_6459844] using wordTrace_append hprefix tailTrace_6459844
  have hstable : (prefixWord ++ tailWord_6459844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459844).length < 2 ^ (prefixWord ++ tailWord_6459844).sum := by decide
  have hdescent : baseEnd_6459844 < baseStart_6459844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459849 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 2, 3, 3]
def baseStart_6459849 : Nat := 118140960795 + 6459849 * 2 ^ 59
def prefixEnd_6459849 : Nat := 4983230072969 + 3 ^ 40 * 6459849 * 2
def baseEnd_6459849 : Nat := 3317007492466001544779201

theorem tailTrace_6459849 : CollatzResearch.WordTrace tailWord_6459849 prefixEnd_6459849 3317007492466001544779201 := by
  unfold tailWord_6459849
  simp only [CollatzResearch.WordTrace]
  refine ⟨235610049174077802219742601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157073366116051868146495067 235610049174077802219742601)
  ·
    refine ⟨176707536880558351664806951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235610049174077802219742601 176707536880558351664806951)
    ·
      refine ⟨265061305320837527497210427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176707536880558351664806951 265061305320837527497210427)
      ·
        refine ⟨397591957981256291245815641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265061305320837527497210427 397591957981256291245815641)
        ·
          refine ⟨298193968485942218434361731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397591957981256291245815641 298193968485942218434361731)
          ·
            refine ⟨447290952728913327651542597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298193968485942218434361731 447290952728913327651542597)
            ·
              refine ⟨83867053636671248934664237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 447290952728913327651542597 83867053636671248934664237)
              ·
                refine ⟨31450145113751718350499089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83867053636671248934664237 31450145113751718350499089)
                ·
                  refine ⟨23587608835313788762874317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31450145113751718350499089 23587608835313788762874317)
                  ·
                    refine ⟨8845353313242670786077869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23587608835313788762874317 8845353313242670786077869)
                    ·
                      refine ⟨3317007492466001544779201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8845353313242670786077869 3317007492466001544779201)
                      ·
                        rfl

theorem cell23_6459849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 3, 3].length) (baseStart_6459849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459849 prefixEnd_6459849 := by exact prefixLift 6459849
  have htrace : WordTrace (prefixWord ++ tailWord_6459849) baseStart_6459849 baseEnd_6459849 := by
    simpa [prefixWord, tailWord_6459849, baseEnd_6459849] using wordTrace_append hprefix tailTrace_6459849
  have hstable : (prefixWord ++ tailWord_6459849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459849).length < 2 ^ (prefixWord ++ tailWord_6459849).sum := by decide
  have hdescent : baseEnd_6459849 < baseStart_6459849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459879 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6459879 : Nat := 118140960795 + 6459879 * 2 ^ 59
def prefixEnd_6459879 : Nat := 4983230072969 + 3 ^ 40 * 6459879 * 2
def baseEnd_6459879 : Nat := 3317022896885636427404063

theorem tailTrace_6459879 : CollatzResearch.WordTrace tailWord_6459879 prefixEnd_6459879 3317022896885636427404063 := by
  unfold tailWord_6459879
  simp only [CollatzResearch.WordTrace]
  refine ⟨235611143363969117343334691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157074095575979411562223127 235611143363969117343334691)
  ·
    refine ⟨353416715045953676015002037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235611143363969117343334691 353416715045953676015002037)
    ·
      refine ⟨33132817035558157126406441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 353416715045953676015002037 33132817035558157126406441)
      ·
        refine ⟨24849612776668617844804831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33132817035558157126406441 24849612776668617844804831)
        ·
          refine ⟨37274419165002926767207247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24849612776668617844804831 37274419165002926767207247)
          ·
            refine ⟨55911628747504390150810871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37274419165002926767207247 55911628747504390150810871)
            ·
              refine ⟨83867443121256585226216307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55911628747504390150810871 83867443121256585226216307)
              ·
                refine ⟨125801164681884877839324461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83867443121256585226216307 125801164681884877839324461)
                ·
                  refine ⟨47175436755706829189746673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125801164681884877839324461 47175436755706829189746673)
                  ·
                    refine ⟨35381577566780121892310005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47175436755706829189746673 35381577566780121892310005)
                    ·
                      refine ⟨3317022896885636427404063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35381577566780121892310005 3317022896885636427404063)
                      ·
                        rfl

theorem cell23_6459879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6459879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459879 prefixEnd_6459879 := by exact prefixLift 6459879
  have htrace : WordTrace (prefixWord ++ tailWord_6459879) baseStart_6459879 baseEnd_6459879 := by
    simpa [prefixWord, tailWord_6459879, baseEnd_6459879] using wordTrace_append hprefix tailTrace_6459879
  have hstable : (prefixWord ++ tailWord_6459879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459879).length < 2 ^ (prefixWord ++ tailWord_6459879).sum := by decide
  have hdescent : baseEnd_6459879 < baseStart_6459879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459886 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_6459886 : Nat := 118140960795 + 6459886 * 2 ^ 59
def prefixEnd_6459886 : Nat := 4983230072969 + 3 ^ 40 * 6459886 * 2
def baseEnd_6459886 : Nat := 1105675497083405966672177

theorem tailTrace_6459886 : CollatzResearch.WordTrace tailWord_6459886 prefixEnd_6459886 1105675497083405966672177 := by
  unfold tailWord_6459886
  simp only [CollatzResearch.WordTrace]
  refine ⟨29451424834367969692354939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157074265783295838359226341 29451424834367969692354939)
  ·
    refine ⟨44177137251551954538532409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29451424834367969692354939 44177137251551954538532409)
    ·
      refine ⟨33132852938663965903899307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44177137251551954538532409 33132852938663965903899307)
      ·
        refine ⟨49699279407995948855848961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33132852938663965903899307 49699279407995948855848961)
        ·
          refine ⟨37274459555996961641886721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49699279407995948855848961 37274459555996961641886721)
          ·
            refine ⟨27955844666997721231415041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37274459555996961641886721 27955844666997721231415041)
            ·
              refine ⟨20966883500248290923561281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27955844666997721231415041 20966883500248290923561281)
              ·
                refine ⟨15725162625186218192670961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20966883500248290923561281 15725162625186218192670961)
                ·
                  refine ⟨11793871968889663644503221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15725162625186218192670961 11793871968889663644503221)
                  ·
                    refine ⟨1105675497083405966672177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11793871968889663644503221 1105675497083405966672177)
                    ·
                      rfl

theorem cell23_6459886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_6459886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459886 prefixEnd_6459886 := by exact prefixLift 6459886
  have htrace : WordTrace (prefixWord ++ tailWord_6459886) baseStart_6459886 baseEnd_6459886 := by
    simpa [prefixWord, tailWord_6459886, baseEnd_6459886] using wordTrace_append hprefix tailTrace_6459886
  have hstable : (prefixWord ++ tailWord_6459886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459886).length < 2 ^ (prefixWord ++ tailWord_6459886).sum := by decide
  have hdescent : baseEnd_6459886 < baseStart_6459886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459916 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 5, 4]
def baseStart_6459916 : Nat := 118140960795 + 6459916 * 2 ^ 59
def prefixEnd_6459916 : Nat := 4983230072969 + 3 ^ 40 * 6459916 * 2
def baseEnd_6459916 : Nat := 1105680631889950927547131

theorem tailTrace_6459916 : CollatzResearch.WordTrace tailWord_6459916 prefixEnd_6459916 1105680631889950927547131 := by
  unfold tailWord_6459916
  simp only [CollatzResearch.WordTrace]
  refine ⟨117806246432417536331215801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157074995243223381774954401 117806246432417536331215801)
  ·
    refine ⟨88354684824313152248411851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117806246432417536331215801 88354684824313152248411851)
    ·
      refine ⟨132532027236469728372617777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88354684824313152248411851 132532027236469728372617777)
      ·
        refine ⟨99399020427352296279463333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132532027236469728372617777 99399020427352296279463333)
        ·
          refine ⟨18637316330128555552399375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99399020427352296279463333 18637316330128555552399375)
          ·
            refine ⟨27955974495192833328599063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18637316330128555552399375 27955974495192833328599063)
            ·
              refine ⟨41933961742789249992898595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27955974495192833328599063 41933961742789249992898595)
              ·
                refine ⟨62900942614183874989347893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41933961742789249992898595 62900942614183874989347893)
                ·
                  refine ⟨5896963370079738280251365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62900942614183874989347893 5896963370079738280251365)
                  ·
                    refine ⟨1105680631889950927547131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5896963370079738280251365 1105680631889950927547131)
                    ·
                      rfl

theorem cell23_6459916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_6459916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459916 prefixEnd_6459916 := by exact prefixLift 6459916
  have htrace : WordTrace (prefixWord ++ tailWord_6459916) baseStart_6459916 baseEnd_6459916 := by
    simpa [prefixWord, tailWord_6459916, baseEnd_6459916] using wordTrace_append hprefix tailTrace_6459916
  have hstable : (prefixWord ++ tailWord_6459916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459916).length < 2 ^ (prefixWord ++ tailWord_6459916).sum := by decide
  have hdescent : baseEnd_6459916 < baseStart_6459916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459946 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 8]
def baseStart_6459946 : Nat := 118140960795 + 6459946 * 2 ^ 59
def prefixEnd_6459946 : Nat := 4983230072969 + 3 ^ 40 * 6459946 * 2
def baseEnd_6459946 : Nat := 368561922232165296140695

theorem tailTrace_6459946 : CollatzResearch.WordTrace tailWord_6459946 prefixEnd_6459946 368561922232165296140695 := by
  unfold tailWord_6459946
  simp only [CollatzResearch.WordTrace]
  refine ⟨58903396763681596946505923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157075724703150925190682461 58903396763681596946505923)
  ·
    refine ⟨88355095145522395419758885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58903396763681596946505923 88355095145522395419758885)
    ·
      refine ⟨16566580339785449141204791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88355095145522395419758885 16566580339785449141204791)
      ·
        refine ⟨24849870509678173711807187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16566580339785449141204791 24849870509678173711807187)
        ·
          refine ⟨37274805764517260567710781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24849870509678173711807187 37274805764517260567710781)
          ·
            refine ⟨13978052161693972712891543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37274805764517260567710781 13978052161693972712891543)
            ·
              refine ⟨20967078242540959069337315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13978052161693972712891543 20967078242540959069337315)
              ·
                refine ⟨31450617363811438604005973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20967078242540959069337315 31450617363811438604005973)
                ·
                  refine ⟨368561922232165296140695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31450617363811438604005973 368561922232165296140695)
                  ·
                    rfl

theorem cell23_6459946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_6459946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459946 prefixEnd_6459946 := by exact prefixLift 6459946
  have htrace : WordTrace (prefixWord ++ tailWord_6459946) baseStart_6459946 baseEnd_6459946 := by
    simpa [prefixWord, tailWord_6459946, baseEnd_6459946] using wordTrace_append hprefix tailTrace_6459946
  have hstable : (prefixWord ++ tailWord_6459946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459946).length < 2 ^ (prefixWord ++ tailWord_6459946).sum := by decide
  have hdescent : baseEnd_6459946 < baseStart_6459946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459950 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_6459950 : Nat := 118140960795 + 6459950 * 2 ^ 59
def prefixEnd_6459950 : Nat := 4983230072969 + 3 ^ 40 * 6459950 * 2
def baseEnd_6459950 : Nat := 1105686451337368549872079

theorem tailTrace_6459950 : CollatzResearch.WordTrace tailWord_6459950 prefixEnd_6459950 1105686451337368549872079 := by
  unfold tailWord_6459950
  simp only [CollatzResearch.WordTrace]
  refine ⟨29451716618338987058646163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157075821964474597646112869 29451716618338987058646163)
  ·
    refine ⟨44177574927508480587969245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29451716618338987058646163 44177574927508480587969245)
    ·
      refine ⟨16566590597815680220488467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44177574927508480587969245 16566590597815680220488467)
      ·
        refine ⟨24849885896723520330732701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16566590597815680220488467 24849885896723520330732701)
        ·
          refine ⟨9318707211271320124024763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24849885896723520330732701 9318707211271320124024763)
          ·
            refine ⟨13978060816906980186037145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9318707211271320124024763 13978060816906980186037145)
            ·
              refine ⟨10483545612680235139527859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13978060816906980186037145 10483545612680235139527859)
              ·
                refine ⟨15725318419020352709291789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10483545612680235139527859 15725318419020352709291789)
                ·
                  refine ⟨5896994407132632265984421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15725318419020352709291789 5896994407132632265984421)
                  ·
                    refine ⟨1105686451337368549872079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5896994407132632265984421 1105686451337368549872079)
                    ·
                      rfl

theorem cell23_6459950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_6459950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459950 prefixEnd_6459950 := by exact prefixLift 6459950
  have htrace : WordTrace (prefixWord ++ tailWord_6459950) baseStart_6459950 baseEnd_6459950 := by
    simpa [prefixWord, tailWord_6459950, baseEnd_6459950] using wordTrace_append hprefix tailTrace_6459950
  have hstable : (prefixWord ++ tailWord_6459950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459950).length < 2 ^ (prefixWord ++ tailWord_6459950).sum := by decide
  have hdescent : baseEnd_6459950 < baseStart_6459950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459973 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 3, 1, 3]
def baseStart_6459973 : Nat := 118140960795 + 6459973 * 2 ^ 59
def prefixEnd_6459973 : Nat := 4983230072969 + 3 ^ 40 * 6459973 * 2
def baseEnd_6459973 : Nat := 3317071164067159059628631

theorem tailTrace_6459973 : CollatzResearch.WordTrace tailWord_6459973 prefixEnd_6459973 3317071164067159059628631 := by
  unfold tailWord_6459973
  simp only [CollatzResearch.WordTrace]
  refine ⟨235614571825628571397256573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157076381217085714264837715 235614571825628571397256573)
  ·
    refine ⟨88355464434610714273971215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235614571825628571397256573 88355464434610714273971215)
    ·
      refine ⟨132533196651916071410956823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88355464434610714273971215 132533196651916071410956823)
      ·
        refine ⟨198799794977874107116435235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132533196651916071410956823 198799794977874107116435235)
        ·
          refine ⟨298199692466811160674652853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198799794977874107116435235 298199692466811160674652853)
          ·
            refine ⟨27956221168763546313248705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 298199692466811160674652853 27956221168763546313248705)
            ·
              refine ⟨20967165876572659734936529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27956221168763546313248705 20967165876572659734936529)
              ·
                refine ⟨15725374407429494801202397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20967165876572659734936529 15725374407429494801202397)
                ·
                  refine ⟨5897015402786060550450899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15725374407429494801202397 5897015402786060550450899)
                  ·
                    refine ⟨8845523104179090825676349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5897015402786060550450899 8845523104179090825676349)
                    ·
                      refine ⟨3317071164067159059628631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8845523104179090825676349 3317071164067159059628631)
                      ·
                        rfl

theorem cell23_6459973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_6459973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459973 prefixEnd_6459973 := by exact prefixLift 6459973
  have htrace : WordTrace (prefixWord ++ tailWord_6459973) baseStart_6459973 baseEnd_6459973 := by
    simpa [prefixWord, tailWord_6459973, baseEnd_6459973] using wordTrace_append hprefix tailTrace_6459973
  have hstable : (prefixWord ++ tailWord_6459973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459973).length < 2 ^ (prefixWord ++ tailWord_6459973).sum := by decide
  have hdescent : baseEnd_6459973 < baseStart_6459973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460033 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_6460033 : Nat := 118140960795 + 6460033 * 2 ^ 59
def prefixEnd_6460033 : Nat := 4983230072969 + 3 ^ 40 * 6460033 * 2
def baseEnd_6460033 : Nat := 3317101972906428824878355

theorem tailTrace_6460033 : CollatzResearch.WordTrace tailWord_6460033 prefixEnd_6460033 3317101972906428824878355 := by
  unfold tailWord_6460033
  simp only [CollatzResearch.WordTrace]
  refine ⟨235616760205411201644440753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157077840136940801096293835 235616760205411201644440753)
  ·
    refine ⟨176712570154058401233330565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235616760205411201644440753 176712570154058401233330565)
    ·
      refine ⟨33133606903885950231249481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176712570154058401233330565 33133606903885950231249481)
      ·
        refine ⟨24850205177914462673437111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33133606903885950231249481 24850205177914462673437111)
        ·
          refine ⟨37275307766871694010155667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24850205177914462673437111 37275307766871694010155667)
          ·
            refine ⟨55912961650307541015233501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37275307766871694010155667 55912961650307541015233501)
            ·
              refine ⟨20967360618865327880712563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55912961650307541015233501 20967360618865327880712563)
              ·
                refine ⟨31451040928297991821068845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20967360618865327880712563 31451040928297991821068845)
                ·
                  refine ⟨11794140348111746932900817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31451040928297991821068845 11794140348111746932900817)
                  ·
                    refine ⟨8845605261083810199675613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11794140348111746932900817 8845605261083810199675613)
                    ·
                      refine ⟨3317101972906428824878355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8845605261083810199675613 3317101972906428824878355)
                      ·
                        rfl

theorem cell23_6460033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_6460033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460033 prefixEnd_6460033 := by exact prefixLift 6460033
  have htrace : WordTrace (prefixWord ++ tailWord_6460033) baseStart_6460033 baseEnd_6460033 := by
    simpa [prefixWord, tailWord_6460033, baseEnd_6460033] using wordTrace_append hprefix tailTrace_6460033
  have hstable : (prefixWord ++ tailWord_6460033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460033).length < 2 ^ (prefixWord ++ tailWord_6460033).sum := by decide
  have hdescent : baseEnd_6460033 < baseStart_6460033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460036 : List Nat := [2, 3, 2, 1, 3, 1, 2, 9]
def baseStart_6460036 : Nat := 118140960795 + 6460036 * 2 ^ 59
def prefixEnd_6460036 : Nat := 4983230072969 + 3 ^ 40 * 6460036 * 2
def baseEnd_6460036 : Nat := 122855685679570085671883

theorem tailTrace_6460036 : CollatzResearch.WordTrace tailWord_6460036 prefixEnd_6460036 122855685679570085671883 := by
  unfold tailWord_6460036
  simp only [CollatzResearch.WordTrace]
  refine ⟨117808434812200166578399981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157077913082933555437866641 117808434812200166578399981)
  ·
    refine ⟨44178163054575062466899993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117808434812200166578399981 44178163054575062466899993)
    ·
      refine ⟨33133622290931296850174995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44178163054575062466899993 33133622290931296850174995)
      ·
        refine ⟨49700433436396945275262493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33133622290931296850174995 49700433436396945275262493)
        ·
          refine ⟨18637662538648854478223435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49700433436396945275262493 18637662538648854478223435)
          ·
            refine ⟨27956493807973281717335153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18637662538648854478223435 27956493807973281717335153)
            ·
              refine ⟨20967370355979961288001365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27956493807973281717335153 20967370355979961288001365)
              ·
                refine ⟨122855685679570085671883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20967370355979961288001365 122855685679570085671883)
                ·
                  rfl

theorem cell23_6460036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 9].length) (baseStart_6460036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460036 prefixEnd_6460036 := by exact prefixLift 6460036
  have htrace : WordTrace (prefixWord ++ tailWord_6460036) baseStart_6460036 baseEnd_6460036 := by
    simpa [prefixWord, tailWord_6460036, baseEnd_6460036] using wordTrace_append hprefix tailTrace_6460036
  have hstable : (prefixWord ++ tailWord_6460036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460036).length < 2 ^ (prefixWord ++ tailWord_6460036).sum := by decide
  have hdescent : baseEnd_6460036 < baseStart_6460036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460050 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_6460050 : Nat := 118140960795 + 6460050 * 2 ^ 59
def prefixEnd_6460050 : Nat := 4983230072969 + 3 ^ 40 * 6460050 * 2
def baseEnd_6460050 : Nat := 3317110702077555258365777

theorem tailTrace_6460050 : CollatzResearch.WordTrace tailWord_6460050 prefixEnd_6460050 3317110702077555258365777 := by
  unfold tailWord_6460050
  simp only [CollatzResearch.WordTrace]
  refine ⟨58904345061587403386952401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157078253497566409031873069 58904345061587403386952401)
  ·
    refine ⟨44178258796190552540214301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58904345061587403386952401 44178258796190552540214301)
    ·
      refine ⟨16566847048571457202580363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44178258796190552540214301 16566847048571457202580363)
      ·
        refine ⟨24850270572857185803870545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16566847048571457202580363 24850270572857185803870545)
        ·
          refine ⟨18637702929642889352902909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24850270572857185803870545 18637702929642889352902909)
          ·
            refine ⟨6989138598616083507338591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18637702929642889352902909 6989138598616083507338591)
            ·
              refine ⟨10483707897924125261007887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6989138598616083507338591 10483707897924125261007887)
              ·
                refine ⟨15725561846886187891511831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10483707897924125261007887 15725561846886187891511831)
                ·
                  refine ⟨23588342770329281837267747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15725561846886187891511831 23588342770329281837267747)
                  ·
                    refine ⟨35382514155493922755901621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23588342770329281837267747 35382514155493922755901621)
                    ·
                      refine ⟨3317110702077555258365777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35382514155493922755901621 3317110702077555258365777)
                      ·
                        rfl

theorem cell23_6460050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_6460050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460050 prefixEnd_6460050 := by exact prefixLift 6460050
  have htrace : WordTrace (prefixWord ++ tailWord_6460050) baseStart_6460050 baseEnd_6460050 := by
    simpa [prefixWord, tailWord_6460050, baseEnd_6460050] using wordTrace_append hprefix tailTrace_6460050
  have hstable : (prefixWord ++ tailWord_6460050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460050).length < 2 ^ (prefixWord ++ tailWord_6460050).sum := by decide
  have hdescent : baseEnd_6460050 < baseStart_6460050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460058 : List Nat := [3, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3]
def baseStart_6460058 : Nat := 118140960795 + 6460058 * 2 ^ 59
def prefixEnd_6460058 : Nat := 4983230072969 + 3 ^ 40 * 6460058 * 2
def baseEnd_6460058 : Nat := 3317114809922791227065741

theorem tailTrace_6460058 : CollatzResearch.WordTrace tailWord_6460058 prefixEnd_6460058 3317114809922791227065741 := by
  unfold tailWord_6460058
  simp only [CollatzResearch.WordTrace]
  refine ⟨58904418007580157728525207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157078448020213753942733885 58904418007580157728525207)
  ·
    refine ⟨88356627011370236592787811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58904418007580157728525207 88356627011370236592787811)
    ·
      refine ⟨132534940517055354889181717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88356627011370236592787811 132534940517055354889181717)
      ·
        refine ⟨6212575336736969760430393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 132534940517055354889181717 6212575336736969760430393)
        ·
          refine ⟨4659431502552727320322795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6212575336736969760430393 4659431502552727320322795)
          ·
            refine ⟨6989147253829090980484193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659431502552727320322795 6989147253829090980484193)
            ·
              refine ⟨5241860440371818235363145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6989147253829090980484193 5241860440371818235363145)
              ·
                refine ⟨3931395330278863676522359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5241860440371818235363145 3931395330278863676522359)
                ·
                  refine ⟨5897092995418295514783539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3931395330278863676522359 5897092995418295514783539)
                  ·
                    refine ⟨8845639493127443272175309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5897092995418295514783539 8845639493127443272175309)
                    ·
                      refine ⟨3317114809922791227065741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8845639493127443272175309 3317114809922791227065741)
                      ·
                        rfl

theorem cell23_6460058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_6460058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460058 prefixEnd_6460058 := by exact prefixLift 6460058
  have htrace : WordTrace (prefixWord ++ tailWord_6460058) baseStart_6460058 baseEnd_6460058 := by
    simpa [prefixWord, tailWord_6460058, baseEnd_6460058] using wordTrace_append hprefix tailTrace_6460058
  have hstable : (prefixWord ++ tailWord_6460058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460058).length < 2 ^ (prefixWord ++ tailWord_6460058).sum := by decide
  have hdescent : baseEnd_6460058 < baseStart_6460058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460064 : List Nat := [2, 1, 1, 4, 4, 1, 1, 4, 1, 2, 2]
def baseStart_6460064 : Nat := 118140960795 + 6460064 * 2 ^ 59
def prefixEnd_6460064 : Nat := 4983230072969 + 3 ^ 40 * 6460064 * 2
def baseEnd_6460064 : Nat := 3317117890806718203590713

theorem tailTrace_6460064 : CollatzResearch.WordTrace tailWord_6460064 prefixEnd_6460064 3317117890806718203590713 := by
  unfold tailWord_6460064
  simp only [CollatzResearch.WordTrace]
  refine ⟨117808945434149446969409623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157078593912199262625879497 117808945434149446969409623)
  ·
    refine ⟨176713418151224170454114435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117808945434149446969409623 176713418151224170454114435)
    ·
      refine ⟨265070127226836255681171653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176713418151224170454114435 265070127226836255681171653)
      ·
        refine ⟨49700648855031797940219685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265070127226836255681171653 49700648855031797940219685)
        ·
          refine ⟨9318871660318462113791191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49700648855031797940219685 9318871660318462113791191)
          ·
            refine ⟨13978307490477693170686787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9318871660318462113791191 13978307490477693170686787)
            ·
              refine ⟨20967461235716539756030181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13978307490477693170686787 20967461235716539756030181)
              ·
                refine ⟨3931398981696851204255659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20967461235716539756030181 3931398981696851204255659)
                ·
                  refine ⟨5897098472545276806383489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3931398981696851204255659 5897098472545276806383489)
                  ·
                    refine ⟨4422823854408957604787617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5897098472545276806383489 4422823854408957604787617)
                    ·
                      refine ⟨3317117890806718203590713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422823854408957604787617 3317117890806718203590713)
                      ·
                        rfl

theorem cell23_6460064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_6460064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460064 prefixEnd_6460064 := by exact prefixLift 6460064
  have htrace : WordTrace (prefixWord ++ tailWord_6460064) baseStart_6460064 baseEnd_6460064 := by
    simpa [prefixWord, tailWord_6460064, baseEnd_6460064] using wordTrace_append hprefix tailTrace_6460064
  have hstable : (prefixWord ++ tailWord_6460064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460064).length < 2 ^ (prefixWord ++ tailWord_6460064).sum := by decide
  have hdescent : baseEnd_6460064 < baseStart_6460064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460073 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 3, 3, 2]
def baseStart_6460073 : Nat := 118140960795 + 6460073 * 2 ^ 59
def prefixEnd_6460073 : Nat := 4983230072969 + 3 ^ 40 * 6460073 * 2
def baseEnd_6460073 : Nat := 3317122512132608668378171

theorem tailTrace_6460073 : CollatzResearch.WordTrace tailWord_6460073 prefixEnd_6460073 3317122512132608668378171 := by
  unfold tailWord_6460073
  simp only [CollatzResearch.WordTrace]
  refine ⟨235618219125266288475896873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157078812750177525650597915 235618219125266288475896873)
  ·
    refine ⟨176713664343949716356922655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235618219125266288475896873 176713664343949716356922655)
    ·
      refine ⟨265070496515924574535383983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176713664343949716356922655 265070496515924574535383983)
      ·
        refine ⟨397605744773886861803075975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265070496515924574535383983 397605744773886861803075975)
        ·
          refine ⟨596408617160830292704613963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397605744773886861803075975 596408617160830292704613963)
          ·
            refine ⟨894612925741245439056920945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596408617160830292704613963 894612925741245439056920945)
            ·
              refine ⟨670959694305934079292690709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894612925741245439056920945 670959694305934079292690709)
              ·
                refine ⟨31451235670590659966844877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 670959694305934079292690709 31451235670590659966844877)
                ·
                  refine ⟨11794213376471497487566829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31451235670590659966844877 11794213376471497487566829)
                  ·
                    refine ⟨4422830016176811557837561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11794213376471497487566829 4422830016176811557837561)
                    ·
                      refine ⟨3317122512132608668378171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422830016176811557837561 3317122512132608668378171)
                      ·
                        rfl

theorem cell23_6460073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 3, 2].length) (baseStart_6460073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460073 prefixEnd_6460073 := by exact prefixLift 6460073
  have htrace : WordTrace (prefixWord ++ tailWord_6460073) baseStart_6460073 baseEnd_6460073 := by
    simpa [prefixWord, tailWord_6460073, baseEnd_6460073] using wordTrace_append hprefix tailTrace_6460073
  have hstable : (prefixWord ++ tailWord_6460073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460073).length < 2 ^ (prefixWord ++ tailWord_6460073).sum := by decide
  have hdescent : baseEnd_6460073 < baseStart_6460073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460090 : List Nat := [3, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2]
def baseStart_6460090 : Nat := 118140960795 + 6460090 * 2 ^ 59
def prefixEnd_6460090 : Nat := 4983230072969 + 3 ^ 40 * 6460090 * 2
def baseEnd_6460090 : Nat := 3317131241303735101865593

theorem tailTrace_6460090 : CollatzResearch.WordTrace tailWord_6460090 prefixEnd_6460090 3317131241303735101865593 := by
  unfold tailWord_6460090
  simp only [CollatzResearch.WordTrace]
  refine ⟨58904709791551175094816431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157079226110803133586177149 58904709791551175094816431)
  ·
    refine ⟨88357064687326762642224647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58904709791551175094816431 88357064687326762642224647)
    ·
      refine ⟨132535597030990143963336971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88357064687326762642224647 132535597030990143963336971)
      ·
        refine ⟨198803395546485215945005457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132535597030990143963336971 198803395546485215945005457)
        ·
          refine ⟨149102546659863911958754093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198803395546485215945005457 149102546659863911958754093)
          ·
            refine ⟨55913454997448966984532785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149102546659863911958754093 55913454997448966984532785)
            ·
              refine ⟨41935091248086725238399589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55913454997448966984532785 41935091248086725238399589)
              ·
                refine ⟨7862829609016260982199923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41935091248086725238399589 7862829609016260982199923)
                ·
                  refine ⟨11794244413524391473299885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7862829609016260982199923 11794244413524391473299885)
                  ·
                    refine ⟨4422841655071646802487457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11794244413524391473299885 4422841655071646802487457)
                    ·
                      refine ⟨3317131241303735101865593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422841655071646802487457 3317131241303735101865593)
                      ·
                        rfl

theorem cell23_6460090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2].length) (baseStart_6460090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460090 prefixEnd_6460090 := by exact prefixLift 6460090
  have htrace : WordTrace (prefixWord ++ tailWord_6460090) baseStart_6460090 baseEnd_6460090 := by
    simpa [prefixWord, tailWord_6460090, baseEnd_6460090] using wordTrace_append hprefix tailTrace_6460090
  have hstable : (prefixWord ++ tailWord_6460090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460090).length < 2 ^ (prefixWord ++ tailWord_6460090).sum := by decide
  have hdescent : baseEnd_6460090 < baseStart_6460090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460103 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 3, 4, 2]
def baseStart_6460103 : Nat := 118140960795 + 6460103 * 2 ^ 59
def prefixEnd_6460103 : Nat := 4983230072969 + 3 ^ 40 * 6460103 * 2
def baseEnd_6460103 : Nat := 3317137916552243551003033

theorem tailTrace_6460103 : CollatzResearch.WordTrace tailWord_6460103 prefixEnd_6460103 3317137916552243551003033 := by
  unfold tailWord_6460103
  simp only [CollatzResearch.WordTrace]
  refine ⟨235619313315157603599488963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157079542210105069066325975 235619313315157603599488963)
  ·
    refine ⟨353428969972736405399233445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235619313315157603599488963 353428969972736405399233445)
    ·
      refine ⟨66267931869888076012356271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353428969972736405399233445 66267931869888076012356271)
      ·
        refine ⟨99401897804832114018534407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66267931869888076012356271 99401897804832114018534407)
        ·
          refine ⟨149102846707248171027801611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99401897804832114018534407 149102846707248171027801611)
          ·
            refine ⟨223654270060872256541702417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149102846707248171027801611 223654270060872256541702417)
            ·
              refine ⟨167740702545654192406276813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223654270060872256541702417 167740702545654192406276813)
              ·
                refine ⟨62902763454620322152353805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167740702545654192406276813 62902763454620322152353805)
                ·
                  refine ⟨23588536295482620807132677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62902763454620322152353805 23588536295482620807132677)
                  ·
                    refine ⟨4422850555402991401337377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23588536295482620807132677 4422850555402991401337377)
                    ·
                      refine ⟨3317137916552243551003033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422850555402991401337377 3317137916552243551003033)
                      ·
                        rfl

theorem cell23_6460103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_6460103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460103 prefixEnd_6460103 := by exact prefixLift 6460103
  have htrace : WordTrace (prefixWord ++ tailWord_6460103) baseStart_6460103 baseEnd_6460103 := by
    simpa [prefixWord, tailWord_6460103, baseEnd_6460103] using wordTrace_append hprefix tailTrace_6460103
  have hstable : (prefixWord ++ tailWord_6460103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460103).length < 2 ^ (prefixWord ++ tailWord_6460103).sum := by decide
  have hdescent : baseEnd_6460103 < baseStart_6460103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460114 : List Nat := [3, 2, 2, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_6460114 : Nat := 118140960795 + 6460114 * 2 ^ 59
def prefixEnd_6460114 : Nat := 4983230072969 + 3 ^ 40 * 6460114 * 2
def baseEnd_6460114 : Nat := 3317143564839443007965483

theorem tailTrace_6460114 : CollatzResearch.WordTrace tailWord_6460114 prefixEnd_6460114 3317143564839443007965483 := by
  unfold tailWord_6460114
  simp only [CollatzResearch.WordTrace]
  refine ⟨58904928629529438119534849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157079809678745168318759597 58904928629529438119534849)
  ·
    refine ⟨44178696472147078589651137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58904928629529438119534849 44178696472147078589651137)
    ·
      refine ⟨33134022354110308942238353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44178696472147078589651137 33134022354110308942238353)
      ·
        refine ⟨24850516765582731706678765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33134022354110308942238353 24850516765582731706678765)
        ·
          refine ⟨9318943787093524390004537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24850516765582731706678765 9318943787093524390004537)
          ·
            refine ⟨6989207840320143292503403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9318943787093524390004537 6989207840320143292503403)
            ·
              refine ⟨10483811760480214938755105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6989207840320143292503403 10483811760480214938755105)
              ·
                refine ⟨7862858820360161204066329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10483811760480214938755105 7862858820360161204066329)
                ·
                  refine ⟨5897144115270120903049747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7862858820360161204066329 5897144115270120903049747)
                  ·
                    refine ⟨8845716172905181354574621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5897144115270120903049747 8845716172905181354574621)
                    ·
                      refine ⟨3317143564839443007965483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8845716172905181354574621 3317143564839443007965483)
                      ·
                        rfl

theorem cell23_6460114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_6460114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460114 prefixEnd_6460114 := by exact prefixLift 6460114
  have htrace : WordTrace (prefixWord ++ tailWord_6460114) baseStart_6460114 baseEnd_6460114 := by
    simpa [prefixWord, tailWord_6460114, baseEnd_6460114] using wordTrace_append hprefix tailTrace_6460114
  have hstable : (prefixWord ++ tailWord_6460114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460114).length < 2 ^ (prefixWord ++ tailWord_6460114).sum := by decide
  have hdescent : baseEnd_6460114 < baseStart_6460114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460133 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_6460133 : Nat := 118140960795 + 6460133 * 2 ^ 59
def prefixEnd_6460133 : Nat := 4983230072969 + 3 ^ 40 * 6460133 * 2
def baseEnd_6460133 : Nat := 3317153320971878433627895

theorem tailTrace_6460133 : CollatzResearch.WordTrace tailWord_6460133 prefixEnd_6460133 3317153320971878433627895 := by
  unfold tailWord_6460133
  simp only [CollatzResearch.WordTrace]
  refine ⟨235620407505048918723081053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157080271670032612482054035 235620407505048918723081053)
  ·
    refine ⟨88357652814393344521155395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235620407505048918723081053 88357652814393344521155395)
    ·
      refine ⟨132536479221590016781733093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88357652814393344521155395 132536479221590016781733093)
      ·
        refine ⟨24850589854048128146574955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132536479221590016781733093 24850589854048128146574955)
        ·
          refine ⟨37275884781072192219862433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24850589854048128146574955 37275884781072192219862433)
          ·
            refine ⟨27956913585804144164896825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37275884781072192219862433 27956913585804144164896825)
            ·
              refine ⟨20967685189353108123672619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27956913585804144164896825 20967685189353108123672619)
              ·
                refine ⟨31451527784029662185508929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20967685189353108123672619 31451527784029662185508929)
                ·
                  refine ⟨23588645838022246639131697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31451527784029662185508929 23588645838022246639131697)
                  ·
                    refine ⟨17691484378516684979348773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23588645838022246639131697 17691484378516684979348773)
                    ·
                      refine ⟨3317153320971878433627895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17691484378516684979348773 3317153320971878433627895)
                      ·
                        rfl

theorem cell23_6460133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_6460133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460133 prefixEnd_6460133 := by exact prefixLift 6460133
  have htrace : WordTrace (prefixWord ++ tailWord_6460133) baseStart_6460133 baseEnd_6460133 := by
    simpa [prefixWord, tailWord_6460133, baseEnd_6460133] using wordTrace_append hprefix tailTrace_6460133
  have hstable : (prefixWord ++ tailWord_6460133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460133).length < 2 ^ (prefixWord ++ tailWord_6460133).sum := by decide
  have hdescent : baseEnd_6460133 < baseStart_6460133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460163 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 1, 7, 2]
def baseStart_6460163 : Nat := 118140960795 + 6460163 * 2 ^ 59
def prefixEnd_6460163 : Nat := 4983230072969 + 3 ^ 40 * 6460163 * 2
def baseEnd_6460163 : Nat := 3317168725391513316252757

theorem tailTrace_6460163 : CollatzResearch.WordTrace tailWord_6460163 prefixEnd_6460163 3317168725391513316252757 := by
  unfold tailWord_6460163
  simp only [CollatzResearch.WordTrace]
  refine ⟨235621501694940233846673143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157081001129960155897782095 235621501694940233846673143)
  ·
    refine ⟨353432252542410350770009715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235621501694940233846673143 353432252542410350770009715)
    ·
      refine ⟨530148378813615526155014573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353432252542410350770009715 530148378813615526155014573)
      ·
        refine ⟨198805642055105822308130465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 530148378813615526155014573 198805642055105822308130465)
        ·
          refine ⟨149104231541329366731097849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198805642055105822308130465 149104231541329366731097849)
          ·
            refine ⟨111828173655997025048323387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149104231541329366731097849 111828173655997025048323387)
            ·
              refine ⟨167742260483995537572485081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111828173655997025048323387 167742260483995537572485081)
              ·
                refine ⟨125806695362996653179363811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167742260483995537572485081 125806695362996653179363811)
                ·
                  refine ⟨188710043044494979769045717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125806695362996653179363811 188710043044494979769045717)
                  ·
                    refine ⟨4422891633855351088337009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 188710043044494979769045717 4422891633855351088337009)
                    ·
                      refine ⟨3317168725391513316252757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422891633855351088337009 3317168725391513316252757)
                      ·
                        rfl

theorem cell23_6460163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 7, 2].length) (baseStart_6460163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460163 prefixEnd_6460163 := by exact prefixLift 6460163
  have htrace : WordTrace (prefixWord ++ tailWord_6460163) baseStart_6460163 baseEnd_6460163 := by
    simpa [prefixWord, tailWord_6460163, baseEnd_6460163] using wordTrace_append hprefix tailTrace_6460163
  have hstable : (prefixWord ++ tailWord_6460163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460163).length < 2 ^ (prefixWord ++ tailWord_6460163).sum := by decide
  have hdescent : baseEnd_6460163 < baseStart_6460163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460176 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 4]
def baseStart_6460176 : Nat := 118140960795 + 6460176 * 2 ^ 59
def prefixEnd_6460176 : Nat := 4983230072969 + 3 ^ 40 * 6460176 * 2
def baseEnd_6460176 : Nat := 3317175400640021765390197

theorem tailTrace_6460176 : CollatzResearch.WordTrace tailWord_6460176 prefixEnd_6460176 3317175400640021765390197 := by
  unfold tailWord_6460176
  simp only [CollatzResearch.WordTrace]
  refine ⟨117810987921946568533448191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157081317229262091377930921 117810987921946568533448191)
  ·
    refine ⟨176716481882919852800172287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117810987921946568533448191 176716481882919852800172287)
    ·
      refine ⟨265074722824379779200258431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176716481882919852800172287 265074722824379779200258431)
      ·
        refine ⟨397612084236569668800387647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265074722824379779200258431 397612084236569668800387647)
        ·
          refine ⟨596418126354854503200581471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397612084236569668800387647 596418126354854503200581471)
          ·
            refine ⟨894627189532281754800872207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596418126354854503200581471 894627189532281754800872207)
            ·
              refine ⟨1341940784298422632201308311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894627189532281754800872207 1341940784298422632201308311)
              ·
                refine ⟨2012911176447633948301962467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341940784298422632201308311 2012911176447633948301962467)
                ·
                  refine ⟨3019366764671450922452943701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012911176447633948301962467 3019366764671450922452943701)
                  ·
                    refine ⟨17691602136746782748747717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 3019366764671450922452943701 17691602136746782748747717)
                    ·
                      refine ⟨3317175400640021765390197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17691602136746782748747717 3317175400640021765390197)
                      ·
                        rfl

theorem cell23_6460176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_6460176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460176 prefixEnd_6460176 := by exact prefixLift 6460176
  have htrace : WordTrace (prefixWord ++ tailWord_6460176) baseStart_6460176 baseEnd_6460176 := by
    simpa [prefixWord, tailWord_6460176, baseEnd_6460176] using wordTrace_append hprefix tailTrace_6460176
  have hstable : (prefixWord ++ tailWord_6460176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460176).length < 2 ^ (prefixWord ++ tailWord_6460176).sum := by decide
  have hdescent : baseEnd_6460176 < baseStart_6460176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460193 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_6460193 : Nat := 118140960795 + 6460193 * 2 ^ 59
def prefixEnd_6460193 : Nat := 4983230072969 + 3 ^ 40 * 6460193 * 2
def baseEnd_6460193 : Nat := 3317184129811148198877619

theorem tailTrace_6460193 : CollatzResearch.WordTrace tailWord_6460193 prefixEnd_6460193 3317184129811148198877619 := by
  unfold tailWord_6460193
  simp only [CollatzResearch.WordTrace]
  refine ⟨235622595884831548970265233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157081730589887699313510155 235622595884831548970265233)
  ·
    refine ⟨176716946913623661727698925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235622595884831548970265233 176716946913623661727698925)
    ·
      refine ⟨66268855092608873147887097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176716946913623661727698925 66268855092608873147887097)
      ·
        refine ⟨49701641319456654860915323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66268855092608873147887097 49701641319456654860915323)
        ·
          refine ⟨74552461979184982291372985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49701641319456654860915323 74552461979184982291372985)
          ·
            refine ⟨55914346484388736718529739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74552461979184982291372985 55914346484388736718529739)
            ·
              refine ⟨83871519726583105077794609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55914346484388736718529739 83871519726583105077794609)
              ·
                refine ⟨62903639794937328808345957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83871519726583105077794609 62903639794937328808345957)
                ·
                  refine ⟨11794432461550749151564867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62903639794937328808345957 11794432461550749151564867)
                  ·
                    refine ⟨17691648692326123727347301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11794432461550749151564867 17691648692326123727347301)
                    ·
                      refine ⟨3317184129811148198877619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17691648692326123727347301 3317184129811148198877619)
                      ·
                        rfl

theorem cell23_6460193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_6460193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460193 prefixEnd_6460193 := by exact prefixLift 6460193
  have htrace : WordTrace (prefixWord ++ tailWord_6460193) baseStart_6460193 baseEnd_6460193 := by
    simpa [prefixWord, tailWord_6460193, baseEnd_6460193] using wordTrace_append hprefix tailTrace_6460193
  have hstable : (prefixWord ++ tailWord_6460193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460193).length < 2 ^ (prefixWord ++ tailWord_6460193).sum := by decide
  have hdescent : baseEnd_6460193 < baseStart_6460193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460210 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_6460210 : Nat := 118140960795 + 6460210 * 2 ^ 59
def prefixEnd_6460210 : Nat := 4983230072969 + 3 ^ 40 * 6460210 * 2
def baseEnd_6460210 : Nat := 3317192858982274632365041

theorem tailTrace_6460210 : CollatzResearch.WordTrace tailWord_6460210 prefixEnd_6460210 3317192858982274632365041 := by
  unfold tailWord_6460210
  simp only [CollatzResearch.WordTrace]
  refine ⟨58905803981442490218408521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157082143950513307249089389 58905803981442490218408521)
  ·
    refine ⟨44179352986081867663806391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58905803981442490218408521 44179352986081867663806391)
    ·
      refine ⟨66269029479122801495709587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44179352986081867663806391 66269029479122801495709587)
      ·
        refine ⟨99403544218684202243564381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66269029479122801495709587 99403544218684202243564381)
        ·
          refine ⟨37276329082006575841336643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99403544218684202243564381 37276329082006575841336643)
          ·
            refine ⟨55914493623009863762004965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37276329082006575841336643 55914493623009863762004965)
            ·
              refine ⟨10483967554314349455375931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55914493623009863762004965 10483967554314349455375931)
              ·
                refine ⟨15725951331471524183063897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10483967554314349455375931 15725951331471524183063897)
                ·
                  refine ⟨11794463498603643137297923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15725951331471524183063897 11794463498603643137297923)
                  ·
                    refine ⟨17691695247905464705946885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11794463498603643137297923 17691695247905464705946885)
                    ·
                      refine ⟨3317192858982274632365041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17691695247905464705946885 3317192858982274632365041)
                      ·
                        rfl

theorem cell23_6460210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_6460210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460210 prefixEnd_6460210 := by exact prefixLift 6460210
  have htrace : WordTrace (prefixWord ++ tailWord_6460210) baseStart_6460210 baseEnd_6460210 := by
    simpa [prefixWord, tailWord_6460210, baseEnd_6460210] using wordTrace_append hprefix tailTrace_6460210
  have hstable : (prefixWord ++ tailWord_6460210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460210).length < 2 ^ (prefixWord ++ tailWord_6460210).sum := by decide
  have hdescent : baseEnd_6460210 < baseStart_6460210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460228 : List Nat := [2, 3, 4, 2, 2, 1, 2, 2, 5]
def baseStart_6460228 : Nat := 118140960795 + 6460228 * 2 ^ 59
def prefixEnd_6460228 : Nat := 4983230072969 + 3 ^ 40 * 6460228 * 2
def baseEnd_6460228 : Nat := 368578011292672840215551

theorem tailTrace_6460228 : CollatzResearch.WordTrace tailWord_6460228 prefixEnd_6460228 368578011292672840215551 := by
  unfold tailWord_6460228
  simp only [CollatzResearch.WordTrace]
  refine ⟨117811936219852374973894669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157082581626469833298526225 117811936219852374973894669)
  ·
    refine ⟨44179476082444640615210501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117811936219852374973894669 44179476082444640615210501)
    ·
      refine ⟨8283651765458370115351969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44179476082444640615210501 8283651765458370115351969)
      ·
        refine ⟨6212738824093777586513977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8283651765458370115351969 6212738824093777586513977)
        ·
          refine ⟨4659554118070333189885483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6212738824093777586513977 4659554118070333189885483)
          ·
            refine ⟨6989331177105499784828225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659554118070333189885483 6989331177105499784828225)
            ·
              refine ⟨5241998382829124838621169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6989331177105499784828225 5241998382829124838621169)
              ·
                refine ⟨3931498787121843628965877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5241998382829124838621169 3931498787121843628965877)
                ·
                  refine ⟨368578011292672840215551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3931498787121843628965877 368578011292672840215551)
                  ·
                    rfl

theorem cell23_6460228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_6460228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460228 prefixEnd_6460228 := by exact prefixLift 6460228
  have htrace : WordTrace (prefixWord ++ tailWord_6460228) baseStart_6460228 baseEnd_6460228 := by
    simpa [prefixWord, tailWord_6460228, baseEnd_6460228] using wordTrace_append hprefix tailTrace_6460228
  have hstable : (prefixWord ++ tailWord_6460228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460228).length < 2 ^ (prefixWord ++ tailWord_6460228).sum := by decide
  have hdescent : baseEnd_6460228 < baseStart_6460228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460233 : List Nat := [1, 2, 1, 1, 2, 5, 1, 4, 6]
def baseStart_6460233 : Nat := 118140960795 + 6460233 * 2 ^ 59
def prefixEnd_6460233 : Nat := 4983230072969 + 3 ^ 40 * 6460233 * 2
def baseEnd_6460233 : Nat := 368578296559703115819715

theorem tailTrace_6460233 : CollatzResearch.WordTrace tailWord_6460233 prefixEnd_6460233 368578296559703115819715 := by
  unfold tailWord_6460233
  simp only [CollatzResearch.WordTrace]
  refine ⟨235624054804686635801721353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157082703203124423867814235 235624054804686635801721353)
  ·
    refine ⟨176718041103514976851291015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235624054804686635801721353 176718041103514976851291015)
    ·
      refine ⟨265077061655272465276936523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176718041103514976851291015 265077061655272465276936523)
      ·
        refine ⟨397615592482908697915404785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265077061655272465276936523 397615592482908697915404785)
        ·
          refine ⟨298211694362181523436553589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397615592482908697915404785 298211694362181523436553589)
          ·
            refine ⟨27957346346454517822176899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 298211694362181523436553589 27957346346454517822176899)
            ·
              refine ⟨41936019519681776733265349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27957346346454517822176899 41936019519681776733265349)
              ·
                refine ⟨7863003659940333137487253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41936019519681776733265349 7863003659940333137487253)
                ·
                  refine ⟨368578296559703115819715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7863003659940333137487253 368578296559703115819715)
                  ·
                    rfl

theorem cell23_6460233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 6].length) (baseStart_6460233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460233 prefixEnd_6460233 := by exact prefixLift 6460233
  have htrace : WordTrace (prefixWord ++ tailWord_6460233) baseStart_6460233 baseEnd_6460233 := by
    simpa [prefixWord, tailWord_6460233, baseEnd_6460233] using wordTrace_append hprefix tailTrace_6460233
  have hstable : (prefixWord ++ tailWord_6460233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460233).length < 2 ^ (prefixWord ++ tailWord_6460233).sum := by decide
  have hdescent : baseEnd_6460233 < baseStart_6460233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460317 : List Nat := [1, 4, 2, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_6460317 : Nat := 118140960795 + 6460317 * 2 ^ 59
def prefixEnd_6460317 : Nat := 4983230072969 + 3 ^ 40 * 6460317 * 2
def baseEnd_6460317 : Nat := 3317247801412305713727049

theorem tailTrace_6460317 : CollatzResearch.WordTrace tailWord_6460317 prefixEnd_6460317 3317247801412305713727049 := by
  unfold tailWord_6460317
  simp only [CollatzResearch.WordTrace]
  refine ⟨235627118536382318147779205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157084745690921545431852803 235627118536382318147779205)
  ·
    refine ⟨44180084725571684652708601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235627118536382318147779205 44180084725571684652708601)
    ·
      refine ⟨33135063544178763489531451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44180084725571684652708601 33135063544178763489531451)
      ·
        refine ⟨49702595316268145234297177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33135063544178763489531451 49702595316268145234297177)
        ·
          refine ⟨37276946487201108925722883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49702595316268145234297177 37276946487201108925722883)
          ·
            refine ⟨55915419730801663388584325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37276946487201108925722883 55915419730801663388584325)
            ·
              refine ⟨10484141199525311885359561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55915419730801663388584325 10484141199525311885359561)
              ·
                refine ⟨7863105899643983914019671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10484141199525311885359561 7863105899643983914019671)
                ·
                  refine ⟨11794658849465975871029507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7863105899643983914019671 11794658849465975871029507)
                  ·
                    refine ⟨17691988274198963806544261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11794658849465975871029507 17691988274198963806544261)
                    ·
                      refine ⟨3317247801412305713727049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17691988274198963806544261 3317247801412305713727049)
                      ·
                        rfl

theorem cell23_6460317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_6460317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460317 prefixEnd_6460317 := by exact prefixLift 6460317
  have htrace : WordTrace (prefixWord ++ tailWord_6460317) baseStart_6460317 baseEnd_6460317 := by
    simpa [prefixWord, tailWord_6460317, baseEnd_6460317] using wordTrace_append hprefix tailTrace_6460317
  have hstable : (prefixWord ++ tailWord_6460317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460317).length < 2 ^ (prefixWord ++ tailWord_6460317).sum := by decide
  have hdescent : baseEnd_6460317 < baseStart_6460317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460320 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 3]
def baseStart_6460320 : Nat := 118140960795 + 6460320 * 2 ^ 59
def prefixEnd_6460320 : Nat := 4983230072969 + 3 ^ 40 * 6460320 * 2
def baseEnd_6460320 : Nat := 3317249341854269201989535

theorem tailTrace_6460320 : CollatzResearch.WordTrace tailWord_6460320 prefixEnd_6460320 3317249341854269201989535 := by
  unfold tailWord_6460320
  simp only [CollatzResearch.WordTrace]
  refine ⟨117813613977685724830069207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157084818636914299773425609 117813613977685724830069207)
  ·
    refine ⟨176720420966528587245103811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117813613977685724830069207 176720420966528587245103811)
    ·
      refine ⟨265080631449792880867655717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176720420966528587245103811 265080631449792880867655717)
      ·
        refine ⟨49702618396836165162685447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265080631449792880867655717 49702618396836165162685447)
        ·
          refine ⟨74553927595254247744028171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49702618396836165162685447 74553927595254247744028171)
          ·
            refine ⟨111830891392881371616042257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74553927595254247744028171 111830891392881371616042257)
            ·
              refine ⟨83873168544661028712031693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111830891392881371616042257 83873168544661028712031693)
              ·
                refine ⟨31452438204247885767011885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83873168544661028712031693 31452438204247885767011885)
                ·
                  refine ⟨11794664326592957162629457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31452438204247885767011885 11794664326592957162629457)
                  ·
                    refine ⟨8845998244944717871972093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11794664326592957162629457 8845998244944717871972093)
                    ·
                      refine ⟨3317249341854269201989535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8845998244944717871972093 3317249341854269201989535)
                      ·
                        rfl

theorem cell23_6460320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_6460320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460320 prefixEnd_6460320 := by exact prefixLift 6460320
  have htrace : WordTrace (prefixWord ++ tailWord_6460320) baseStart_6460320 baseEnd_6460320 := by
    simpa [prefixWord, tailWord_6460320, baseEnd_6460320] using wordTrace_append hprefix tailTrace_6460320
  have hstable : (prefixWord ++ tailWord_6460320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460320).length < 2 ^ (prefixWord ++ tailWord_6460320).sum := by decide
  have hdescent : baseEnd_6460320 < baseStart_6460320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460337 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 1, 1, 5]
def baseStart_6460337 : Nat := 118140960795 + 6460337 * 2 ^ 59
def prefixEnd_6460337 : Nat := 4983230072969 + 3 ^ 40 * 6460337 * 2
def baseEnd_6460337 : Nat := 3317258071025395635476957

theorem tailTrace_6460337 : CollatzResearch.WordTrace tailWord_6460337 prefixEnd_6460337 3317258071025395635476957 := by
  unfold tailWord_6460337
  simp only [CollatzResearch.WordTrace]
  refine ⟨235627847996309861563507265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157085231997539907709004843 235627847996309861563507265)
  ·
    refine ⟨176720885997232396172630449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235627847996309861563507265 176720885997232396172630449)
    ·
      refine ⟨132540664497924297129472837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176720885997232396172630449 132540664497924297129472837)
      ·
        refine ⟨24851374593360805711776157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132540664497924297129472837 24851374593360805711776157)
        ·
          refine ⟨9319265472510302141916059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24851374593360805711776157 9319265472510302141916059)
          ·
            refine ⟨13978898208765453212874089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9319265472510302141916059 13978898208765453212874089)
            ·
              refine ⟨10484173656574089909655567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13978898208765453212874089 10484173656574089909655567)
              ·
                refine ⟨15726260484861134864483351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10484173656574089909655567 15726260484861134864483351)
                ·
                  refine ⟨23589390727291702296725027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15726260484861134864483351 23589390727291702296725027)
                  ·
                    refine ⟨35384086090937553445087541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23589390727291702296725027 35384086090937553445087541)
                    ·
                      refine ⟨3317258071025395635476957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35384086090937553445087541 3317258071025395635476957)
                      ·
                        rfl

theorem cell23_6460337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_6460337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460337 prefixEnd_6460337 := by exact prefixLift 6460337
  have htrace : WordTrace (prefixWord ++ tailWord_6460337) baseStart_6460337 baseEnd_6460337 := by
    simpa [prefixWord, tailWord_6460337, baseEnd_6460337] using wordTrace_append hprefix tailTrace_6460337
  have hstable : (prefixWord ++ tailWord_6460337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460337).length < 2 ^ (prefixWord ++ tailWord_6460337).sum := by decide
  have hdescent : baseEnd_6460337 < baseStart_6460337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460365 : List Nat := [1, 6, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_6460365 : Nat := 118140960795 + 6460365 * 2 ^ 59
def prefixEnd_6460365 : Nat := 4983230072969 + 3 ^ 40 * 6460365 * 2
def baseEnd_6460365 : Nat := 1105757482827907175308943

theorem tailTrace_6460365 : CollatzResearch.WordTrace tailWord_6460365 prefixEnd_6460365 1105757482827907175308943 := by
  unfold tailWord_6460365
  simp only [CollatzResearch.WordTrace]
  refine ⟨235628869240208422345526549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157085912826805614897017699 235628869240208422345526549)
  ·
    refine ⟨11045103245634769797446557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 235628869240208422345526549 11045103245634769797446557)
    ·
      refine ⟨4141913717113038674042459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11045103245634769797446557 4141913717113038674042459)
      ·
        refine ⟨6212870575669558011063689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4141913717113038674042459 6212870575669558011063689)
        ·
          refine ⟨4659652931752168508297767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6212870575669558011063689 4659652931752168508297767)
          ·
            refine ⟨6989479397628252762446651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659652931752168508297767 6989479397628252762446651)
            ·
              refine ⟨10484219096442379143669977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6989479397628252762446651 10484219096442379143669977)
              ·
                refine ⟨7863164322331784357752483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10484219096442379143669977 7863164322331784357752483)
                ·
                  refine ⟨11794746483497676536628725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7863164322331784357752483 11794746483497676536628725)
                  ·
                    refine ⟨1105757482827907175308943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11794746483497676536628725 1105757482827907175308943)
                    ·
                      rfl

theorem cell23_6460365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_6460365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460365 prefixEnd_6460365 := by exact prefixLift 6460365
  have htrace : WordTrace (prefixWord ++ tailWord_6460365) baseStart_6460365 baseEnd_6460365 := by
    simpa [prefixWord, tailWord_6460365, baseEnd_6460365] using wordTrace_append hprefix tailTrace_6460365
  have hstable : (prefixWord ++ tailWord_6460365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460365).length < 2 ^ (prefixWord ++ tailWord_6460365).sum := by decide
  have hdescent : baseEnd_6460365 < baseStart_6460365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460402 : List Nat := [3, 2, 1, 5, 1, 2, 2, 2, 1, 2, 2]
def baseStart_6460402 : Nat := 118140960795 + 6460402 * 2 ^ 59
def prefixEnd_6460402 : Nat := 4983230072969 + 3 ^ 40 * 6460402 * 2
def baseEnd_6460402 : Nat := 3317291447267937881164159

theorem tailTrace_6460402 : CollatzResearch.WordTrace tailWord_6460402 prefixEnd_6460402 3317291447267937881164159 := by
  unfold tailWord_6460402
  simp only [CollatzResearch.WordTrace]
  refine ⟨58907554685268594416155865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157086812494049585109748973 58907554685268594416155865)
  ·
    refine ⟨44180666013951445812116899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58907554685268594416155865 44180666013951445812116899)
    ·
      refine ⟨66270999020927168718175349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44180666013951445812116899 66270999020927168718175349)
      ·
        refine ⟨6212906158211922067328939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66270999020927168718175349 6212906158211922067328939)
        ·
          refine ⟨9319359237317883100993409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6212906158211922067328939 9319359237317883100993409)
          ·
            refine ⟨6989519427988412325745057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9319359237317883100993409 6989519427988412325745057)
            ·
              refine ⟨5242139570991309244308793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6989519427988412325745057 5242139570991309244308793)
              ·
                refine ⟨3931604678243481933231595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5242139570991309244308793 3931604678243481933231595)
                ·
                  refine ⟨5897407017365222899847393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3931604678243481933231595 5897407017365222899847393)
                  ·
                    refine ⟨4423055263023917174885545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5897407017365222899847393 4423055263023917174885545)
                    ·
                      refine ⟨3317291447267937881164159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4423055263023917174885545 3317291447267937881164159)
                      ·
                        rfl

theorem cell23_6460402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_6460402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460402 prefixEnd_6460402 := by exact prefixLift 6460402
  have htrace : WordTrace (prefixWord ++ tailWord_6460402) baseStart_6460402 baseEnd_6460402 := by
    simpa [prefixWord, tailWord_6460402, baseEnd_6460402] using wordTrace_append hprefix tailTrace_6460402
  have hstable : (prefixWord ++ tailWord_6460402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460402).length < 2 ^ (prefixWord ++ tailWord_6460402).sum := by decide
  have hdescent : baseEnd_6460402 < baseStart_6460402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460403 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 6]
def baseStart_6460403 : Nat := 118140960795 + 6460403 * 2 ^ 59
def prefixEnd_6460403 : Nat := 4983230072969 + 3 ^ 40 * 6460403 * 2
def baseEnd_6460403 : Nat := 3317291960748592377251653

theorem tailTrace_6460403 : CollatzResearch.WordTrace tailWord_6460403 prefixEnd_6460403 3317291960748592377251653 := by
  unfold tailWord_6460403
  simp only [CollatzResearch.WordTrace]
  refine ⟨235630255214070754835409863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157086836809380503223606575 235630255214070754835409863)
  ·
    refine ⟨353445382821106132253114795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235630255214070754835409863 353445382821106132253114795)
    ·
      refine ⟨530168074231659198379672193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353445382821106132253114795 530168074231659198379672193)
      ·
        refine ⟨397626055673744398784754145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530168074231659198379672193 397626055673744398784754145)
        ·
          refine ⟨298219541755308299088565609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397626055673744398784754145 298219541755308299088565609)
          ·
            refine ⟨223664656316481224316424207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298219541755308299088565609 223664656316481224316424207)
            ·
              refine ⟨335496984474721836474636311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223664656316481224316424207 335496984474721836474636311)
              ·
                refine ⟨503245476712082754711954467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335496984474721836474636311 503245476712082754711954467)
                ·
                  refine ⟨754868215068124132067931701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503245476712082754711954467 754868215068124132067931701)
                  ·
                    refine ⟨70768895162636637381368597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 754868215068124132067931701 70768895162636637381368597)
                    ·
                      refine ⟨3317291960748592377251653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70768895162636637381368597 3317291960748592377251653)
                      ·
                        rfl

theorem cell23_6460403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_6460403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460403 prefixEnd_6460403 := by exact prefixLift 6460403
  have htrace : WordTrace (prefixWord ++ tailWord_6460403) baseStart_6460403 baseEnd_6460403 := by
    simpa [prefixWord, tailWord_6460403, baseEnd_6460403] using wordTrace_append hprefix tailTrace_6460403
  have hstable : (prefixWord ++ tailWord_6460403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460403).length < 2 ^ (prefixWord ++ tailWord_6460403).sum := by decide
  have hdescent : baseEnd_6460403 < baseStart_6460403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460424 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 1, 4, 2]
def baseStart_6460424 : Nat := 118140960795 + 6460424 * 2 ^ 59
def prefixEnd_6460424 : Nat := 4983230072969 + 3 ^ 40 * 6460424 * 2
def baseEnd_6460424 : Nat := 3317302743842336795089057

theorem tailTrace_6460424 : CollatzResearch.WordTrace tailWord_6460424 prefixEnd_6460424 3317302743842336795089057 := by
  unfold tailWord_6460424
  simp only [CollatzResearch.WordTrace]
  refine ⟨117815510573497337710962163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157087347431329783614616217 117815510573497337710962163)
  ·
    refine ⟨176723265860246006566443245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117815510573497337710962163 176723265860246006566443245)
    ·
      refine ⟨66271224697592252462416217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176723265860246006566443245 66271224697592252462416217)
      ·
        refine ⟨49703418523194189346812163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66271224697592252462416217 49703418523194189346812163)
        ·
          refine ⟨74555127784791284020218245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49703418523194189346812163 74555127784791284020218245)
          ·
            refine ⟨13979086459648365753790921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74555127784791284020218245 13979086459648365753790921)
            ·
              refine ⟨10484314844736274315343191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13979086459648365753790921 10484314844736274315343191)
              ·
                refine ⟨15726472267104411473014787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10484314844736274315343191 15726472267104411473014787)
                ·
                  refine ⟨23589708400656617209522181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15726472267104411473014787 23589708400656617209522181)
                  ·
                    refine ⟨4423070325123115726785409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23589708400656617209522181 4423070325123115726785409)
                    ·
                      refine ⟨3317302743842336795089057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4423070325123115726785409 3317302743842336795089057)
                      ·
                        rfl

theorem cell23_6460424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_6460424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460424 prefixEnd_6460424 := by exact prefixLift 6460424
  have htrace : WordTrace (prefixWord ++ tailWord_6460424) baseStart_6460424 baseEnd_6460424 := by
    simpa [prefixWord, tailWord_6460424, baseEnd_6460424] using wordTrace_append hprefix tailTrace_6460424
  have hstable : (prefixWord ++ tailWord_6460424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460424).length < 2 ^ (prefixWord ++ tailWord_6460424).sum := by decide
  have hdescent : baseEnd_6460424 < baseStart_6460424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460430 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 9]
def baseStart_6460430 : Nat := 118140960795 + 6460430 * 2 ^ 59
def prefixEnd_6460430 : Nat := 4983230072969 + 3 ^ 40 * 6460430 * 2
def baseEnd_6460430 : Nat := 368589536080695974623781

theorem tailTrace_6460430 : CollatzResearch.WordTrace tailWord_6460430 prefixEnd_6460430 368589536080695974623781 := by
  unfold tailWord_6460430
  simp only [CollatzResearch.WordTrace]
  refine ⟨29453904998121617305830343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157087493323315292297761829 29453904998121617305830343)
  ·
    refine ⟨44180857497182425958745515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29453904998121617305830343 44180857497182425958745515)
    ·
      refine ⟨66271286245773638938118273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44180857497182425958745515 66271286245773638938118273)
      ·
        refine ⟨49703464684330229203588705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66271286245773638938118273 49703464684330229203588705)
        ·
          refine ⟨37277598513247671902691529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49703464684330229203588705 37277598513247671902691529)
          ·
            refine ⟨27958198884935753927018647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37277598513247671902691529 27958198884935753927018647)
            ·
              refine ⟨41937298327403630890527971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27958198884935753927018647 41937298327403630890527971)
              ·
                refine ⟨62905947491105446335791957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41937298327403630890527971 62905947491105446335791957)
                ·
                  refine ⟨368589536080695974623781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62905947491105446335791957 368589536080695974623781)
                  ·
                    rfl

theorem cell23_6460430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_6460430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460430 prefixEnd_6460430 := by exact prefixLift 6460430
  have htrace : WordTrace (prefixWord ++ tailWord_6460430) baseStart_6460430 baseEnd_6460430 := by
    simpa [prefixWord, tailWord_6460430, baseEnd_6460430] using wordTrace_append hprefix tailTrace_6460430
  have hstable : (prefixWord ++ tailWord_6460430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460430).length < 2 ^ (prefixWord ++ tailWord_6460430).sum := by decide
  have hdescent : baseEnd_6460430 < baseStart_6460430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460445 : List Nat := [1, 4, 2, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_6460445 : Nat := 118140960795 + 6460445 * 2 ^ 59
def prefixEnd_6460445 : Nat := 4983230072969 + 3 ^ 40 * 6460445 * 2
def baseEnd_6460445 : Nat := 3317313526936081212926461

theorem tailTrace_6460445 : CollatzResearch.WordTrace tailWord_6460445 prefixEnd_6460445 3317313526936081212926461 := by
  unfold tailWord_6460445
  simp only [CollatzResearch.WordTrace]
  refine ⟨235631787079918596008438789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157087858053279064005625859 235631787079918596008438789)
  ·
    refine ⟨44180960077484736751582273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235631787079918596008438789 44180960077484736751582273)
    ·
      refine ⟨33135720058113552563686705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44180960077484736751582273 33135720058113552563686705)
      ·
        refine ⟨24851790043585164422765029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33135720058113552563686705 24851790043585164422765029)
        ·
          refine ⟨4659710633172218329268443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24851790043585164422765029 4659710633172218329268443)
          ·
            refine ⟨6989565949758327493902665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659710633172218329268443 6989565949758327493902665)
            ·
              refine ⟨5242174462318745620426999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6989565949758327493902665 5242174462318745620426999)
              ·
                refine ⟨7863261693478118430640499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5242174462318745620426999 7863261693478118430640499)
                ·
                  refine ⟨11794892540217177645960749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7863261693478118430640499 11794892540217177645960749)
                  ·
                    refine ⟨4423084702581441617235281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11794892540217177645960749 4423084702581441617235281)
                    ·
                      refine ⟨3317313526936081212926461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4423084702581441617235281 3317313526936081212926461)
                      ·
                        rfl

theorem cell23_6460445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_6460445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460445 prefixEnd_6460445 := by exact prefixLift 6460445
  have htrace : WordTrace (prefixWord ++ tailWord_6460445) baseStart_6460445 baseEnd_6460445 := by
    simpa [prefixWord, tailWord_6460445, baseEnd_6460445] using wordTrace_append hprefix tailTrace_6460445
  have hstable : (prefixWord ++ tailWord_6460445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460445).length < 2 ^ (prefixWord ++ tailWord_6460445).sum := by decide
  have hdescent : baseEnd_6460445 < baseStart_6460445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460447 : List Nat := [1, 1, 2, 4, 1, 3, 1, 5, 5]
def baseStart_6460447 : Nat := 118140960795 + 6460447 * 2 ^ 59
def prefixEnd_6460447 : Nat := 4983230072969 + 3 ^ 40 * 6460447 * 2
def baseEnd_6460447 : Nat := 368590505988598911677939

theorem tailTrace_6460447 : CollatzResearch.WordTrace tailWord_6460447 prefixEnd_6460447 368590505988598911677939 := by
  unfold tailWord_6460447
  simp only [CollatzResearch.WordTrace]
  refine ⟨235631860025911350350011595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157087906683940900233341063 235631860025911350350011595)
  ·
    refine ⟨353447790038867025525017393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235631860025911350350011595 353447790038867025525017393)
    ·
      refine ⟨265085842529150269143763045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353447790038867025525017393 265085842529150269143763045)
      ·
        refine ⟨49703595474215675464455571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265085842529150269143763045 49703595474215675464455571)
        ·
          refine ⟨74555393211323513196683357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49703595474215675464455571 74555393211323513196683357)
          ·
            refine ⟨27958272454246317448756259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74555393211323513196683357 27958272454246317448756259)
            ·
              refine ⟨41937408681369476173134389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27958272454246317448756259 41937408681369476173134389)
              ·
                refine ⟨3931632063878388391231349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41937408681369476173134389 3931632063878388391231349)
                ·
                  refine ⟨368590505988598911677939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3931632063878388391231349 368590505988598911677939)
                  ·
                    rfl

theorem cell23_6460447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 5].length) (baseStart_6460447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460447 prefixEnd_6460447 := by exact prefixLift 6460447
  have htrace : WordTrace (prefixWord ++ tailWord_6460447) baseStart_6460447 baseEnd_6460447 := by
    simpa [prefixWord, tailWord_6460447, baseEnd_6460447] using wordTrace_append hprefix tailTrace_6460447
  have hstable : (prefixWord ++ tailWord_6460447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460447).length < 2 ^ (prefixWord ++ tailWord_6460447).sum := by decide
  have hdescent : baseEnd_6460447 < baseStart_6460447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460460 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 4, 5]
def baseStart_6460460 : Nat := 118140960795 + 6460460 * 2 ^ 59
def prefixEnd_6460460 : Nat := 4983230072969 + 3 ^ 40 * 6460460 * 2
def baseEnd_6460460 : Nat := 1105773743048632884746297

theorem tailTrace_6460460 : CollatzResearch.WordTrace tailWord_6460460 prefixEnd_6460460 1105773743048632884746297 := by
  unfold tailWord_6460460
  simp only [CollatzResearch.WordTrace]
  refine ⟨117816167087432126785117417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157088222783242835713489889 117816167087432126785117417)
  ·
    refine ⟨88362125315574095088838063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117816167087432126785117417 88362125315574095088838063)
    ·
      refine ⟨132543187973361142633257095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88362125315574095088838063 132543187973361142633257095)
      ·
        refine ⟨198814781960041713949885643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132543187973361142633257095 198814781960041713949885643)
        ·
          refine ⟨298222172940062570924828465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198814781960041713949885643 298222172940062570924828465)
          ·
            refine ⟨223666629705046928193621349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298222172940062570924828465 223666629705046928193621349)
            ·
              refine ⟨41937493069696299036304003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223666629705046928193621349 41937493069696299036304003)
              ·
                refine ⟨62906239604544448554456005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41937493069696299036304003 62906239604544448554456005)
                ·
                  refine ⟨11794919925852084103960501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62906239604544448554456005 11794919925852084103960501)
                  ·
                    refine ⟨1105773743048632884746297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11794919925852084103960501 1105773743048632884746297)
                    ·
                      rfl

theorem cell23_6460460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_6460460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460460 prefixEnd_6460460 := by exact prefixLift 6460460
  have htrace : WordTrace (prefixWord ++ tailWord_6460460) baseStart_6460460 baseEnd_6460460 := by
    simpa [prefixWord, tailWord_6460460, baseEnd_6460460] using wordTrace_append hprefix tailTrace_6460460
  have hstable : (prefixWord ++ tailWord_6460460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460460).length < 2 ^ (prefixWord ++ tailWord_6460460).sum := by decide
  have hdescent : baseEnd_6460460 < baseStart_6460460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460480 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 4]
def baseStart_6460480 : Nat := 118140960795 + 6460480 * 2 ^ 59
def prefixEnd_6460480 : Nat := 4983230072969 + 3 ^ 40 * 6460480 * 2
def baseEnd_6460480 : Nat := 3317331498758988575988799

theorem tailTrace_6460480 : CollatzResearch.WordTrace tailWord_6460480 prefixEnd_6460480 3317331498758988575988799 := by
  unfold tailWord_6460480
  simp only [CollatzResearch.WordTrace]
  refine ⟨117816531817395898492981447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157088709089861197990641929 117816531817395898492981447)
  ·
    refine ⟨176724797726093847739472171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117816531817395898492981447 176724797726093847739472171)
    ·
      refine ⟨265087196589140771609208257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176724797726093847739472171 265087196589140771609208257)
      ·
        refine ⟨198815397441855578706906193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265087196589140771609208257 198815397441855578706906193)
        ·
          refine ⟨149111548081391684030179645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198815397441855578706906193 149111548081391684030179645)
          ·
            refine ⟨55916830530521881511317367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149111548081391684030179645 55916830530521881511317367)
            ·
              refine ⟨83875245795782822266976051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55916830530521881511317367 83875245795782822266976051)
              ·
                refine ⟨125812868693674233400464077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83875245795782822266976051 125812868693674233400464077)
                ·
                  refine ⟨47179825760127837525174029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125812868693674233400464077 47179825760127837525174029)
                  ·
                    refine ⟨17692434660047939071940261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47179825760127837525174029 17692434660047939071940261)
                    ·
                      refine ⟨3317331498758988575988799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17692434660047939071940261 3317331498758988575988799)
                      ·
                        rfl

theorem cell23_6460480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_6460480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460480 prefixEnd_6460480 := by exact prefixLift 6460480
  have htrace : WordTrace (prefixWord ++ tailWord_6460480) baseStart_6460480 baseEnd_6460480 := by
    simpa [prefixWord, tailWord_6460480, baseEnd_6460480] using wordTrace_append hprefix tailTrace_6460480
  have hstable : (prefixWord ++ tailWord_6460480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460480).length < 2 ^ (prefixWord ++ tailWord_6460480).sum := by decide
  have hdescent : baseEnd_6460480 < baseStart_6460480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460497 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 1, 6, 2]
def baseStart_6460497 : Nat := 118140960795 + 6460497 * 2 ^ 59
def prefixEnd_6460497 : Nat := 4983230072969 + 3 ^ 40 * 6460497 * 2
def baseEnd_6460497 : Nat := 3317340227930115009476221

theorem tailTrace_6460497 : CollatzResearch.WordTrace tailWord_6460497 prefixEnd_6460497 3317340227930115009476221 := by
  unfold tailWord_6460497
  simp only [CollatzResearch.WordTrace]
  refine ⟨235633683675730208889331745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157089122450486805926221163 235633683675730208889331745)
  ·
    refine ⟨176725262756797656666998809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235633683675730208889331745 176725262756797656666998809)
    ·
      refine ⟨132543947067598242500249107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176725262756797656666998809 132543947067598242500249107)
      ·
        refine ⟨198815920601397363750373661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132543947067598242500249107 198815920601397363750373661)
        ·
          refine ⟨74555970225524011406390123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198815920601397363750373661 74555970225524011406390123)
          ·
            refine ⟨111833955338286017109585185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74555970225524011406390123 111833955338286017109585185)
            ·
              refine ⟨83875466503714512832188889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111833955338286017109585185 83875466503714512832188889)
              ·
                refine ⟨62906599877785884624141667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83875466503714512832188889 62906599877785884624141667)
                ·
                  refine ⟨94359899816678826936212501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62906599877785884624141667 94359899816678826936212501)
                  ·
                    refine ⟨4423120303906820012634961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94359899816678826936212501 4423120303906820012634961)
                    ·
                      refine ⟨3317340227930115009476221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4423120303906820012634961 3317340227930115009476221)
                      ·
                        rfl

theorem cell23_6460497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 6, 2].length) (baseStart_6460497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460497 prefixEnd_6460497 := by exact prefixLift 6460497
  have htrace : WordTrace (prefixWord ++ tailWord_6460497) baseStart_6460497 baseEnd_6460497 := by
    simpa [prefixWord, tailWord_6460497, baseEnd_6460497] using wordTrace_append hprefix tailTrace_6460497
  have hstable : (prefixWord ++ tailWord_6460497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460497).length < 2 ^ (prefixWord ++ tailWord_6460497).sum := by decide
  have hdescent : baseEnd_6460497 < baseStart_6460497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460514 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6460514 : Nat := 118140960795 + 6460514 * 2 ^ 59
def prefixEnd_6460514 : Nat := 4983230072969 + 3 ^ 40 * 6460514 * 2
def baseEnd_6460514 : Nat := 3317348957101241442963643

theorem tailTrace_6460514 : CollatzResearch.WordTrace tailWord_6460514 prefixEnd_6460514 3317348957101241442963643 := by
  unfold tailWord_6460514
  simp only [CollatzResearch.WordTrace]
  refine ⟨58908575929167155198175149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157089535811112413861800397 58908575929167155198175149)
  ·
    refine ⟨22090715973437683199315681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58908575929167155198175149 22090715973437683199315681)
    ·
      refine ⟨16568036980078262399486761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22090715973437683199315681 16568036980078262399486761)
      ·
        refine ⟨12426027735058696799615071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16568036980078262399486761 12426027735058696799615071)
        ·
          refine ⟨18639041602588045199422607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12426027735058696799615071 18639041602588045199422607)
          ·
            refine ⟨27958562403882067799133911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18639041602588045199422607 27958562403882067799133911)
            ·
              refine ⟨41937843605823101698700867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27958562403882067799133911 41937843605823101698700867)
              ·
                refine ⟨62906765408734652548051301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41937843605823101698700867 62906765408734652548051301)
                ·
                  refine ⟨11795018514137747352759619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62906765408734652548051301 11795018514137747352759619)
                  ·
                    refine ⟨17692527771206621029139429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11795018514137747352759619 17692527771206621029139429)
                    ·
                      refine ⟨3317348957101241442963643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17692527771206621029139429 3317348957101241442963643)
                      ·
                        rfl

theorem cell23_6460514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6460514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460514 prefixEnd_6460514 := by exact prefixLift 6460514
  have htrace : WordTrace (prefixWord ++ tailWord_6460514) baseStart_6460514 baseEnd_6460514 := by
    simpa [prefixWord, tailWord_6460514, baseEnd_6460514] using wordTrace_append hprefix tailTrace_6460514
  have hstable : (prefixWord ++ tailWord_6460514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460514).length < 2 ^ (prefixWord ++ tailWord_6460514).sum := by decide
  have hdescent : baseEnd_6460514 < baseStart_6460514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460534 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_6460534 : Nat := 118140960795 + 6460534 * 2 ^ 59
def prefixEnd_6460534 : Nat := 4983230072969 + 3 ^ 40 * 6460534 * 2
def baseEnd_6460534 : Nat := 3317359226714331364713551

theorem tailTrace_6460534 : CollatzResearch.WordTrace tailWord_6460534 prefixEnd_6460534 3317359226714331364713551 := by
  unfold tailWord_6460534
  simp only [CollatzResearch.WordTrace]
  refine ⟨14727189573537260263026791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157090022117730776138952437 14727189573537260263026791)
  ·
    refine ⟨22090784360305890394540187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14727189573537260263026791 22090784360305890394540187)
    ·
      refine ⟨33136176540458835591810281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22090784360305890394540187 33136176540458835591810281)
      ·
        refine ⟨24852132405344126693857711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33136176540458835591810281 24852132405344126693857711)
        ·
          refine ⟨37278198608016190040786567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24852132405344126693857711 37278198608016190040786567)
          ·
            refine ⟨55917297912024285061179851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37278198608016190040786567 55917297912024285061179851)
            ·
              refine ⟨83875946868036427591769777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55917297912024285061179851 83875946868036427591769777)
              ·
                refine ⟨62906960151027320693827333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83875946868036427591769777 62906960151027320693827333)
                ·
                  refine ⟨11795055028317622630092625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62906960151027320693827333 11795055028317622630092625)
                  ·
                    refine ⟨8846291271238216972569469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11795055028317622630092625 8846291271238216972569469)
                    ·
                      refine ⟨3317359226714331364713551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8846291271238216972569469 3317359226714331364713551)
                      ·
                        rfl

theorem cell23_6460534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_6460534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460534 prefixEnd_6460534 := by exact prefixLift 6460534
  have htrace : WordTrace (prefixWord ++ tailWord_6460534) baseStart_6460534 baseEnd_6460534 := by
    simpa [prefixWord, tailWord_6460534, baseEnd_6460534] using wordTrace_append hprefix tailTrace_6460534
  have hstable : (prefixWord ++ tailWord_6460534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460534).length < 2 ^ (prefixWord ++ tailWord_6460534).sum := by decide
  have hdescent : baseEnd_6460534 < baseStart_6460534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460560 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 5]
def baseStart_6460560 : Nat := 118140960795 + 6460560 * 2 ^ 59
def prefixEnd_6460560 : Nat := 4983230072969 + 3 ^ 40 * 6460560 * 2
def baseEnd_6460560 : Nat := 3317372577211348262988431

theorem tailTrace_6460560 : CollatzResearch.WordTrace tailWord_6460560 prefixEnd_6460560 3317372577211348262988431 := by
  unfold tailWord_6460560
  simp only [CollatzResearch.WordTrace]
  refine ⟨117817990737250985324437567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157090654316334647099250089 117817990737250985324437567)
  ·
    refine ⟨176726986105876477986656351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117817990737250985324437567 176726986105876477986656351)
    ·
      refine ⟨265090479158814716979984527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176726986105876477986656351 265090479158814716979984527)
      ·
        refine ⟨397635718738222075469976791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265090479158814716979984527 397635718738222075469976791)
        ·
          refine ⟨596453578107333113204965187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397635718738222075469976791 596453578107333113204965187)
          ·
            refine ⟨894680367160999669807447781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596453578107333113204965187 894680367160999669807447781)
            ·
              refine ⟨167752568842687438088896459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 894680367160999669807447781 167752568842687438088896459)
              ·
                refine ⟨251628853264031157133344689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167752568842687438088896459 251628853264031157133344689)
                ·
                  refine ⟨188721639948023367850008517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251628853264031157133344689 188721639948023367850008517)
                  ·
                    refine ⟨35385307490254381471876597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188721639948023367850008517 35385307490254381471876597)
                    ·
                      refine ⟨3317372577211348262988431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35385307490254381471876597 3317372577211348262988431)
                      ·
                        rfl

theorem cell23_6460560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_6460560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460560 prefixEnd_6460560 := by exact prefixLift 6460560
  have htrace : WordTrace (prefixWord ++ tailWord_6460560) baseStart_6460560 baseEnd_6460560 := by
    simpa [prefixWord, tailWord_6460560, baseEnd_6460560] using wordTrace_append hprefix tailTrace_6460560
  have hstable : (prefixWord ++ tailWord_6460560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460560).length < 2 ^ (prefixWord ++ tailWord_6460560).sum := by decide
  have hdescent : baseEnd_6460560 < baseStart_6460560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460575 : List Nat := [1, 1, 2, 6, 2, 2, 2, 2, 1, 4]
def baseStart_6460575 : Nat := 118140960795 + 6460575 * 2 ^ 59
def prefixEnd_6460575 : Nat := 4983230072969 + 3 ^ 40 * 6460575 * 2
def baseEnd_6460575 : Nat := 1105793426473721901433621

theorem tailTrace_6460575 : CollatzResearch.WordTrace tailWord_6460575 prefixEnd_6460575 1105793426473721901433621 := by
  unfold tailWord_6460575
  simp only [CollatzResearch.WordTrace]
  refine ⟨235636528569447628210671179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157091019046298418807114119 235636528569447628210671179)
  ·
    refine ⟨353454792854171442316006769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235636528569447628210671179 353454792854171442316006769)
    ·
      refine ⟨265091094640628581737005077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353454792854171442316006769 265091094640628581737005077)
      ·
        refine ⟨12426145061279464768922113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 265091094640628581737005077 12426145061279464768922113)
        ·
          refine ⟨9319608795959598576691585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12426145061279464768922113 9319608795959598576691585)
          ·
            refine ⟨6989706596969698932518689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9319608795959598576691585 6989706596969698932518689)
            ·
              refine ⟨5242279947727274199389017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6989706596969698932518689 5242279947727274199389017)
              ·
                refine ⟨3931709960795455649541763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5242279947727274199389017 3931709960795455649541763)
                ·
                  refine ⟨5897564941193183474312645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3931709960795455649541763 5897564941193183474312645)
                  ·
                    refine ⟨1105793426473721901433621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5897564941193183474312645 1105793426473721901433621)
                    ·
                      rfl

theorem cell23_6460575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 1, 4].length) (baseStart_6460575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460575 prefixEnd_6460575 := by exact prefixLift 6460575
  have htrace : WordTrace (prefixWord ++ tailWord_6460575) baseStart_6460575 baseEnd_6460575 := by
    simpa [prefixWord, tailWord_6460575, baseEnd_6460575] using wordTrace_append hprefix tailTrace_6460575
  have hstable : (prefixWord ++ tailWord_6460575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460575).length < 2 ^ (prefixWord ++ tailWord_6460575).sum := by decide
  have hdescent : baseEnd_6460575 < baseStart_6460575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460604 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_6460604 : Nat := 118140960795 + 6460604 * 2 ^ 59
def prefixEnd_6460604 : Nat := 4983230072969 + 3 ^ 40 * 6460604 * 2
def baseEnd_6460604 : Nat := 3317395170360146090838229

theorem tailTrace_6460604 : CollatzResearch.WordTrace tailWord_6460604 prefixEnd_6460604 3317395170360146090838229 := by
  unfold tailWord_6460604
  simp only [CollatzResearch.WordTrace]
  refine ⟨117818793143171283081738433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157091724190895044108984577 117818793143171283081738433)
  ·
    refine ⟨88364094857378462311303825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117818793143171283081738433 88364094857378462311303825)
    ·
      refine ⟨66273071143033846733477869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88364094857378462311303825 66273071143033846733477869)
      ·
        refine ⟨24852401678637692525054201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66273071143033846733477869 24852401678637692525054201)
        ·
          refine ⟨18639301258978269393790651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24852401678637692525054201 18639301258978269393790651)
          ·
            refine ⟨27958951888467404090685977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18639301258978269393790651 27958951888467404090685977)
            ·
              refine ⟨20969213916350553068014483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27958951888467404090685977 20969213916350553068014483)
              ·
                refine ⟨31453820874525829602021725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20969213916350553068014483 31453820874525829602021725)
                ·
                  refine ⟨11795182827947186100758147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31453820874525829602021725 11795182827947186100758147)
                  ·
                    refine ⟨17692774241920779151137221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11795182827947186100758147 17692774241920779151137221)
                    ·
                      refine ⟨3317395170360146090838229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17692774241920779151137221 3317395170360146090838229)
                      ·
                        rfl

theorem cell23_6460604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_6460604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460604 prefixEnd_6460604 := by exact prefixLift 6460604
  have htrace : WordTrace (prefixWord ++ tailWord_6460604) baseStart_6460604 baseEnd_6460604 := by
    simpa [prefixWord, tailWord_6460604, baseEnd_6460604] using wordTrace_append hprefix tailTrace_6460604
  have hstable : (prefixWord ++ tailWord_6460604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460604).length < 2 ^ (prefixWord ++ tailWord_6460604).sum := by decide
  have hdescent : baseEnd_6460604 < baseStart_6460604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460608 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 2, 3, 2]
def baseStart_6460608 : Nat := 118140960795 + 6460608 * 2 ^ 59
def prefixEnd_6460608 : Nat := 4983230072969 + 3 ^ 40 * 6460608 * 2
def baseEnd_6460608 : Nat := 3317397224282764075188211

theorem tailTrace_6460608 : CollatzResearch.WordTrace tailWord_6460608 prefixEnd_6460608 3317397224282764075188211 := by
  unfold tailWord_6460608
  simp only [CollatzResearch.WordTrace]
  refine ⟨117818866089164037423311239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157091821452218716564414985 117818866089164037423311239)
  ·
    refine ⟨176728299133746056134966859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117818866089164037423311239 176728299133746056134966859)
    ·
      refine ⟨265092448700619084202450289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176728299133746056134966859 265092448700619084202450289)
      ·
        refine ⟨198819336525464313151837717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265092448700619084202450289 198819336525464313151837717)
        ·
          refine ⟨9319656399631139678992393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 198819336525464313151837717 9319656399631139678992393)
          ·
            refine ⟨6989742299723354759244295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9319656399631139678992393 6989742299723354759244295)
            ·
              refine ⟨10484613449585032138866443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6989742299723354759244295 10484613449585032138866443)
              ·
                refine ⟨15726920174377548208299665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10484613449585032138866443 15726920174377548208299665)
                ·
                  refine ⟨11795190130783161156224749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15726920174377548208299665 11795190130783161156224749)
                  ·
                    refine ⟨4423196299043685433584281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11795190130783161156224749 4423196299043685433584281)
                    ·
                      refine ⟨3317397224282764075188211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4423196299043685433584281 3317397224282764075188211)
                      ·
                        rfl

theorem cell23_6460608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 2, 3, 2].length) (baseStart_6460608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460608 prefixEnd_6460608 := by exact prefixLift 6460608
  have htrace : WordTrace (prefixWord ++ tailWord_6460608) baseStart_6460608 baseEnd_6460608 := by
    simpa [prefixWord, tailWord_6460608, baseEnd_6460608] using wordTrace_append hprefix tailTrace_6460608
  have hstable : (prefixWord ++ tailWord_6460608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460608).length < 2 ^ (prefixWord ++ tailWord_6460608).sum := by decide
  have hdescent : baseEnd_6460608 < baseStart_6460608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460658 : List Nat := [3, 2, 1, 3, 3, 1, 2, 2, 1, 2, 3]
def baseStart_6460658 : Nat := 118140960795 + 6460658 * 2 ^ 59
def prefixEnd_6460658 : Nat := 4983230072969 + 3 ^ 40 * 6460658 * 2
def baseEnd_6460658 : Nat := 3317422898315488879562981

theorem tailTrace_6460658 : CollatzResearch.WordTrace tailWord_6460658 prefixEnd_6460658 3317422898315488879562981 := by
  unfold tailWord_6460658
  simp only [CollatzResearch.WordTrace]
  refine ⟨58909888957036733346485657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157093037218764622257295085 58909888957036733346485657)
  ·
    refine ⟨44182416717777550009864243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58909888957036733346485657 44182416717777550009864243)
    ·
      refine ⟨66273625076666325014796365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44182416717777550009864243 66273625076666325014796365)
      ·
        refine ⟨24852609403749871880548637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66273625076666325014796365 24852609403749871880548637)
        ·
          refine ⟨9319728526406201955205739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24852609403749871880548637 9319728526406201955205739)
          ·
            refine ⟨13979592789609302932808609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9319728526406201955205739 13979592789609302932808609)
            ·
              refine ⟨10484694592206977199606457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13979592789609302932808609 10484694592206977199606457)
              ·
                refine ⟨7863520944155232899704843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10484694592206977199606457 7863520944155232899704843)
                ·
                  refine ⟨11795281416232849349557265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7863520944155232899704843 11795281416232849349557265)
                  ·
                    refine ⟨8846461062174637012167949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11795281416232849349557265 8846461062174637012167949)
                    ·
                      refine ⟨3317422898315488879562981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8846461062174637012167949 3317422898315488879562981)
                      ·
                        rfl

theorem cell23_6460658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_6460658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460658 prefixEnd_6460658 := by exact prefixLift 6460658
  have htrace : WordTrace (prefixWord ++ tailWord_6460658) baseStart_6460658 baseEnd_6460658 := by
    simpa [prefixWord, tailWord_6460658, baseEnd_6460658] using wordTrace_append hprefix tailTrace_6460658
  have hstable : (prefixWord ++ tailWord_6460658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460658).length < 2 ^ (prefixWord ++ tailWord_6460658).sum := by decide
  have hdescent : baseEnd_6460658 < baseStart_6460658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460681 : List Nat := [1, 2, 1, 1, 3, 3, 1, 5, 1, 3, 2]
def baseStart_6460681 : Nat := 118140960795 + 6460681 * 2 ^ 59
def prefixEnd_6460681 : Nat := 4983230072969 + 3 ^ 40 * 6460681 * 2
def baseEnd_6460681 : Nat := 3317434708370542289575375

theorem tailTrace_6460681 : CollatzResearch.WordTrace tailWord_6460681 prefixEnd_6460681 3317434708370542289575375 := by
  unfold tailWord_6460681
  simp only [CollatzResearch.WordTrace]
  refine ⟨235640394707063608314029897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157093596471375738876019931 235640394707063608314029897)
  ·
    refine ⟨176730296030297706235522423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235640394707063608314029897 176730296030297706235522423)
    ·
      refine ⟨265095444045446559353283635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176730296030297706235522423 265095444045446559353283635)
      ·
        refine ⟨397643166068169839029925453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265095444045446559353283635 397643166068169839029925453)
        ·
          refine ⟨149116187275563689636222045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397643166068169839029925453 149116187275563689636222045)
          ·
            refine ⟨55918570228336383613583267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149116187275563689636222045 55918570228336383613583267)
            ·
              refine ⟨83877855342504575420374901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55918570228336383613583267 83877855342504575420374901)
              ·
                refine ⟨7863548938359803945660147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83877855342504575420374901 7863548938359803945660147)
                ·
                  refine ⟨11795323407539705918490221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7863548938359803945660147 11795323407539705918490221)
                  ·
                    refine ⟨4423246277827389719433833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11795323407539705918490221 4423246277827389719433833)
                    ·
                      refine ⟨3317434708370542289575375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4423246277827389719433833 3317434708370542289575375)
                      ·
                        rfl

theorem cell23_6460681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 3, 2].length) (baseStart_6460681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460681 prefixEnd_6460681 := by exact prefixLift 6460681
  have htrace : WordTrace (prefixWord ++ tailWord_6460681) baseStart_6460681 baseEnd_6460681 := by
    simpa [prefixWord, tailWord_6460681, baseEnd_6460681] using wordTrace_append hprefix tailTrace_6460681
  have hstable : (prefixWord ++ tailWord_6460681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460681).length < 2 ^ (prefixWord ++ tailWord_6460681).sum := by decide
  have hdescent : baseEnd_6460681 < baseStart_6460681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460744 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_6460744 : Nat := 118140960795 + 6460744 * 2 ^ 59
def prefixEnd_6460744 : Nat := 4983230072969 + 3 ^ 40 * 6460744 * 2
def baseEnd_6460744 : Nat := 3317467057651775543087585

theorem tailTrace_6460744 : CollatzResearch.WordTrace tailWord_6460744 prefixEnd_6460744 3317467057651775543087585 := by
  unfold tailWord_6460744
  simp only [CollatzResearch.WordTrace]
  refine ⟨117821346252917685036786643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157095128337223580049048857 117821346252917685036786643)
  ·
    refine ⟨176732019379376527555179965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117821346252917685036786643 176732019379376527555179965)
    ·
      refine ⟨66274507267266197833192487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176732019379376527555179965 66274507267266197833192487)
      ·
        refine ⟨99411760900899296749788731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66274507267266197833192487 99411760900899296749788731)
        ·
          refine ⟨149117641351348945124683097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99411760900899296749788731 149117641351348945124683097)
          ·
            refine ⟨111838231013511708843512323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149117641351348945124683097 111838231013511708843512323)
            ·
              refine ⟨167757346520267563265268485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111838231013511708843512323 167757346520267563265268485)
              ·
                refine ⟨31454502472550168112237841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167757346520267563265268485 31454502472550168112237841)
                ·
                  refine ⟨23590876854412626084178381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31454502472550168112237841 23590876854412626084178381)
                  ·
                    refine ⟨8846578820404734781566893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23590876854412626084178381 8846578820404734781566893)
                    ·
                      refine ⟨3317467057651775543087585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8846578820404734781566893 3317467057651775543087585)
                      ·
                        rfl

theorem cell23_6460744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_6460744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460744 prefixEnd_6460744 := by exact prefixLift 6460744
  have htrace : WordTrace (prefixWord ++ tailWord_6460744) baseStart_6460744 baseEnd_6460744 := by
    simpa [prefixWord, tailWord_6460744, baseEnd_6460744] using wordTrace_append hprefix tailTrace_6460744
  have hstable : (prefixWord ++ tailWord_6460744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460744).length < 2 ^ (prefixWord ++ tailWord_6460744).sum := by decide
  have hdescent : baseEnd_6460744 < baseStart_6460744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460777 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 1, 10]
def baseStart_6460777 : Nat := 118140960795 + 6460777 * 2 ^ 59
def prefixEnd_6460777 : Nat := 4983230072969 + 3 ^ 40 * 6460777 * 2
def baseEnd_6460777 : Nat := 1105828000837791304658311

theorem tailTrace_6460777 : CollatzResearch.WordTrace tailWord_6460777 prefixEnd_6460777 1105828000837791304658311 := by
  unfold tailWord_6460777
  simp only [CollatzResearch.WordTrace]
  refine ⟨235643896114715816709524585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157095930743143877806349723 235643896114715816709524585)
  ·
    refine ⟨176732922086036862532143439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235643896114715816709524585 176732922086036862532143439)
    ·
      refine ⟨265099383129055293798215159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176732922086036862532143439 265099383129055293798215159)
      ·
        refine ⟨397649074693582940697322739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265099383129055293798215159 397649074693582940697322739)
        ·
          refine ⟨596473612040374411045984109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397649074693582940697322739 596473612040374411045984109)
          ·
            refine ⟨223677604515140404142244041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 596473612040374411045984109 223677604515140404142244041)
            ·
              refine ⟨167758203386355303106683031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223677604515140404142244041 167758203386355303106683031)
              ·
                refine ⟨251637305079532954660024547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167758203386355303106683031 251637305079532954660024547)
                ·
                  refine ⟨377455957619299431990036821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251637305079532954660024547 377455957619299431990036821)
                  ·
                    refine ⟨1105828000837791304658311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 377455957619299431990036821 1105828000837791304658311)
                    ·
                      rfl

theorem cell23_6460777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_6460777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460777 prefixEnd_6460777 := by exact prefixLift 6460777
  have htrace : WordTrace (prefixWord ++ tailWord_6460777) baseStart_6460777 baseEnd_6460777 := by
    simpa [prefixWord, tailWord_6460777, baseEnd_6460777] using wordTrace_append hprefix tailTrace_6460777
  have hstable : (prefixWord ++ tailWord_6460777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460777).length < 2 ^ (prefixWord ++ tailWord_6460777).sum := by decide
  have hdescent : baseEnd_6460777 < baseStart_6460777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460781 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_6460781 : Nat := 118140960795 + 6460781 * 2 ^ 59
def prefixEnd_6460781 : Nat := 4983230072969 + 3 ^ 40 * 6460781 * 2
def baseEnd_6460781 : Nat := 1105828685478663966108305

theorem tailTrace_6460781 : CollatzResearch.WordTrace tailWord_6460781 prefixEnd_6460781 1105828685478663966108305 := by
  unfold tailWord_6460781
  simp only [CollatzResearch.WordTrace]
  refine ⟨235644042006701325392670197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157096028004467550261780131 235644042006701325392670197)
  ·
    refine ⟨22091628938128249255562831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235644042006701325392670197 22091628938128249255562831)
    ·
      refine ⟨33137443407192373883344247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22091628938128249255562831 33137443407192373883344247)
      ·
        refine ⟨49706165110788560825016371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33137443407192373883344247 49706165110788560825016371)
        ·
          refine ⟨74559247666182841237524557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49706165110788560825016371 74559247666182841237524557)
          ·
            refine ⟨27959717874818565464071709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74559247666182841237524557 27959717874818565464071709)
            ·
              refine ⟨10484894203056962049026891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27959717874818565464071709 10484894203056962049026891)
              ·
                refine ⟨15727341304585443073540337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10484894203056962049026891 15727341304585443073540337)
                ·
                  refine ⟨11795505978439082305155253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15727341304585443073540337 11795505978439082305155253)
                  ·
                    refine ⟨1105828685478663966108305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11795505978439082305155253 1105828685478663966108305)
                    ·
                      rfl

theorem cell23_6460781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_6460781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460781 prefixEnd_6460781 := by exact prefixLift 6460781
  have htrace : WordTrace (prefixWord ++ tailWord_6460781) baseStart_6460781 baseEnd_6460781 := by
    simpa [prefixWord, tailWord_6460781, baseEnd_6460781] using wordTrace_append hprefix tailTrace_6460781
  have hstable : (prefixWord ++ tailWord_6460781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460781).length < 2 ^ (prefixWord ++ tailWord_6460781).sum := by decide
  have hdescent : baseEnd_6460781 < baseStart_6460781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460784 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 4]
def baseStart_6460784 : Nat := 118140960795 + 6460784 * 2 ^ 59
def prefixEnd_6460784 : Nat := 4983230072969 + 3 ^ 40 * 6460784 * 2
def baseEnd_6460784 : Nat := 3317487596877955386587401

theorem tailTrace_6460784 : CollatzResearch.WordTrace tailWord_6460784 prefixEnd_6460784 3317487596877955386587401 := by
  unfold tailWord_6460784
  simp only [CollatzResearch.WordTrace]
  refine ⟨117822075712845228452514703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157096100950460304603352937 117822075712845228452514703)
  ·
    refine ⟨176733113569267842678772055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117822075712845228452514703 176733113569267842678772055)
    ·
      refine ⟨265099670353901764018158083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176733113569267842678772055 265099670353901764018158083)
      ·
        refine ⟨397649505530852646027237125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265099670353901764018158083 397649505530852646027237125)
        ·
          refine ⟨74559282287034871130106961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397649505530852646027237125 74559282287034871130106961)
          ·
            refine ⟨55919461715276153347580221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74559282287034871130106961 55919461715276153347580221)
            ·
              refine ⟨20969798143228557505342583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55919461715276153347580221 20969798143228557505342583)
              ·
                refine ⟨31454697214842836258013875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20969798143228557505342583 31454697214842836258013875)
                ·
                  refine ⟨47182045822264254387020813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31454697214842836258013875 47182045822264254387020813)
                  ·
                    refine ⟨17693267183349095395132805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47182045822264254387020813 17693267183349095395132805)
                    ·
                      refine ⟨3317487596877955386587401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17693267183349095395132805 3317487596877955386587401)
                      ·
                        rfl

theorem cell23_6460784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_6460784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460784 prefixEnd_6460784 := by exact prefixLift 6460784
  have htrace : WordTrace (prefixWord ++ tailWord_6460784) baseStart_6460784 baseEnd_6460784 := by
    simpa [prefixWord, tailWord_6460784, baseEnd_6460784] using wordTrace_append hprefix tailTrace_6460784
  have hstable : (prefixWord ++ tailWord_6460784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460784).length < 2 ^ (prefixWord ++ tailWord_6460784).sum := by decide
  have hdescent : baseEnd_6460784 < baseStart_6460784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460787 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 9]
def baseStart_6460787 : Nat := 118140960795 + 6460787 * 2 ^ 59
def prefixEnd_6460787 : Nat := 4983230072969 + 3 ^ 40 * 6460787 * 2
def baseEnd_6460787 : Nat := 3317489137319918874849887

theorem tailTrace_6460787 : CollatzResearch.WordTrace tailWord_6460787 prefixEnd_6460787 3317489137319918874849887 := by
  unfold tailWord_6460787
  simp only [CollatzResearch.WordTrace]
  refine ⟨235644260844679588417388615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157096173896453058944925743 235644260844679588417388615)
  ·
    refine ⟨353466391267019382626082923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235644260844679588417388615 353466391267019382626082923)
    ·
      refine ⟨530199586900529073939124385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353466391267019382626082923 530199586900529073939124385)
      ·
        refine ⟨397649690175396805454343289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530199586900529073939124385 397649690175396805454343289)
        ·
          refine ⟨298237267631547604090757467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397649690175396805454343289 298237267631547604090757467)
          ·
            refine ⟨447355901447321406136136201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298237267631547604090757467 447355901447321406136136201)
            ·
              refine ⟨335516926085491054602102151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447355901447321406136136201 335516926085491054602102151)
              ·
                refine ⟨503275389128236581903153227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335516926085491054602102151 503275389128236581903153227)
                ·
                  refine ⟨754913083692354872854729841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503275389128236581903153227 754913083692354872854729841)
                  ·
                    refine ⟨566184812769266154641047381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 754913083692354872854729841 566184812769266154641047381)
                    ·
                      refine ⟨3317489137319918874849887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 566184812769266154641047381 3317489137319918874849887)
                      ·
                        rfl

theorem cell23_6460787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_6460787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460787 prefixEnd_6460787 := by exact prefixLift 6460787
  have htrace : WordTrace (prefixWord ++ tailWord_6460787) baseStart_6460787 baseEnd_6460787 := by
    simpa [prefixWord, tailWord_6460787, baseEnd_6460787] using wordTrace_append hprefix tailTrace_6460787
  have hstable : (prefixWord ++ tailWord_6460787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460787).length < 2 ^ (prefixWord ++ tailWord_6460787).sum := by decide
  have hdescent : baseEnd_6460787 < baseStart_6460787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460811 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 3, 4]
def baseStart_6460811 : Nat := 118140960795 + 6460811 * 2 ^ 59
def prefixEnd_6460811 : Nat := 4983230072969 + 3 ^ 40 * 6460811 * 2
def baseEnd_6460811 : Nat := 1105833820285208926983259

theorem tailTrace_6460811 : CollatzResearch.WordTrace tailWord_6460811 prefixEnd_6460811 1105833820285208926983259 := by
  unfold tailWord_6460811
  simp only [CollatzResearch.WordTrace]
  refine ⟨235645136196592640516262287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157096757464395093677508191 235645136196592640516262287)
  ·
    refine ⟨353467704294888960774393431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235645136196592640516262287 353467704294888960774393431)
    ·
      refine ⟨530201556442333441161590147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353467704294888960774393431 530201556442333441161590147)
      ·
        refine ⟨795302334663500161742385221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530201556442333441161590147 795302334663500161742385221)
        ·
          refine ⟨149119187749406280326697229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 795302334663500161742385221 149119187749406280326697229)
          ·
            refine ⟨55919695406027355122511461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149119187749406280326697229 55919695406027355122511461)
            ·
              refine ⟨10484942888630129085470899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55919695406027355122511461 10484942888630129085470899)
              ·
                refine ⟨15727414332945193628206349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10484942888630129085470899 15727414332945193628206349)
                ·
                  refine ⟨5897780374854447610577381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15727414332945193628206349 5897780374854447610577381)
                  ·
                    refine ⟨1105833820285208926983259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5897780374854447610577381 1105833820285208926983259)
                    ·
                      rfl

theorem cell23_6460811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 4].length) (baseStart_6460811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460811 prefixEnd_6460811 := by exact prefixLift 6460811
  have htrace : WordTrace (prefixWord ++ tailWord_6460811) baseStart_6460811 baseEnd_6460811 := by
    simpa [prefixWord, tailWord_6460811, baseEnd_6460811] using wordTrace_append hprefix tailTrace_6460811
  have hstable : (prefixWord ++ tailWord_6460811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460811).length < 2 ^ (prefixWord ++ tailWord_6460811).sum := by decide
  have hdescent : baseEnd_6460811 < baseStart_6460811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460851 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 5, 1, 3]
def baseStart_6460851 : Nat := 118140960795 + 6460851 * 2 ^ 59
def prefixEnd_6460851 : Nat := 4983230072969 + 3 ^ 40 * 6460851 * 2
def baseEnd_6460851 : Nat := 3317522000081806624449593

theorem tailTrace_6460851 : CollatzResearch.WordTrace tailWord_6460851 prefixEnd_6460851 3317522000081806624449593 := by
  unfold tailWord_6460851
  simp only [CollatzResearch.WordTrace]
  refine ⟨235646595116447727347718407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157097730077631818231812271 235646595116447727347718407)
  ·
    refine ⟨353469892674671591021577611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235646595116447727347718407 353469892674671591021577611)
    ·
      refine ⟨530204839012007386532366417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353469892674671591021577611 530204839012007386532366417)
      ·
        refine ⟨397653629259005539899274813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530204839012007386532366417 397653629259005539899274813)
        ·
          refine ⟨149120110972127077462228055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397653629259005539899274813 149120110972127077462228055)
          ·
            refine ⟨223680166458190616193342083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149120110972127077462228055 223680166458190616193342083)
            ·
              refine ⟨335520249687285924290013125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223680166458190616193342083 335520249687285924290013125)
              ·
                refine ⟨62910046816366110804377461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335520249687285924290013125 62910046816366110804377461)
                ·
                  refine ⟨5897816889034322887910387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62910046816366110804377461 5897816889034322887910387)
                  ·
                    refine ⟨8846725333551484331865581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5897816889034322887910387 8846725333551484331865581)
                    ·
                      refine ⟨3317522000081806624449593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8846725333551484331865581 3317522000081806624449593)
                      ·
                        rfl

theorem cell23_6460851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 1, 3].length) (baseStart_6460851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460851 prefixEnd_6460851 := by exact prefixLift 6460851
  have htrace : WordTrace (prefixWord ++ tailWord_6460851) baseStart_6460851 baseEnd_6460851 := by
    simpa [prefixWord, tailWord_6460851, baseEnd_6460851] using wordTrace_append hprefix tailTrace_6460851
  have hstable : (prefixWord ++ tailWord_6460851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460851).length < 2 ^ (prefixWord ++ tailWord_6460851).sum := by decide
  have hdescent : baseEnd_6460851 < baseStart_6460851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460901 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 3, 6]
def baseStart_6460901 : Nat := 118140960795 + 6460901 * 2 ^ 59
def prefixEnd_6460901 : Nat := 4983230072969 + 3 ^ 40 * 6460901 * 2
def baseEnd_6460901 : Nat := 1105849224704843809608121

theorem tailTrace_6460901 : CollatzResearch.WordTrace tailWord_6460901 prefixEnd_6460901 1105849224704843809608121 := by
  unfold tailWord_6460901
  simp only [CollatzResearch.WordTrace]
  refine ⟨235648418766266585887038557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157098945844177723924692371 235648418766266585887038557)
  ·
    refine ⟨88368157037349969707639459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235648418766266585887038557 88368157037349969707639459)
    ·
      refine ⟨132552235556024954561459189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88368157037349969707639459 132552235556024954561459189)
      ·
        refine ⟨12426772083377339490136799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132552235556024954561459189 12426772083377339490136799)
        ·
          refine ⟨18640158125066009235205199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12426772083377339490136799 18640158125066009235205199)
          ·
            refine ⟨27960237187599013852807799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18640158125066009235205199 27960237187599013852807799)
            ·
              refine ⟨41940355781398520779211699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27960237187599013852807799 41940355781398520779211699)
              ·
                refine ⟨62910533672097781168817549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41940355781398520779211699 62910533672097781168817549)
                ·
                  refine ⟨23591450127036667938306581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62910533672097781168817549 23591450127036667938306581)
                  ·
                    refine ⟨1105849224704843809608121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23591450127036667938306581 1105849224704843809608121)
                    ·
                      rfl

theorem cell23_6460901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_6460901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460901 prefixEnd_6460901 := by exact prefixLift 6460901
  have htrace : WordTrace (prefixWord ++ tailWord_6460901) baseStart_6460901 baseEnd_6460901 := by
    simpa [prefixWord, tailWord_6460901, baseEnd_6460901] using wordTrace_append hprefix tailTrace_6460901
  have hstable : (prefixWord ++ tailWord_6460901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460901).length < 2 ^ (prefixWord ++ tailWord_6460901).sum := by decide
  have hdescent : baseEnd_6460901 < baseStart_6460901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460908 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 7, 2, 2]
def baseStart_6460908 : Nat := 118140960795 + 6460908 * 2 ^ 59
def prefixEnd_6460908 : Nat := 4983230072969 + 3 ^ 40 * 6460908 * 2
def baseEnd_6460908 : Nat := 3317551268479112901436831

theorem tailTrace_6460908 : CollatzResearch.WordTrace tailWord_6460908 prefixEnd_6460908 3317551268479112901436831 := by
  unfold tailWord_6460908
  simp only [CollatzResearch.WordTrace]
  refine ⟨117824337038620613041271689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157099116051494150721695585 117824337038620613041271689)
  ·
    refine ⟨88368252778965459780953767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117824337038620613041271689 88368252778965459780953767)
    ·
      refine ⟨132552379168448189671430651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88368252778965459780953767 132552379168448189671430651)
      ·
        refine ⟨198828568752672284507145977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132552379168448189671430651 198828568752672284507145977)
        ·
          refine ⟨149121426564504213380359483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198828568752672284507145977 149121426564504213380359483)
          ·
            refine ⟨223682139846756320070539225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149121426564504213380359483 223682139846756320070539225)
            ·
              refine ⟨167761604885067240052904419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223682139846756320070539225 167761604885067240052904419)
              ·
                refine ⟨251642407327600860079356629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167761604885067240052904419 251642407327600860079356629)
                ·
                  refine ⟨5897868921740645158109921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 251642407327600860079356629 5897868921740645158109921)
                  ·
                    refine ⟨4423401691305483868582441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5897868921740645158109921 4423401691305483868582441)
                    ·
                      refine ⟨3317551268479112901436831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4423401691305483868582441 3317551268479112901436831)
                      ·
                        rfl

theorem cell23_6460908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 2, 2].length) (baseStart_6460908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460908 prefixEnd_6460908 := by exact prefixLift 6460908
  have htrace : WordTrace (prefixWord ++ tailWord_6460908) baseStart_6460908 baseEnd_6460908 := by
    simpa [prefixWord, tailWord_6460908, baseEnd_6460908] using wordTrace_append hprefix tailTrace_6460908
  have hstable : (prefixWord ++ tailWord_6460908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460908).length < 2 ^ (prefixWord ++ tailWord_6460908).sum := by decide
  have hdescent : baseEnd_6460908 < baseStart_6460908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460911 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 5]
def baseStart_6460911 : Nat := 118140960795 + 6460911 * 2 ^ 59
def prefixEnd_6460911 : Nat := 4983230072969 + 3 ^ 40 * 6460911 * 2
def baseEnd_6460911 : Nat := 3317552808921076389699317

theorem tailTrace_6460911 : CollatzResearch.WordTrace tailWord_6460911 prefixEnd_6460911 3317552808921076389699317 := by
  unfold tailWord_6460911
  simp only [CollatzResearch.WordTrace]
  refine ⟨235648783496230357594902587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157099188997486905063268391 235648783496230357594902587)
  ·
    refine ⟨353473175244345536392353881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235648783496230357594902587 353473175244345536392353881)
    ·
      refine ⟨265104881433259152294265411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353473175244345536392353881 265104881433259152294265411)
      ·
        refine ⟨397657322149888728441398117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265104881433259152294265411 397657322149888728441398117)
        ·
          refine ⟨74560747903104136582762147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397657322149888728441398117 74560747903104136582762147)
          ·
            refine ⟨111841121854656204874143221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74560747903104136582762147 111841121854656204874143221)
            ·
              refine ⟨10485105173874019206950927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111841121854656204874143221 10485105173874019206950927)
              ·
                refine ⟨15727657760811028810426391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10485105173874019206950927 15727657760811028810426391)
                ·
                  refine ⟨23591486641216543215639587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15727657760811028810426391 23591486641216543215639587)
                  ·
                    refine ⟨35387229961824814823459381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23591486641216543215639587 35387229961824814823459381)
                    ·
                      refine ⟨3317552808921076389699317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35387229961824814823459381 3317552808921076389699317)
                      ·
                        rfl

theorem cell23_6460911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 5].length) (baseStart_6460911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460911 prefixEnd_6460911 := by exact prefixLift 6460911
  have htrace : WordTrace (prefixWord ++ tailWord_6460911) baseStart_6460911 baseEnd_6460911 := by
    simpa [prefixWord, tailWord_6460911, baseEnd_6460911] using wordTrace_append hprefix tailTrace_6460911
  have hstable : (prefixWord ++ tailWord_6460911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460911).length < 2 ^ (prefixWord ++ tailWord_6460911).sum := by decide
  have hdescent : baseEnd_6460911 < baseStart_6460911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460938 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_6460938 : Nat := 118140960795 + 6460938 * 2 ^ 59
def prefixEnd_6460938 : Nat := 4983230072969 + 3 ^ 40 * 6460938 * 2
def baseEnd_6460938 : Nat := 3317566672898747784061693

theorem tailTrace_6460938 : CollatzResearch.WordTrace tailWord_6460938 prefixEnd_6460938 3317566672898747784061693 := by
  unfold tailWord_6460938
  simp only [CollatzResearch.WordTrace]
  refine ⟨58912442066783135301533867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157099845511421694137423645 58912442066783135301533867)
  ·
    refine ⟨88368663100174702952300801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58912442066783135301533867 88368663100174702952300801)
    ·
      refine ⟨66276497325131027214225601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88368663100174702952300801 66276497325131027214225601)
      ·
        refine ⟨49707372993848270410669201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66276497325131027214225601 49707372993848270410669201)
        ·
          refine ⟨37280529745386202808001901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49707372993848270410669201 37280529745386202808001901)
          ·
            refine ⟨13980198654519826053000713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37280529745386202808001901 13980198654519826053000713)
            ·
              refine ⟨10485148990889869539750535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13980198654519826053000713 10485148990889869539750535)
              ·
                refine ⟨15727723486334804309625803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10485148990889869539750535 15727723486334804309625803)
                ·
                  refine ⟨23591585229502206464438705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15727723486334804309625803 23591585229502206464438705)
                  ·
                    refine ⟨17693688922126654848329029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23591585229502206464438705 17693688922126654848329029)
                    ·
                      refine ⟨3317566672898747784061693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17693688922126654848329029 3317566672898747784061693)
                      ·
                        rfl

theorem cell23_6460938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_6460938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460938 prefixEnd_6460938 := by exact prefixLift 6460938
  have htrace : WordTrace (prefixWord ++ tailWord_6460938) baseStart_6460938 baseEnd_6460938 := by
    simpa [prefixWord, tailWord_6460938, baseEnd_6460938] using wordTrace_append hprefix tailTrace_6460938
  have hstable : (prefixWord ++ tailWord_6460938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460938).length < 2 ^ (prefixWord ++ tailWord_6460938).sum := by decide
  have hdescent : baseEnd_6460938 < baseStart_6460938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460942 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2]
def baseStart_6460942 : Nat := 118140960795 + 6460942 * 2 ^ 59
def prefixEnd_6460942 : Nat := 4983230072969 + 3 ^ 40 * 6460942 * 2
def baseEnd_6460942 : Nat := 3317568726821365768411675

theorem tailTrace_6460942 : CollatzResearch.WordTrace tailWord_6460942 prefixEnd_6460942 3317568726821365768411675 := by
  unfold tailWord_6460942
  simp only [CollatzResearch.WordTrace]
  refine ⟨29456239269889756236160135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157099942772745366592854053 29456239269889756236160135)
  ·
    refine ⟨44184358904834634354240203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29456239269889756236160135 44184358904834634354240203)
    ·
      refine ⟨66276538357251951531360305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44184358904834634354240203 66276538357251951531360305)
      ·
        refine ⟨49707403767938963648520229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66276538357251951531360305 49707403767938963648520229)
        ·
          refine ⟨9320138206488555684097543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49707403767938963648520229 9320138206488555684097543)
          ·
            refine ⟨13980207309732833526146315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9320138206488555684097543 13980207309732833526146315)
            ·
              refine ⟨20970310964599250289219473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13980207309732833526146315 20970310964599250289219473)
              ·
                refine ⟨15727733223449437716914605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20970310964599250289219473 15727733223449437716914605)
                ·
                  refine ⟨5897899958793539143842977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15727733223449437716914605 5897899958793539143842977)
                  ·
                    refine ⟨4423424969095154357882233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5897899958793539143842977 4423424969095154357882233)
                    ·
                      refine ⟨3317568726821365768411675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4423424969095154357882233 3317568726821365768411675)
                      ·
                        rfl

theorem cell23_6460942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_6460942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460942 prefixEnd_6460942 := by exact prefixLift 6460942
  have htrace : WordTrace (prefixWord ++ tailWord_6460942) baseStart_6460942 baseEnd_6460942 := by
    simpa [prefixWord, tailWord_6460942, baseEnd_6460942] using wordTrace_append hprefix tailTrace_6460942
  have hstable : (prefixWord ++ tailWord_6460942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460942).length < 2 ^ (prefixWord ++ tailWord_6460942).sum := by decide
  have hdescent : baseEnd_6460942 < baseStart_6460942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6460991 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 2, 6]
def baseStart_6460991 : Nat := 118140960795 + 6460991 * 2 ^ 59
def prefixEnd_6460991 : Nat := 4983230072969 + 3 ^ 40 * 6460991 * 2
def baseEnd_6460991 : Nat := 1105864629124478692232983

theorem tailTrace_6460991 : CollatzResearch.WordTrace tailWord_6460991 prefixEnd_6460991 1105864629124478692232983 := by
  unfold tailWord_6460991
  simp only [CollatzResearch.WordTrace]
  refine ⟨235651701335940531257814827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157101134223960354171876551 235651701335940531257814827)
  ·
    refine ⟨353477552003910796886722241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235651701335940531257814827 353477552003910796886722241)
    ·
      refine ⟨265108164002933097665041681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353477552003910796886722241 265108164002933097665041681)
      ·
        refine ⟨198831123002199823248781261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265108164002933097665041681 198831123002199823248781261)
        ·
          refine ⟨74561671125824933718292973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198831123002199823248781261 74561671125824933718292973)
          ·
            refine ⟨27960626672184350144359865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74561671125824933718292973 27960626672184350144359865)
            ·
              refine ⟨20970470004138262608269899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27960626672184350144359865 20970470004138262608269899)
              ·
                refine ⟨31455705006207393912404849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20970470004138262608269899 31455705006207393912404849)
                ·
                  refine ⟨23591778754655545434303637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31455705006207393912404849 23591778754655545434303637)
                  ·
                    refine ⟨1105864629124478692232983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23591778754655545434303637 1105864629124478692232983)
                    ·
                      rfl

theorem cell23_6460991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 6].length) (baseStart_6460991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6460991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6460991 prefixEnd_6460991 := by exact prefixLift 6460991
  have htrace : WordTrace (prefixWord ++ tailWord_6460991) baseStart_6460991 baseEnd_6460991 := by
    simpa [prefixWord, tailWord_6460991, baseEnd_6460991] using wordTrace_append hprefix tailTrace_6460991
  have hstable : (prefixWord ++ tailWord_6460991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6460991).length < 2 ^ (prefixWord ++ tailWord_6460991).sum := by decide
  have hdescent : baseEnd_6460991 < baseStart_6460991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6460991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461001 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 2, 4, 3]
def baseStart_6461001 : Nat := 118140960795 + 6461001 * 2 ^ 59
def prefixEnd_6461001 : Nat := 4983230072969 + 3 ^ 40 * 6461001 * 2
def baseEnd_6461001 : Nat := 3317599022179981037573903

theorem tailTrace_6461001 : CollatzResearch.WordTrace tailWord_6461001 prefixEnd_6461001 3317599022179981037573903 := by
  unfold tailWord_6461001
  simp only [CollatzResearch.WordTrace]
  refine ⟨235652066065904302965678857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157101377377269535310452571 235652066065904302965678857)
  ·
    refine ⟨176739049549428227224259143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235652066065904302965678857 176739049549428227224259143)
    ·
      refine ⟨265108574324142340836388715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176739049549428227224259143 265108574324142340836388715)
      ·
        refine ⟨397662861486213511254583073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265108574324142340836388715 397662861486213511254583073)
        ·
          refine ⟨298247146114660133440937305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397662861486213511254583073 298247146114660133440937305)
          ·
            refine ⟨223685359585995100080702979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298247146114660133440937305 223685359585995100080702979)
            ·
              refine ⟨335528039378992650121054469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223685359585995100080702979 335528039378992650121054469)
              ·
                refine ⟨62911507383561121897697713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335528039378992650121054469 62911507383561121897697713)
                ·
                  refine ⟨47183630537670841423273285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62911507383561121897697713 47183630537670841423273285)
                  ·
                    refine ⟨8846930725813282766863741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47183630537670841423273285 8846930725813282766863741)
                    ·
                      refine ⟨3317599022179981037573903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8846930725813282766863741 3317599022179981037573903)
                      ·
                        rfl

theorem cell23_6461001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 4, 3].length) (baseStart_6461001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461001 prefixEnd_6461001 := by exact prefixLift 6461001
  have htrace : WordTrace (prefixWord ++ tailWord_6461001) baseStart_6461001 baseEnd_6461001 := by
    simpa [prefixWord, tailWord_6461001, baseEnd_6461001] using wordTrace_append hprefix tailTrace_6461001
  have hstable : (prefixWord ++ tailWord_6461001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461001).length < 2 ^ (prefixWord ++ tailWord_6461001).sum := by decide
  have hdescent : baseEnd_6461001 < baseStart_6461001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461015 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 4, 2, 2]
def baseStart_6461015 : Nat := 118140960795 + 6461015 * 2 ^ 59
def prefixEnd_6461015 : Nat := 4983230072969 + 3 ^ 40 * 6461015 * 2
def baseEnd_6461015 : Nat := 3317606210909143982798839

theorem tailTrace_6461015 : CollatzResearch.WordTrace tailWord_6461015 prefixEnd_6461015 3317606210909143982798839 := by
  unfold tailWord_6461015
  simp only [CollatzResearch.WordTrace]
  refine ⟨235652576687853583356688499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157101717791902388904458999 235652576687853583356688499)
  ·
    refine ⟨353478865031780375035032749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235652576687853583356688499 353478865031780375035032749)
    ·
      refine ⟨132554574386917640638137281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353478865031780375035032749 132554574386917640638137281)
      ·
        refine ⟨99415930790188230478602961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132554574386917640638137281 99415930790188230478602961)
        ·
          refine ⟨74561948092641172858952221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99415930790188230478602961 74561948092641172858952221)
          ·
            refine ⟨27960730534740439822107083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74561948092641172858952221 27960730534740439822107083)
            ·
              refine ⟨41941095802110659733160625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27960730534740439822107083 41941095802110659733160625)
              ·
                refine ⟨31455821851582994799870469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41941095802110659733160625 31455821851582994799870469)
                ·
                  refine ⟨5897966597171811524975713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31455821851582994799870469 5897966597171811524975713)
                  ·
                    refine ⟨4423474947878858643731785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5897966597171811524975713 4423474947878858643731785)
                    ·
                      refine ⟨3317606210909143982798839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4423474947878858643731785 3317606210909143982798839)
                      ·
                        rfl

theorem cell23_6461015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_6461015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461015 prefixEnd_6461015 := by exact prefixLift 6461015
  have htrace : WordTrace (prefixWord ++ tailWord_6461015) baseStart_6461015 baseEnd_6461015 := by
    simpa [prefixWord, tailWord_6461015, baseEnd_6461015] using wordTrace_append hprefix tailTrace_6461015
  have hstable : (prefixWord ++ tailWord_6461015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461015).length < 2 ^ (prefixWord ++ tailWord_6461015).sum := by decide
  have hdescent : baseEnd_6461015 < baseStart_6461015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461032 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_6461032 : Nat := 118140960795 + 6461032 * 2 ^ 59
def prefixEnd_6461032 : Nat := 4983230072969 + 3 ^ 40 * 6461032 * 2
def baseEnd_6461032 : Nat := 3317614940080270416286261

theorem tailTrace_6461032 : CollatzResearch.WordTrace tailWord_6461032 prefixEnd_6461032 3317614940080270416286261 := by
  unfold tailWord_6461032
  simp only [CollatzResearch.WordTrace]
  refine ⟨117826598364395997630028675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157102131152527996840038233 117826598364395997630028675)
  ·
    refine ⟨176739897546593996445043013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117826598364395997630028675 176739897546593996445043013)
    ·
      refine ⟨33138730789986374333445565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176739897546593996445043013 33138730789986374333445565)
      ·
        refine ⟨12427024046244890375042087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33138730789986374333445565 12427024046244890375042087)
        ·
          refine ⟨18640536069367335562563131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12427024046244890375042087 18640536069367335562563131)
          ·
            refine ⟨27960804104051003343844697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18640536069367335562563131 27960804104051003343844697)
            ·
              refine ⟨20970603078038252507883523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27960804104051003343844697 20970603078038252507883523)
              ·
                refine ⟨31455904617057378761825285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20970603078038252507883523 31455904617057378761825285)
                ·
                  refine ⟨5897982115698258517842241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31455904617057378761825285 5897982115698258517842241)
                  ·
                    refine ⟨4423486586773693888381681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5897982115698258517842241 4423486586773693888381681)
                    ·
                      refine ⟨3317614940080270416286261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4423486586773693888381681 3317614940080270416286261)
                      ·
                        rfl

theorem cell23_6461032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_6461032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461032 prefixEnd_6461032 := by exact prefixLift 6461032
  have htrace : WordTrace (prefixWord ++ tailWord_6461032) baseStart_6461032 baseEnd_6461032 := by
    simpa [prefixWord, tailWord_6461032, baseEnd_6461032] using wordTrace_append hprefix tailTrace_6461032
  have hstable : (prefixWord ++ tailWord_6461032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461032).length < 2 ^ (prefixWord ++ tailWord_6461032).sum := by decide
  have hdescent : baseEnd_6461032 < baseStart_6461032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461051 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 4, 5]
def baseStart_6461051 : Nat := 118140960795 + 6461051 * 2 ^ 59
def prefixEnd_6461051 : Nat := 4983230072969 + 3 ^ 40 * 6461051 * 2
def baseEnd_6461051 : Nat := 1105874898737568613982891

theorem tailTrace_6461051 : CollatzResearch.WordTrace tailWord_6461051 prefixEnd_6461051 1105874898737568613982891 := by
  unfold tailWord_6461051
  simp only [CollatzResearch.WordTrace]
  refine ⟨235653889715723161504999007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157102593143815441003332671 235653889715723161504999007)
  ·
    refine ⟨353480834573584742257498511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235653889715723161504999007 353480834573584742257498511)
    ·
      refine ⟨530221251860377113386247767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353480834573584742257498511 530221251860377113386247767)
      ·
        refine ⟨795331877790565670079371651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530221251860377113386247767 795331877790565670079371651)
        ·
          refine ⟨1192997816685848505119057477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795331877790565670079371651 1192997816685848505119057477)
          ·
            refine ⟨223687090628596594709823277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1192997816685848505119057477 223687090628596594709823277)
            ·
              refine ⟨83882658985723723016183729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223687090628596594709823277 83882658985723723016183729)
              ·
                refine ⟨62911994239292792262137797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83882658985723723016183729 62911994239292792262137797)
                ·
                  refine ⟨11795998919867398549150837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62911994239292792262137797 11795998919867398549150837)
                  ·
                    refine ⟨1105874898737568613982891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11795998919867398549150837 1105874898737568613982891)
                    ·
                      rfl

theorem cell23_6461051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 5].length) (baseStart_6461051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461051 prefixEnd_6461051 := by exact prefixLift 6461051
  have htrace : WordTrace (prefixWord ++ tailWord_6461051) baseStart_6461051 baseEnd_6461051 := by
    simpa [prefixWord, tailWord_6461051, baseEnd_6461051] using wordTrace_append hprefix tailTrace_6461051
  have hstable : (prefixWord ++ tailWord_6461051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461051).length < 2 ^ (prefixWord ++ tailWord_6461051).sum := by decide
  have hdescent : baseEnd_6461051 < baseStart_6461051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461061 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_6461061 : Nat := 118140960795 + 6461061 * 2 ^ 59
def prefixEnd_6461061 : Nat := 4983230072969 + 3 ^ 40 * 6461061 * 2
def baseEnd_6461061 : Nat := 3317629831019250802823627

theorem tailTrace_6461061 : CollatzResearch.WordTrace tailWord_6461061 prefixEnd_6461061 3317629831019250802823627 := by
  unfold tailWord_6461061
  simp only [CollatzResearch.WordTrace]
  refine ⟨235654254445686933212863037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157102836297124622141908691 235654254445686933212863037)
  ·
    refine ⟨88370345417132599954823639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235654254445686933212863037 88370345417132599954823639)
    ·
      refine ⟨132555518125698899932235459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88370345417132599954823639 132555518125698899932235459)
      ·
        refine ⟨198833277188548349898353189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132555518125698899932235459 198833277188548349898353189)
        ·
          refine ⟨37281239472852815605941223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198833277188548349898353189 37281239472852815605941223)
          ·
            refine ⟨55921859209279223408911835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37281239472852815605941223 55921859209279223408911835)
            ·
              refine ⟨83882788813918835113367753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55921859209279223408911835 83882788813918835113367753)
              ·
                refine ⟨62912091610439126335025815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83882788813918835113367753 62912091610439126335025815)
                ·
                  refine ⟨94368137415658689502538723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62912091610439126335025815 94368137415658689502538723)
                  ·
                    refine ⟨141552206123488034253808085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94368137415658689502538723 141552206123488034253808085)
                    ·
                      refine ⟨3317629831019250802823627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141552206123488034253808085 3317629831019250802823627)
                      ·
                        rfl

theorem cell23_6461061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_6461061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461061 prefixEnd_6461061 := by exact prefixLift 6461061
  have htrace : WordTrace (prefixWord ++ tailWord_6461061) baseStart_6461061 baseEnd_6461061 := by
    simpa [prefixWord, tailWord_6461061, baseEnd_6461061] using wordTrace_append hprefix tailTrace_6461061
  have hstable : (prefixWord ++ tailWord_6461061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461061).length < 2 ^ (prefixWord ++ tailWord_6461061).sum := by decide
  have hdescent : baseEnd_6461061 < baseStart_6461061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461068 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 2, 5]
def baseStart_6461068 : Nat := 118140960795 + 6461068 * 2 ^ 59
def prefixEnd_6461068 : Nat := 4983230072969 + 3 ^ 40 * 6461068 * 2
def baseEnd_6461068 : Nat := 1105877808461277425145365

theorem tailTrace_6461068 : CollatzResearch.WordTrace tailWord_6461068 prefixEnd_6461068 1105877808461277425145365 := by
  unfold tailWord_6461068
  simp only [CollatzResearch.WordTrace]
  refine ⟨117827254878330786704183929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157103006504441048938911905 117827254878330786704183929)
  ·
    refine ⟨88370441158748090028137947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117827254878330786704183929 88370441158748090028137947)
    ·
      refine ⟨132555661738122135042206921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88370441158748090028137947 132555661738122135042206921)
      ·
        refine ⟨99416746303591601281655191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132555661738122135042206921 99416746303591601281655191)
        ·
          refine ⟨149125119455387401922482787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99416746303591601281655191 149125119455387401922482787)
          ·
            refine ⟨223687679183081102883724181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149125119455387401922482787 223687679183081102883724181)
            ·
              refine ⟨10485359961706926697674571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 223687679183081102883724181 10485359961706926697674571)
              ·
                refine ⟨15728039942560390046511857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10485359961706926697674571 15728039942560390046511857)
                ·
                  refine ⟨11796029956920292534883893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15728039942560390046511857 11796029956920292534883893)
                  ·
                    refine ⟨1105877808461277425145365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11796029956920292534883893 1105877808461277425145365)
                    ·
                      rfl

theorem cell23_6461068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_6461068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461068 prefixEnd_6461068 := by exact prefixLift 6461068
  have htrace : WordTrace (prefixWord ++ tailWord_6461068) baseStart_6461068 baseEnd_6461068 := by
    simpa [prefixWord, tailWord_6461068, baseEnd_6461068] using wordTrace_append hprefix tailTrace_6461068
  have hstable : (prefixWord ++ tailWord_6461068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461068).length < 2 ^ (prefixWord ++ tailWord_6461068).sum := by decide
  have hdescent : baseEnd_6461068 < baseStart_6461068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461091 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 5]
def baseStart_6461091 : Nat := 118140960795 + 6461091 * 2 ^ 59
def prefixEnd_6461091 : Nat := 4983230072969 + 3 ^ 40 * 6461091 * 2
def baseEnd_6461091 : Nat := 3317645235438885685448489

theorem tailTrace_6461091 : CollatzResearch.WordTrace tailWord_6461091 prefixEnd_6461091 3317645235438885685448489 := by
  unfold tailWord_6461091
  simp only [CollatzResearch.WordTrace]
  refine ⟨235655348635578248336455127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157103565757052165557636751 235655348635578248336455127)
  ·
    refine ⟨353483022953367372504682691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235655348635578248336455127 353483022953367372504682691)
    ·
      refine ⟨530224534430051058757024037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353483022953367372504682691 530224534430051058757024037)
      ·
        refine ⟨99417100205634573516942007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 530224534430051058757024037 99417100205634573516942007)
        ·
          refine ⟨149125650308451860275413011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99417100205634573516942007 149125650308451860275413011)
          ·
            refine ⟨223688475462677790413119517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149125650308451860275413011 223688475462677790413119517)
            ·
              refine ⟨83883178298504171404919819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223688475462677790413119517 83883178298504171404919819)
              ·
                refine ⟨125824767447756257107379729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83883178298504171404919819 125824767447756257107379729)
                ·
                  refine ⟨94368575585817192830534797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125824767447756257107379729 94368575585817192830534797)
                  ·
                    refine ⟨35388215844681447311450549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94368575585817192830534797 35388215844681447311450549)
                    ·
                      refine ⟨3317645235438885685448489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35388215844681447311450549 3317645235438885685448489)
                      ·
                        rfl

theorem cell23_6461091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_6461091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461091 prefixEnd_6461091 := by exact prefixLift 6461091
  have htrace : WordTrace (prefixWord ++ tailWord_6461091) baseStart_6461091 baseEnd_6461091 := by
    simpa [prefixWord, tailWord_6461091, baseEnd_6461091] using wordTrace_append hprefix tailTrace_6461091
  have hstable : (prefixWord ++ tailWord_6461091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461091).length < 2 ^ (prefixWord ++ tailWord_6461091).sum := by decide
  have hdescent : baseEnd_6461091 < baseStart_6461091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461131 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 6]
def baseStart_6461131 : Nat := 118140960795 + 6461131 * 2 ^ 59
def prefixEnd_6461131 : Nat := 4983230072969 + 3 ^ 40 * 6461131 * 2
def baseEnd_6461131 : Nat := 3317665774665065528948305

theorem tailTrace_6461131 : CollatzResearch.WordTrace tailWord_6461131 prefixEnd_6461131 3317665774665065528948305 := by
  unfold tailWord_6461131
  simp only [CollatzResearch.WordTrace]
  refine ⟨235656807555433335167911247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157104538370288890111940831 235656807555433335167911247)
  ·
    refine ⟨353485211333150002751866871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235656807555433335167911247 353485211333150002751866871)
    ·
      refine ⟨530227816999725004127800307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353485211333150002751866871 530227816999725004127800307)
      ·
        refine ⟨795341725499587506191700461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530227816999725004127800307 795341725499587506191700461)
        ·
          refine ⟨298253147062345314821887673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 795341725499587506191700461 298253147062345314821887673)
          ·
            refine ⟨223689860296758986116415755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298253147062345314821887673 223689860296758986116415755)
            ·
              refine ⟨335534790445138479174623633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223689860296758986116415755 335534790445138479174623633)
              ·
                refine ⟨251651092833853859380967725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335534790445138479174623633 251651092833853859380967725)
                ·
                  refine ⟨94369159812695197267862897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251651092833853859380967725 94369159812695197267862897)
                  ·
                    refine ⟨70776869859521397950897173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94369159812695197267862897 70776869859521397950897173)
                    ·
                      refine ⟨3317665774665065528948305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70776869859521397950897173 3317665774665065528948305)
                      ·
                        rfl

theorem cell23_6461131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 6].length) (baseStart_6461131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461131 prefixEnd_6461131 := by exact prefixLift 6461131
  have htrace : WordTrace (prefixWord ++ tailWord_6461131) baseStart_6461131 baseEnd_6461131 := by
    simpa [prefixWord, tailWord_6461131, baseEnd_6461131] using wordTrace_append hprefix tailTrace_6461131
  have hstable : (prefixWord ++ tailWord_6461131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461131).length < 2 ^ (prefixWord ++ tailWord_6461131).sum := by decide
  have hdescent : baseEnd_6461131 < baseStart_6461131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461145 : List Nat := [1, 2, 1, 2, 3, 5, 1, 2, 6]
def baseStart_6461145 : Nat := 118140960795 + 6461145 * 2 ^ 59
def prefixEnd_6461145 : Nat := 4983230072969 + 3 ^ 40 * 6461145 * 2
def baseEnd_6461145 : Nat := 368630329266025386019249

theorem tailTrace_6461145 : CollatzResearch.WordTrace tailWord_6461145 prefixEnd_6461145 368630329266025386019249 := by
  unfold tailWord_6461145
  simp only [CollatzResearch.WordTrace]
  refine ⟨235657318177382615558920889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157104878784921743705947259 235657318177382615558920889)
  ·
    refine ⟨176742988633036961669190667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235657318177382615558920889 176742988633036961669190667)
    ·
      refine ⟨265114482949555442503786001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176742988633036961669190667 265114482949555442503786001)
      ·
        refine ⟨198835862212166581877839501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265114482949555442503786001 198835862212166581877839501)
        ·
          refine ⟨74563448329562468204189813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198835862212166581877839501 74563448329562468204189813)
          ·
            refine ⟨6990323280896481394142795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74563448329562468204189813 6990323280896481394142795)
            ·
              refine ⟨10485484921344722091214193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6990323280896481394142795 10485484921344722091214193)
              ·
                refine ⟨7864113691008541568410645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10485484921344722091214193 7864113691008541568410645)
                ·
                  refine ⟨368630329266025386019249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7864113691008541568410645 368630329266025386019249)
                  ·
                    rfl

theorem cell23_6461145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 6].length) (baseStart_6461145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461145 prefixEnd_6461145 := by exact prefixLift 6461145
  have htrace : WordTrace (prefixWord ++ tailWord_6461145) baseStart_6461145 baseEnd_6461145 := by
    simpa [prefixWord, tailWord_6461145, baseEnd_6461145] using wordTrace_append hprefix tailTrace_6461145
  have hstable : (prefixWord ++ tailWord_6461145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461145).length < 2 ^ (prefixWord ++ tailWord_6461145).sum := by decide
  have hdescent : baseEnd_6461145 < baseStart_6461145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461149 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_6461149 : Nat := 118140960795 + 6461149 * 2 ^ 59
def prefixEnd_6461149 : Nat := 4983230072969 + 3 ^ 40 * 6461149 * 2
def baseEnd_6461149 : Nat := 1105891672438948819507741

theorem tailTrace_6461149 : CollatzResearch.WordTrace tailWord_6461149 prefixEnd_6461149 1105891672438948819507741 := by
  unfold tailWord_6461149
  simp only [CollatzResearch.WordTrace]
  refine ⟨235657464069368124242066501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157104976046245416161377667 235657464069368124242066501)
  ·
    refine ⟨44185774513006523295387469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235657464069368124242066501 44185774513006523295387469)
    ·
      refine ⟨16569665442377446235770301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44185774513006523295387469 16569665442377446235770301)
      ·
        refine ⟨6213624540891542338413863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16569665442377446235770301 6213624540891542338413863)
        ·
          refine ⟨9320436811337313507620795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6213624540891542338413863 9320436811337313507620795)
          ·
            refine ⟨13980655217005970261431193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9320436811337313507620795 13980655217005970261431193)
            ·
              refine ⟨10485491412754477696073395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13980655217005970261431193 10485491412754477696073395)
              ·
                refine ⟨15728237119131716544110093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10485491412754477696073395 15728237119131716544110093)
                ·
                  refine ⟨5898088919674393704041285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15728237119131716544110093 5898088919674393704041285)
                  ·
                    refine ⟨1105891672438948819507741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5898088919674393704041285 1105891672438948819507741)
                    ·
                      rfl

theorem cell23_6461149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_6461149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461149 prefixEnd_6461149 := by exact prefixLift 6461149
  have htrace : WordTrace (prefixWord ++ tailWord_6461149) baseStart_6461149 baseEnd_6461149 := by
    simpa [prefixWord, tailWord_6461149, baseEnd_6461149] using wordTrace_append hprefix tailTrace_6461149
  have hstable : (prefixWord ++ tailWord_6461149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461149).length < 2 ^ (prefixWord ++ tailWord_6461149).sum := by decide
  have hdescent : baseEnd_6461149 < baseStart_6461149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461195 : List Nat := [1, 1, 1, 1, 5, 1, 4, 3, 1, 1, 4]
def baseStart_6461195 : Nat := 118140960795 + 6461195 * 2 ^ 59
def prefixEnd_6461195 : Nat := 4983230072969 + 3 ^ 40 * 6461195 * 2
def baseEnd_6461195 : Nat := 3317698637426953278548011

theorem tailTrace_6461195 : CollatzResearch.WordTrace tailWord_6461195 prefixEnd_6461195 3317698637426953278548011 := by
  unfold tailWord_6461195
  simp only [CollatzResearch.WordTrace]
  refine ⟨235659141827201474098241039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157106094551467649398827359 235659141827201474098241039)
  ·
    refine ⟨353488712740802211147361559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235659141827201474098241039 353488712740802211147361559)
    ·
      refine ⟨530233069111203316721042339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353488712740802211147361559 530233069111203316721042339)
      ·
        refine ⟨795349603666804975081563509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530233069111203316721042339 795349603666804975081563509)
        ·
          refine ⟨74564025343762966413896579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 795349603666804975081563509 74564025343762966413896579)
          ·
            refine ⟨111846038015644449620844869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74564025343762966413896579 111846038015644449620844869)
            ·
              refine ⟨20971132127933334303908413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111846038015644449620844869 20971132127933334303908413)
              ·
                refine ⟨7864174547975000363965655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20971132127933334303908413 7864174547975000363965655)
                ·
                  refine ⟨11796261821962500545948483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7864174547975000363965655 11796261821962500545948483)
                  ·
                    refine ⟨17694392732943750818922725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11796261821962500545948483 17694392732943750818922725)
                    ·
                      refine ⟨3317698637426953278548011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17694392732943750818922725 3317698637426953278548011)
                      ·
                        rfl

theorem cell23_6461195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 1, 4].length) (baseStart_6461195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461195 prefixEnd_6461195 := by exact prefixLift 6461195
  have htrace : WordTrace (prefixWord ++ tailWord_6461195) baseStart_6461195 baseEnd_6461195 := by
    simpa [prefixWord, tailWord_6461195, baseEnd_6461195] using wordTrace_append hprefix tailTrace_6461195
  have hstable : (prefixWord ++ tailWord_6461195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461195).length < 2 ^ (prefixWord ++ tailWord_6461195).sum := by decide
  have hdescent : baseEnd_6461195 < baseStart_6461195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461205 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 4, 4]
def baseStart_6461205 : Nat := 118140960795 + 6461205 * 2 ^ 59
def prefixEnd_6461205 : Nat := 4983230072969 + 3 ^ 40 * 6461205 * 2
def baseEnd_6461205 : Nat := 1105901257411166079807655

theorem tailTrace_6461205 : CollatzResearch.WordTrace tailWord_6461205 prefixEnd_6461205 1105901257411166079807655 := by
  unfold tailWord_6461205
  simp only [CollatzResearch.WordTrace]
  refine ⟨235659506557165245806105069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157106337704776830537403379 235659506557165245806105069)
  ·
    refine ⟨88372314958936967177289401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235659506557165245806105069 88372314958936967177289401)
    ·
      refine ⟨66279236219202725382967051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88372314958936967177289401 66279236219202725382967051)
      ·
        refine ⟨99418854328804088074450577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66279236219202725382967051 99418854328804088074450577)
        ·
          refine ⟨74564140746603066055837933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99418854328804088074450577 74564140746603066055837933)
          ·
            refine ⟨27961552779976149770939225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74564140746603066055837933 27961552779976149770939225)
            ·
              refine ⟨20971164584982112328204419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27961552779976149770939225 20971164584982112328204419)
              ·
                refine ⟨31456746877473168492306629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20971164584982112328204419 31456746877473168492306629)
                ·
                  refine ⟨5898140039526219092307493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31456746877473168492306629 5898140039526219092307493)
                  ·
                    refine ⟨1105901257411166079807655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5898140039526219092307493 1105901257411166079807655)
                    ·
                      rfl

theorem cell23_6461205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_6461205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461205 prefixEnd_6461205 := by exact prefixLift 6461205
  have htrace : WordTrace (prefixWord ++ tailWord_6461205) baseStart_6461205 baseEnd_6461205 := by
    simpa [prefixWord, tailWord_6461205, baseEnd_6461205] using wordTrace_append hprefix tailTrace_6461205
  have hstable : (prefixWord ++ tailWord_6461205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461205).length < 2 ^ (prefixWord ++ tailWord_6461205).sum := by decide
  have hdescent : baseEnd_6461205 < baseStart_6461205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461208 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_6461208 : Nat := 118140960795 + 6461208 * 2 ^ 59
def prefixEnd_6461208 : Nat := 4983230072969 + 3 ^ 40 * 6461208 * 2
def baseEnd_6461208 : Nat := 3317705312675461727685451

theorem tailTrace_6461208 : CollatzResearch.WordTrace tailWord_6461208 prefixEnd_6461208 3317705312675461727685451 := by
  unfold tailWord_6461208
  simp only [CollatzResearch.WordTrace]
  refine ⟨117829807988077188659232139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157106410650769584878976185 117829807988077188659232139)
  ·
    refine ⟨176744711982115782988848209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117829807988077188659232139 176744711982115782988848209)
    ·
      refine ⟨132558533986586837241636157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176744711982115782988848209 132558533986586837241636157)
      ·
        refine ⟨49709450244970063965613559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132558533986586837241636157 49709450244970063965613559)
        ·
          refine ⟨74564175367455095948420339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49709450244970063965613559 74564175367455095948420339)
          ·
            refine ⟨111846263051182643922630509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74564175367455095948420339 111846263051182643922630509)
            ·
              refine ⟨41942348644193491470986441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111846263051182643922630509 41942348644193491470986441)
              ·
                refine ⟨31456761483145118603239831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41942348644193491470986441 31456761483145118603239831)
                ·
                  refine ⟨47185142224717677904859747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31456761483145118603239831 47185142224717677904859747)
                  ·
                    refine ⟨70777713337076516857289621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47185142224717677904859747 70777713337076516857289621)
                    ·
                      refine ⟨3317705312675461727685451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70777713337076516857289621 3317705312675461727685451)
                      ·
                        rfl

theorem cell23_6461208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_6461208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461208 prefixEnd_6461208 := by exact prefixLift 6461208
  have htrace : WordTrace (prefixWord ++ tailWord_6461208) baseStart_6461208 baseEnd_6461208 := by
    simpa [prefixWord, tailWord_6461208, baseEnd_6461208] using wordTrace_append hprefix tailTrace_6461208
  have hstable : (prefixWord ++ tailWord_6461208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461208).length < 2 ^ (prefixWord ++ tailWord_6461208).sum := by decide
  have hdescent : baseEnd_6461208 < baseStart_6461208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461215 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 3]
def baseStart_6461215 : Nat := 118140960795 + 6461215 * 2 ^ 59
def prefixEnd_6461215 : Nat := 4983230072969 + 3 ^ 40 * 6461215 * 2
def baseEnd_6461215 : Nat := 3317708907040043200297919

theorem tailTrace_6461215 : CollatzResearch.WordTrace tailWord_6461215 prefixEnd_6461215 3317708907040043200297919 := by
  unfold tailWord_6461215
  simp only [CollatzResearch.WordTrace]
  refine ⟨235659871287129017513969099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157106580858086011675979399 235659871287129017513969099)
  ·
    refine ⟨353489806930693526270953649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235659871287129017513969099 353489806930693526270953649)
    ·
      refine ⟨265117355198020144703215237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353489806930693526270953649 265117355198020144703215237)
      ·
        refine ⟨49709504099628777131852857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265117355198020144703215237 49709504099628777131852857)
        ·
          refine ⟨37282128074721582848889643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49709504099628777131852857 37282128074721582848889643)
          ·
            refine ⟨55923192112082374273334465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37282128074721582848889643 55923192112082374273334465)
            ·
              refine ⟨41942394084061780705000849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55923192112082374273334465 41942394084061780705000849)
              ·
                refine ⟨31456795563046335528750637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41942394084061780705000849 31456795563046335528750637)
                ·
                  refine ⟨11796298336142375823281489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31456795563046335528750637 11796298336142375823281489)
                  ·
                    refine ⟨8847223752106781867461117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11796298336142375823281489 8847223752106781867461117)
                    ·
                      refine ⟨3317708907040043200297919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8847223752106781867461117 3317708907040043200297919)
                      ·
                        rfl

theorem cell23_6461215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_6461215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461215 prefixEnd_6461215 := by exact prefixLift 6461215
  have htrace : WordTrace (prefixWord ++ tailWord_6461215) baseStart_6461215 baseEnd_6461215 := by
    simpa [prefixWord, tailWord_6461215, baseEnd_6461215] using wordTrace_append hprefix tailTrace_6461215
  have hstable : (prefixWord ++ tailWord_6461215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461215).length < 2 ^ (prefixWord ++ tailWord_6461215).sum := by decide
  have hdescent : baseEnd_6461215 < baseStart_6461215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461313 : List Nat := [1, 2, 4, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_6461313 : Nat := 118140960795 + 6461313 * 2 ^ 59
def prefixEnd_6461313 : Nat := 4983230072969 + 3 ^ 40 * 6461313 * 2
def baseEnd_6461313 : Nat := 3317759228144183816872469

theorem tailTrace_6461313 : CollatzResearch.WordTrace tailWord_6461313 prefixEnd_6461313 3317759228144183816872469 := by
  unfold tailWord_6461313
  simp only [CollatzResearch.WordTrace]
  refine ⟨235663445640773980251036593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157108963760515986834024395 235663445640773980251036593)
  ·
    refine ⟨176747584230580485188277445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235663445640773980251036593 176747584230580485188277445)
    ·
      refine ⟨33140172043233840972802021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176747584230580485188277445 33140172043233840972802021)
      ·
        refine ⟨6213782258106345182400379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33140172043233840972802021 6213782258106345182400379)
        ·
          refine ⟨9320673387159517773600569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6213782258106345182400379 9320673387159517773600569)
          ·
            refine ⟨6990505040369638330200427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9320673387159517773600569 6990505040369638330200427)
            ·
              refine ⟨10485757560554457495300641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6990505040369638330200427 10485757560554457495300641)
              ·
                refine ⟨7864318170415843121475481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10485757560554457495300641 7864318170415843121475481)
                ·
                  refine ⟨5898238627811882341106611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7864318170415843121475481 5898238627811882341106611)
                  ·
                    refine ⟨8847357941717823511659917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5898238627811882341106611 8847357941717823511659917)
                    ·
                      refine ⟨3317759228144183816872469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8847357941717823511659917 3317759228144183816872469)
                      ·
                        rfl

theorem cell23_6461313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_6461313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461313 prefixEnd_6461313 := by exact prefixLift 6461313
  have htrace : WordTrace (prefixWord ++ tailWord_6461313) baseStart_6461313 baseEnd_6461313 := by
    simpa [prefixWord, tailWord_6461313, baseEnd_6461313] using wordTrace_append hprefix tailTrace_6461313
  have hstable : (prefixWord ++ tailWord_6461313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461313).length < 2 ^ (prefixWord ++ tailWord_6461313).sum := by decide
  have hdescent : baseEnd_6461313 < baseStart_6461313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461315 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 4]
def baseStart_6461315 : Nat := 118140960795 + 6461315 * 2 ^ 59
def prefixEnd_6461315 : Nat := 4983230072969 + 3 ^ 40 * 6461315 * 2
def baseEnd_6461315 : Nat := 3317760255105492809047459

theorem tailTrace_6461315 : CollatzResearch.WordTrace tailWord_6461315 prefixEnd_6461315 3317760255105492809047459 := by
  unfold tailWord_6461315
  simp only [CollatzResearch.WordTrace]
  refine ⟨235663518586766734592609399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157109012391177823061739599 235663518586766734592609399)
  ·
    refine ⟨353495277880150101888914099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235663518586766734592609399 353495277880150101888914099)
    ·
      refine ⟨530242916820225152833371149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353495277880150101888914099 530242916820225152833371149)
      ·
        refine ⟨198841093807584432312514181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 530242916820225152833371149 198841093807584432312514181)
        ·
          refine ⟨37282705088922081058596409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198841093807584432312514181 37282705088922081058596409)
          ·
            refine ⟨27962028816691560793947307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37282705088922081058596409 27962028816691560793947307)
            ·
              refine ⟨41943043225037341190920961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27962028816691560793947307 41943043225037341190920961)
              ·
                refine ⟨31457282418778005893190721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41943043225037341190920961 31457282418778005893190721)
                ·
                  refine ⟨23592961814083504419893041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31457282418778005893190721 23592961814083504419893041)
                  ·
                    refine ⟨17694721360562628314919781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23592961814083504419893041 17694721360562628314919781)
                    ·
                      refine ⟨3317760255105492809047459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17694721360562628314919781 3317760255105492809047459)
                      ·
                        rfl

theorem cell23_6461315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_6461315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461315 prefixEnd_6461315 := by exact prefixLift 6461315
  have htrace : WordTrace (prefixWord ++ tailWord_6461315) baseStart_6461315 baseEnd_6461315 := by
    simpa [prefixWord, tailWord_6461315, baseEnd_6461315] using wordTrace_append hprefix tailTrace_6461315
  have hstable : (prefixWord ++ tailWord_6461315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461315).length < 2 ^ (prefixWord ++ tailWord_6461315).sum := by decide
  have hdescent : baseEnd_6461315 < baseStart_6461315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461328 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 8]
def baseStart_6461328 : Nat := 118140960795 + 6461328 * 2 ^ 59
def prefixEnd_6461328 : Nat := 4983230072969 + 3 ^ 40 * 6461328 * 2
def baseEnd_6461328 : Nat := 3317766930354001258184899

theorem tailTrace_6461328 : CollatzResearch.WordTrace tailWord_6461328 prefixEnd_6461328 3317766930354001258184899 := by
  unfold tailWord_6461328
  simp only [CollatzResearch.WordTrace]
  refine ⟨117831996367859818906416319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157109328490479758541888425 117831996367859818906416319)
  ·
    refine ⟨176747994551789728359624479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117831996367859818906416319 176747994551789728359624479)
    ·
      refine ⟨265121991827684592539436719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176747994551789728359624479 265121991827684592539436719)
      ·
        refine ⟨397682987741526888809155079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265121991827684592539436719 397682987741526888809155079)
        ·
          refine ⟨596524481612290333213732619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397682987741526888809155079 596524481612290333213732619)
          ·
            refine ⟨894786722418435499820598929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596524481612290333213732619 894786722418435499820598929)
            ·
              refine ⟨671090041813826624865449197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894786722418435499820598929 671090041813826624865449197)
              ·
                refine ⟨251658765680184984324543449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 671090041813826624865449197 251658765680184984324543449)
                ·
                  refine ⟨188744074260138738243407587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251658765680184984324543449 188744074260138738243407587)
                  ·
                    refine ⟨283116111390208107365111381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188744074260138738243407587 283116111390208107365111381)
                    ·
                      refine ⟨3317766930354001258184899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 283116111390208107365111381 3317766930354001258184899)
                      ·
                        rfl

theorem cell23_6461328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_6461328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461328 prefixEnd_6461328 := by exact prefixLift 6461328
  have htrace : WordTrace (prefixWord ++ tailWord_6461328) baseStart_6461328 baseEnd_6461328 := by
    simpa [prefixWord, tailWord_6461328, baseEnd_6461328] using wordTrace_append hprefix tailTrace_6461328
  have hstable : (prefixWord ++ tailWord_6461328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461328).length < 2 ^ (prefixWord ++ tailWord_6461328).sum := by decide
  have hdescent : baseEnd_6461328 < baseStart_6461328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461332 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_6461332 : Nat := 118140960795 + 6461332 * 2 ^ 59
def prefixEnd_6461332 : Nat := 4983230072969 + 3 ^ 40 * 6461332 * 2
def baseEnd_6461332 : Nat := 3317768984276619242534881

theorem tailTrace_6461332 : CollatzResearch.WordTrace tailWord_6461332 prefixEnd_6461332 3317768984276619242534881 := by
  unfold tailWord_6461332
  simp only [CollatzResearch.WordTrace]
  refine ⟨117832069313852573247989125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157109425751803430997318833 117832069313852573247989125)
  ·
    refine ⟨22093512996347357483997961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117832069313852573247989125 22093512996347357483997961)
    ·
      refine ⟨16570134747260518112998471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22093512996347357483997961 16570134747260518112998471)
      ·
        refine ⟨24855202120890777169497707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16570134747260518112998471 24855202120890777169497707)
        ·
          refine ⟨37282803181336165754246561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24855202120890777169497707 37282803181336165754246561)
          ·
            refine ⟨27962102386002124315684921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37282803181336165754246561 27962102386002124315684921)
            ·
              refine ⟨20971576789501593236763691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27962102386002124315684921 20971576789501593236763691)
              ·
                refine ⟨31457365184252389855145537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20971576789501593236763691 31457365184252389855145537)
                ·
                  refine ⟨23593023888189292391359153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31457365184252389855145537 23593023888189292391359153)
                  ·
                    refine ⟨17694767916141969293519365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23593023888189292391359153 17694767916141969293519365)
                    ·
                      refine ⟨3317768984276619242534881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17694767916141969293519365 3317768984276619242534881)
                      ·
                        rfl

theorem cell23_6461332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_6461332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461332 prefixEnd_6461332 := by exact prefixLift 6461332
  have htrace : WordTrace (prefixWord ++ tailWord_6461332) baseStart_6461332 baseEnd_6461332 := by
    simpa [prefixWord, tailWord_6461332, baseEnd_6461332] using wordTrace_append hprefix tailTrace_6461332
  have hstable : (prefixWord ++ tailWord_6461332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461332).length < 2 ^ (prefixWord ++ tailWord_6461332).sum := by decide
  have hdescent : baseEnd_6461332 < baseStart_6461332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461392 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 2, 4, 2]
def baseStart_6461392 : Nat := 118140960795 + 6461392 * 2 ^ 59
def prefixEnd_6461392 : Nat := 4983230072969 + 3 ^ 40 * 6461392 * 2
def baseEnd_6461392 : Nat := 3317799793115889007784605

theorem tailTrace_6461392 : CollatzResearch.WordTrace tailWord_6461392 prefixEnd_6461392 3317799793115889007784605 := by
  unfold tailWord_6461392
  simp only [CollatzResearch.WordTrace]
  refine ⟨117833163503743888371581215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157110884671658517828774953 117833163503743888371581215)
  ·
    refine ⟨176749745255615832557371823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117833163503743888371581215 176749745255615832557371823)
    ·
      refine ⟨265124617883423748836057735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176749745255615832557371823 265124617883423748836057735)
      ·
        refine ⟨397686926825135623254086603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265124617883423748836057735 397686926825135623254086603)
        ·
          refine ⟨596530390237703434881129905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397686926825135623254086603 596530390237703434881129905)
          ·
            refine ⟨447397792678277576160847429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 596530390237703434881129905 447397792678277576160847429)
            ·
              refine ⟨83887086127177045530158893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 447397792678277576160847429 83887086127177045530158893)
              ·
                refine ⟨31457657297691392073809585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83887086127177045530158893 31457657297691392073809585)
                ·
                  refine ⟨23593242973268544055357189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31457657297691392073809585 23593242973268544055357189)
                  ·
                    refine ⟨4423733057487852010379473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23593242973268544055357189 4423733057487852010379473)
                    ·
                      refine ⟨3317799793115889007784605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4423733057487852010379473 3317799793115889007784605)
                      ·
                        rfl

theorem cell23_6461392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2, 4, 2].length) (baseStart_6461392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461392 prefixEnd_6461392 := by exact prefixLift 6461392
  have htrace : WordTrace (prefixWord ++ tailWord_6461392) baseStart_6461392 baseEnd_6461392 := by
    simpa [prefixWord, tailWord_6461392, baseEnd_6461392] using wordTrace_append hprefix tailTrace_6461392
  have hstable : (prefixWord ++ tailWord_6461392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461392).length < 2 ^ (prefixWord ++ tailWord_6461392).sum := by decide
  have hdescent : baseEnd_6461392 < baseStart_6461392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461460 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_6461460 : Nat := 118140960795 + 6461460 * 2 ^ 59
def prefixEnd_6461460 : Nat := 4983230072969 + 3 ^ 40 * 6461460 * 2
def baseEnd_6461460 : Nat := 3317834709800394741734293

theorem tailTrace_6461460 : CollatzResearch.WordTrace tailWord_6461460 prefixEnd_6461460 3317834709800394741734293 := by
  unfold tailWord_6461460
  simp only [CollatzResearch.WordTrace]
  refine ⟨117834403585620712178318917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157112538114160949571091889 117834403585620712178318917)
  ·
    refine ⟨22093950672303883533434797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117834403585620712178318917 22093950672303883533434797)
    ·
      refine ⟨8285231502113956325038049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22093950672303883533434797 8285231502113956325038049)
      ·
        refine ⟨6213923626585467243778537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8285231502113956325038049 6213923626585467243778537)
        ·
          refine ⟨4660442719939100432833903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6213923626585467243778537 4660442719939100432833903)
          ·
            refine ⟨6990664079908650649250855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4660442719939100432833903 6990664079908650649250855)
            ·
              refine ⟨10485996119862975973876283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6990664079908650649250855 10485996119862975973876283)
              ·
                refine ⟨15728994179794463960814425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10485996119862975973876283 15728994179794463960814425)
                ·
                  refine ⟨11796745634845847970610819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15728994179794463960814425 11796745634845847970610819)
                  ·
                    refine ⟨17695118452268771955916229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11796745634845847970610819 17695118452268771955916229)
                    ·
                      refine ⟨3317834709800394741734293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17695118452268771955916229 3317834709800394741734293)
                      ·
                        rfl

theorem cell23_6461460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_6461460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461460 prefixEnd_6461460 := by exact prefixLift 6461460
  have htrace : WordTrace (prefixWord ++ tailWord_6461460) baseStart_6461460 baseEnd_6461460 := by
    simpa [prefixWord, tailWord_6461460, baseEnd_6461460] using wordTrace_append hprefix tailTrace_6461460
  have hstable : (prefixWord ++ tailWord_6461460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461460).length < 2 ^ (prefixWord ++ tailWord_6461460).sum := by decide
  have hdescent : baseEnd_6461460 < baseStart_6461460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461463 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 2, 2, 3]
def baseStart_6461463 : Nat := 118140960795 + 6461463 * 2 ^ 59
def prefixEnd_6461463 : Nat := 4983230072969 + 3 ^ 40 * 6461463 * 2
def baseEnd_6461463 : Nat := 3317836250242358229996779

theorem tailTrace_6461463 : CollatzResearch.WordTrace tailWord_6461463 prefixEnd_6461463 3317836250242358229996779 := by
  unfold tailWord_6461463
  simp only [CollatzResearch.WordTrace]
  refine ⟨235668916590230555868997043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157112611060153703912664695 235668916590230555868997043)
  ·
    refine ⟨353503374885345833803495565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235668916590230555868997043 353503374885345833803495565)
    ·
      refine ⟨132563765582004687676310837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353503374885345833803495565 132563765582004687676310837)
      ·
        refine ⟨12427853023312939469654141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132563765582004687676310837 12427853023312939469654141)
        ·
          refine ⟨4660444883742352301120303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12427853023312939469654141 4660444883742352301120303)
          ·
            refine ⟨6990667325613528451680455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4660444883742352301120303 6990667325613528451680455)
            ·
              refine ⟨10486000988420292677520683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6990667325613528451680455 10486000988420292677520683)
              ·
                refine ⟨15729001482630439016281025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10486000988420292677520683 15729001482630439016281025)
                ·
                  refine ⟨11796751111972829262210769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15729001482630439016281025 11796751111972829262210769)
                  ·
                    refine ⟨8847563333979621946658077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11796751111972829262210769 8847563333979621946658077)
                    ·
                      refine ⟨3317836250242358229996779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8847563333979621946658077 3317836250242358229996779)
                      ·
                        rfl

theorem cell23_6461463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_6461463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461463 prefixEnd_6461463 := by exact prefixLift 6461463
  have htrace : WordTrace (prefixWord ++ tailWord_6461463) baseStart_6461463 baseEnd_6461463 := by
    simpa [prefixWord, tailWord_6461463, baseEnd_6461463] using wordTrace_append hprefix tailTrace_6461463
  have hstable : (prefixWord ++ tailWord_6461463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461463).length < 2 ^ (prefixWord ++ tailWord_6461463).sum := by decide
  have hdescent : baseEnd_6461463 < baseStart_6461463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461499 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 7, 2, 2]
def baseStart_6461499 : Nat := 118140960795 + 6461499 * 2 ^ 59
def prefixEnd_6461499 : Nat := 4983230072969 + 3 ^ 40 * 6461499 * 2
def baseEnd_6461499 : Nat := 3317854735545920089146613

theorem tailTrace_6461499 : CollatzResearch.WordTrace tailWord_6461499 prefixEnd_6461499 3317854735545920089146613 := by
  unfold tailWord_6461499
  simp only [CollatzResearch.WordTrace]
  refine ⟨235670229618100134017307551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157113486412066756011538367 235670229618100134017307551)
  ·
    refine ⟨353505344427150201025961327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235670229618100134017307551 353505344427150201025961327)
    ·
      refine ⟨530258016640725301538941991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353505344427150201025961327 530258016640725301538941991)
      ·
        refine ⟨795387024961087952308412987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530258016640725301538941991 795387024961087952308412987)
        ·
          refine ⟨1193080537441631928462619481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795387024961087952308412987 1193080537441631928462619481)
          ·
            refine ⟨894810403081223946346964611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1193080537441631928462619481 894810403081223946346964611)
            ·
              refine ⟨1342215604621835919520446917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894810403081223946346964611 1342215604621835919520446917)
              ·
                refine ⟨251665425866594234910083797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1342215604621835919520446917 251665425866594234910083797)
                ·
                  refine ⟨5898408418748302380705089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 251665425866594234910083797 5898408418748302380705089)
                  ·
                    refine ⟨4423806314061226785528817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5898408418748302380705089 4423806314061226785528817)
                    ·
                      refine ⟨3317854735545920089146613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4423806314061226785528817 3317854735545920089146613)
                      ·
                        rfl

theorem cell23_6461499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 2, 2].length) (baseStart_6461499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461499 prefixEnd_6461499 := by exact prefixLift 6461499
  have htrace : WordTrace (prefixWord ++ tailWord_6461499) baseStart_6461499 baseEnd_6461499 := by
    simpa [prefixWord, tailWord_6461499, baseEnd_6461499] using wordTrace_append hprefix tailTrace_6461499
  have hstable : (prefixWord ++ tailWord_6461499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461499).length < 2 ^ (prefixWord ++ tailWord_6461499).sum := by decide
  have hdescent : baseEnd_6461499 < baseStart_6461499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461512 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_6461512 : Nat := 118140960795 + 6461512 * 2 ^ 59
def prefixEnd_6461512 : Nat := 4983230072969 + 3 ^ 40 * 6461512 * 2
def baseEnd_6461512 : Nat := 3317861410794428538284053

theorem tailTrace_6461512 : CollatzResearch.WordTrace tailWord_6461512 prefixEnd_6461512 3317861410794428538284053 := by
  unfold tailWord_6461512
  simp only [CollatzResearch.WordTrace]
  refine ⟨117835351883526518618765395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157113802511368691491687193 117835351883526518618765395)
  ·
    refine ⟨176753027825289777928148093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117835351883526518618765395 176753027825289777928148093)
    ·
      refine ⟨66282385434483666723055535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176753027825289777928148093 66282385434483666723055535)
      ·
        refine ⟨99423578151725500084583303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66282385434483666723055535 99423578151725500084583303)
        ·
          refine ⟨149135367227588250126874955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99423578151725500084583303 149135367227588250126874955)
          ·
            refine ⟨223703050841382375190312433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149135367227588250126874955 223703050841382375190312433)
            ·
              refine ⟨167777288131036781392734325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223703050841382375190312433 167777288131036781392734325)
              ·
                refine ⟨15729120762284698255568843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167777288131036781392734325 15729120762284698255568843)
                ·
                  refine ⟨23593681143427047383353265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15729120762284698255568843 23593681143427047383353265)
                  ·
                    refine ⟨17695260857570285537514949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23593681143427047383353265 17695260857570285537514949)
                    ·
                      refine ⟨3317861410794428538284053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17695260857570285537514949 3317861410794428538284053)
                      ·
                        rfl

theorem cell23_6461512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_6461512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461512 prefixEnd_6461512 := by exact prefixLift 6461512
  have htrace : WordTrace (prefixWord ++ tailWord_6461512) baseStart_6461512 baseEnd_6461512 := by
    simpa [prefixWord, tailWord_6461512, baseEnd_6461512] using wordTrace_append hprefix tailTrace_6461512
  have hstable : (prefixWord ++ tailWord_6461512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461512).length < 2 ^ (prefixWord ++ tailWord_6461512).sum := by decide
  have hdescent : baseEnd_6461512 < baseStart_6461512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461515 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 7]
def baseStart_6461515 : Nat := 118140960795 + 6461515 * 2 ^ 59
def prefixEnd_6461515 : Nat := 4983230072969 + 3 ^ 40 * 6461515 * 2
def baseEnd_6461515 : Nat := 3317862951236392026546539

theorem tailTrace_6461515 : CollatzResearch.WordTrace tailWord_6461515 prefixEnd_6461515 3317862951236392026546539 := by
  unfold tailWord_6461515
  simp only [CollatzResearch.WordTrace]
  refine ⟨235670813186042168749889999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157113875457361445833259999 235670813186042168749889999)
  ·
    refine ⟨353506219779063253124834999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235670813186042168749889999 353506219779063253124834999)
    ·
      refine ⟨530259329668594879687252499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353506219779063253124834999 530259329668594879687252499)
      ·
        refine ⟨795388994502892319530878749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530259329668594879687252499 795388994502892319530878749)
        ·
          refine ⟨298270872938584619824079531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 795388994502892319530878749 298270872938584619824079531)
          ·
            refine ⟨447406309407876929736119297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298270872938584619824079531 447406309407876929736119297)
            ·
              refine ⟨335554732055907697302089473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447406309407876929736119297 335554732055907697302089473)
              ·
                refine ⟨251666049041930772976567105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335554732055907697302089473 251666049041930772976567105)
                ·
                  refine ⟨188749536781448079732425329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251666049041930772976567105 188749536781448079732425329)
                  ·
                    refine ⟨141562152586086059799318997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188749536781448079732425329 141562152586086059799318997)
                    ·
                      refine ⟨3317862951236392026546539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141562152586086059799318997 3317862951236392026546539)
                      ·
                        rfl

theorem cell23_6461515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_6461515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461515 prefixEnd_6461515 := by exact prefixLift 6461515
  have htrace : WordTrace (prefixWord ++ tailWord_6461515) baseStart_6461515 baseEnd_6461515 := by
    simpa [prefixWord, tailWord_6461515, baseEnd_6461515] using wordTrace_append hprefix tailTrace_6461515
  have hstable : (prefixWord ++ tailWord_6461515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461515).length < 2 ^ (prefixWord ++ tailWord_6461515).sum := by decide
  have hdescent : baseEnd_6461515 < baseStart_6461515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461516 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 3, 2, 2]
def baseStart_6461516 : Nat := 118140960795 + 6461516 * 2 ^ 59
def prefixEnd_6461516 : Nat := 4983230072969 + 3 ^ 40 * 6461516 * 2
def baseEnd_6461516 : Nat := 3317863464717046522634035

theorem tailTrace_6461516 : CollatzResearch.WordTrace tailWord_6461516 prefixEnd_6461516 3317863464717046522634035 := by
  unfold tailWord_6461516
  simp only [CollatzResearch.WordTrace]
  refine ⟨117835424829519272960338201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157113899772692363947117601 117835424829519272960338201)
  ·
    refine ⟨88376568622139454720253651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117835424829519272960338201 88376568622139454720253651)
    ·
      refine ⟨132564852933209182080380477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88376568622139454720253651 132564852933209182080380477)
      ·
        refine ⟨49711819849953443280142679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132564852933209182080380477 49711819849953443280142679)
        ·
          refine ⟨74567729774930164920214019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49711819849953443280142679 74567729774930164920214019)
          ·
            refine ⟨111851594662395247380321029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74567729774930164920214019 111851594662395247380321029)
            ·
              refine ⟨20972173999199108883810193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111851594662395247380321029 20972173999199108883810193)
              ·
                refine ⟨15729130499399331662857645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20972173999199108883810193 15729130499399331662857645)
                ·
                  refine ⟨5898423937274749373571617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15729130499399331662857645 5898423937274749373571617)
                  ·
                    refine ⟨4423817952956062030178713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5898423937274749373571617 4423817952956062030178713)
                    ·
                      refine ⟨3317863464717046522634035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4423817952956062030178713 3317863464717046522634035)
                      ·
                        rfl

theorem cell23_6461516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_6461516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461516 prefixEnd_6461516 := by exact prefixLift 6461516
  have htrace : WordTrace (prefixWord ++ tailWord_6461516) baseStart_6461516 baseEnd_6461516 := by
    simpa [prefixWord, tailWord_6461516, baseEnd_6461516] using wordTrace_append hprefix tailTrace_6461516
  have hstable : (prefixWord ++ tailWord_6461516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461516).length < 2 ^ (prefixWord ++ tailWord_6461516).sum := by decide
  have hdescent : baseEnd_6461516 < baseStart_6461516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461590 : List Nat := [5, 3, 2, 1, 2, 10]
def baseStart_6461590 : Nat := 118140960795 + 6461590 * 2 ^ 59
def prefixEnd_6461590 : Nat := 4983230072969 + 3 ^ 40 * 6461590 * 2
def baseEnd_6461590 : Nat := 13653915482656293140365

theorem tailTrace_6461590 : CollatzResearch.WordTrace tailWord_6461590 prefixEnd_6461590 13653915482656293140365 := by
  unfold tailWord_6461590
  simp only [CollatzResearch.WordTrace]
  refine ⟨14729596791298153534929389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157115699107180304372580149 14729596791298153534929389)
  ·
    refine ⟨5523598796736807575598521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14729596791298153534929389 5523598796736807575598521)
    ·
      refine ⟨4142699097552605681698891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5523598796736807575598521 4142699097552605681698891)
      ·
        refine ⟨6214048646328908522548337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4142699097552605681698891 6214048646328908522548337)
        ·
          refine ⟨4660536484746681391911253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6214048646328908522548337 4660536484746681391911253)
          ·
            refine ⟨13653915482656293140365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4660536484746681391911253 13653915482656293140365)
            ·
              rfl

theorem cell23_6461590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 10].length) (baseStart_6461590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461590 prefixEnd_6461590 := by exact prefixLift 6461590
  have htrace : WordTrace (prefixWord ++ tailWord_6461590) baseStart_6461590 baseEnd_6461590 := by
    simpa [prefixWord, tailWord_6461590, baseEnd_6461590] using wordTrace_append hprefix tailTrace_6461590
  have hstable : (prefixWord ++ tailWord_6461590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461590).length < 2 ^ (prefixWord ++ tailWord_6461590).sum := by decide
  have hdescent : baseEnd_6461590 < baseStart_6461590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461623 : List Nat := [1, 1, 3, 1, 4, 2, 2, 3, 2, 2, 2]
def baseStart_6461623 : Nat := 118140960795 + 6461623 * 2 ^ 59
def prefixEnd_6461623 : Nat := 4983230072969 + 3 ^ 40 * 6461623 * 2
def baseEnd_6461623 : Nat := 3317918407147077603996043

theorem tailTrace_6461623 : CollatzResearch.WordTrace tailWord_6461623 prefixEnd_6461623 3317918407147077603996043 := by
  unfold tailWord_6461623
  simp only [CollatzResearch.WordTrace]
  refine ⟨235674752269650903194821523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157116501513100602129881015 235674752269650903194821523)
  ·
    refine ⟨353512128404476354792232285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235674752269650903194821523 353512128404476354792232285)
    ·
      refine ⟨132567048151678633047087107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353512128404476354792232285 132567048151678633047087107)
      ·
        refine ⟨198850572227517949570630661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132567048151678633047087107 198850572227517949570630661)
        ·
          refine ⟨37284482292659615544493249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198850572227517949570630661 37284482292659615544493249)
          ·
            refine ⟨27963361719494711658369937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37284482292659615544493249 27963361719494711658369937)
            ·
              refine ⟨20972521289621033743777453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27963361719494711658369937 20972521289621033743777453)
              ·
                refine ⟨7864695483607887653916545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20972521289621033743777453 7864695483607887653916545)
                ·
                  refine ⟨5898521612705915740437409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7864695483607887653916545 5898521612705915740437409)
                  ·
                    refine ⟨4423891209529436805328057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5898521612705915740437409 4423891209529436805328057)
                    ·
                      refine ⟨3317918407147077603996043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4423891209529436805328057 3317918407147077603996043)
                      ·
                        rfl

theorem cell23_6461623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 2, 2].length) (baseStart_6461623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461623 prefixEnd_6461623 := by exact prefixLift 6461623
  have htrace : WordTrace (prefixWord ++ tailWord_6461623) baseStart_6461623 baseEnd_6461623 := by
    simpa [prefixWord, tailWord_6461623, baseEnd_6461623] using wordTrace_append hprefix tailTrace_6461623
  have hstable : (prefixWord ++ tailWord_6461623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461623).length < 2 ^ (prefixWord ++ tailWord_6461623).sum := by decide
  have hdescent : baseEnd_6461623 < baseStart_6461623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461644 : List Nat := [2, 2, 1, 6, 2, 1, 2, 1, 1, 3, 2]
def baseStart_6461644 : Nat := 118140960795 + 6461644 * 2 ^ 59
def prefixEnd_6461644 : Nat := 4983230072969 + 3 ^ 40 * 6461644 * 2
def baseEnd_6461644 : Nat := 3317929190240822021833447

theorem tailTrace_6461644 : CollatzResearch.WordTrace tailWord_6461644 prefixEnd_6461644 3317929190240822021833447 := by
  unfold tailWord_6461644
  simp only [CollatzResearch.WordTrace]
  refine ⟨117837759101287411890667993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157117012135049882520890657 117837759101287411890667993)
  ·
    refine ⟨88378319325965558918000995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117837759101287411890667993 88378319325965558918000995)
    ·
      refine ⟨132567478988948338377001493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88378319325965558918000995 132567478988948338377001493)
      ·
        refine ⟨6214100577606953361421945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 132567478988948338377001493 6214100577606953361421945)
        ·
          refine ⟨4660575433205215021066459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6214100577606953361421945 4660575433205215021066459)
          ·
            refine ⟨6990863149807822531599689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4660575433205215021066459 6990863149807822531599689)
            ·
              refine ⟨5243147362355866898699767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6990863149807822531599689 5243147362355866898699767)
              ·
                refine ⟨7864721043533800348049651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5243147362355866898699767 7864721043533800348049651)
                ·
                  refine ⟨11797081565300700522074477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7864721043533800348049651 11797081565300700522074477)
                  ·
                    refine ⟨4423905586987762695777929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11797081565300700522074477 4423905586987762695777929)
                    ·
                      refine ⟨3317929190240822021833447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4423905586987762695777929 3317929190240822021833447)
                      ·
                        rfl

theorem cell23_6461644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_6461644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461644 prefixEnd_6461644 := by exact prefixLift 6461644
  have htrace : WordTrace (prefixWord ++ tailWord_6461644) baseStart_6461644 baseEnd_6461644 := by
    simpa [prefixWord, tailWord_6461644, baseEnd_6461644] using wordTrace_append hprefix tailTrace_6461644
  have hstable : (prefixWord ++ tailWord_6461644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461644).length < 2 ^ (prefixWord ++ tailWord_6461644).sum := by decide
  have hdescent : baseEnd_6461644 < baseStart_6461644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461646 : List Nat := [4, 1, 1, 1, 4, 1, 1, 5, 5]
def baseStart_6461646 : Nat := 118140960795 + 6461646 * 2 ^ 59
def prefixEnd_6461646 : Nat := 4983230072969 + 3 ^ 40 * 6461646 * 2
def baseEnd_6461646 : Nat := 368658913022459001556493

theorem tailTrace_6461646 : CollatzResearch.WordTrace tailWord_6461646 prefixEnd_6461646 368658913022459001556493 := by
  unfold tailWord_6461646
  simp only [CollatzResearch.WordTrace]
  refine ⟨29459448893570947265363599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157117060765711718748605861 29459448893570947265363599)
  ·
    refine ⟨44189173340356420898045399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29459448893570947265363599 44189173340356420898045399)
    ·
      refine ⟨66283760010534631347068099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44189173340356420898045399 66283760010534631347068099)
      ·
        refine ⟨99425640015801947020602149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66283760010534631347068099 99425640015801947020602149)
        ·
          refine ⟨18642307502962865066362903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99425640015801947020602149 18642307502962865066362903)
          ·
            refine ⟨27963461254444297599544355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18642307502962865066362903 27963461254444297599544355)
            ·
              refine ⟨41945191881666446399316533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27963461254444297599544355 41945191881666446399316533)
              ·
                refine ⟨3932361738906229349935925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41945191881666446399316533 3932361738906229349935925)
                ·
                  refine ⟨368658913022459001556493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3932361738906229349935925 368658913022459001556493)
                  ·
                    rfl

theorem cell23_6461646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_6461646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461646 prefixEnd_6461646 := by exact prefixLift 6461646
  have htrace : WordTrace (prefixWord ++ tailWord_6461646) baseStart_6461646 baseEnd_6461646 := by
    simpa [prefixWord, tailWord_6461646, baseEnd_6461646] using wordTrace_append hprefix tailTrace_6461646
  have hstable : (prefixWord ++ tailWord_6461646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461646).length < 2 ^ (prefixWord ++ tailWord_6461646).sum := by decide
  have hdescent : baseEnd_6461646 < baseStart_6461646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461679 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 4]
def baseStart_6461679 : Nat := 118140960795 + 6461679 * 2 ^ 59
def prefixEnd_6461679 : Nat := 4983230072969 + 3 ^ 40 * 6461679 * 2
def baseEnd_6461679 : Nat := 3317947162063729384895785

theorem tailTrace_6461679 : CollatzResearch.WordTrace tailWord_6461679 prefixEnd_6461679 3317947162063729384895785 := by
  unfold tailWord_6461679
  simp only [CollatzResearch.WordTrace]
  refine ⟨235676794757448024758860091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157117863171632016505906727 235676794757448024758860091)
  ·
    refine ⟨353515192136172037138290137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235676794757448024758860091 353515192136172037138290137)
    ·
      refine ⟨265136394102129027853717603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353515192136172037138290137 265136394102129027853717603)
      ·
        refine ⟨397704591153193541780576405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265136394102129027853717603 397704591153193541780576405)
        ·
          refine ⟨18642402710305947270964519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 397704591153193541780576405 18642402710305947270964519)
          ·
            refine ⟨27963604065458920906446779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18642402710305947270964519 27963604065458920906446779)
            ·
              refine ⟨41945406098188381359670169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27963604065458920906446779 41945406098188381359670169)
              ·
                refine ⟨31459054573641286019752627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41945406098188381359670169 31459054573641286019752627)
                ·
                  refine ⟨47188581860461929029628941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31459054573641286019752627 47188581860461929029628941)
                  ·
                    refine ⟨17695718197673223386110853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47188581860461929029628941 17695718197673223386110853)
                    ·
                      refine ⟨3317947162063729384895785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17695718197673223386110853 3317947162063729384895785)
                      ·
                        rfl

theorem cell23_6461679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_6461679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461679 prefixEnd_6461679 := by exact prefixLift 6461679
  have htrace : WordTrace (prefixWord ++ tailWord_6461679) baseStart_6461679 baseEnd_6461679 := by
    simpa [prefixWord, tailWord_6461679, baseEnd_6461679] using wordTrace_append hprefix tailTrace_6461679
  have hstable : (prefixWord ++ tailWord_6461679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461679).length < 2 ^ (prefixWord ++ tailWord_6461679).sum := by decide
  have hdescent : baseEnd_6461679 < baseStart_6461679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461689 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 5, 4]
def baseStart_6461689 : Nat := 118140960795 + 6461689 * 2 ^ 59
def prefixEnd_6461689 : Nat := 4983230072969 + 3 ^ 40 * 6461689 * 2
def baseEnd_6461689 : Nat := 1105984098956758115256913

theorem tailTrace_6461689 : CollatzResearch.WordTrace tailWord_6461689 prefixEnd_6461689 1105984098956758115256913 := by
  unfold tailWord_6461689
  simp only [CollatzResearch.WordTrace]
  refine ⟨235677159487411796466724121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157118106324941197644482747 235677159487411796466724121)
  ·
    refine ⟨176757869615558847350043091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235677159487411796466724121 176757869615558847350043091)
    ·
      refine ⟨265136804423338271025064637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176757869615558847350043091 265136804423338271025064637)
      ·
        refine ⟨99426301658751851634399239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265136804423338271025064637 99426301658751851634399239)
        ·
          refine ⟨149139452488127777451598859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99426301658751851634399239 149139452488127777451598859)
          ·
            refine ⟨223709178732191666177398289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149139452488127777451598859 223709178732191666177398289)
            ·
              refine ⟨167781884049143749633048717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223709178732191666177398289 167781884049143749633048717)
              ·
                refine ⟨62918206518428906112393269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167781884049143749633048717 62918206518428906112393269)
                ·
                  refine ⟨5898581861102709948036869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62918206518428906112393269 5898581861102709948036869)
                  ·
                    refine ⟨1105984098956758115256913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5898581861102709948036869 1105984098956758115256913)
                    ·
                      rfl

theorem cell23_6461689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 4].length) (baseStart_6461689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461689 prefixEnd_6461689 := by exact prefixLift 6461689
  have htrace : WordTrace (prefixWord ++ tailWord_6461689) baseStart_6461689 baseEnd_6461689 := by
    simpa [prefixWord, tailWord_6461689, baseEnd_6461689] using wordTrace_append hprefix tailTrace_6461689
  have hstable : (prefixWord ++ tailWord_6461689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461689).length < 2 ^ (prefixWord ++ tailWord_6461689).sum := by decide
  have hdescent : baseEnd_6461689 < baseStart_6461689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461699 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 3]
def baseStart_6461699 : Nat := 118140960795 + 6461699 * 2 ^ 59
def prefixEnd_6461699 : Nat := 4983230072969 + 3 ^ 40 * 6461699 * 2
def baseEnd_6461699 : Nat := 3317957431676819306645693

theorem tailTrace_6461699 : CollatzResearch.WordTrace tailWord_6461699 prefixEnd_6461699 3317957431676819306645693 := by
  unfold tailWord_6461699
  simp only [CollatzResearch.WordTrace]
  refine ⟨235677524217375568174588151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157118349478250378783058767 235677524217375568174588151)
  ·
    refine ⟨353516286326063352261882227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235677524217375568174588151 353516286326063352261882227)
    ·
      refine ⟨530274429489095028392823341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353516286326063352261882227 530274429489095028392823341)
      ·
        refine ⟨198852911058410635647308753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 530274429489095028392823341 198852911058410635647308753)
        ·
          refine ⟨149139683293807976735481565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198852911058410635647308753 149139683293807976735481565)
          ·
            refine ⟨55927381235177991275805587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149139683293807976735481565 55927381235177991275805587)
            ·
              refine ⟨83891071852766986913708381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55927381235177991275805587 83891071852766986913708381)
              ·
                refine ⟨31459151944787620092640643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83891071852766986913708381 31459151944787620092640643)
                ·
                  refine ⟨47188727917181430138960965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31459151944787620092640643 47188727917181430138960965)
                  ·
                    refine ⟨8847886484471518151055181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47188727917181430138960965 8847886484471518151055181)
                    ·
                      refine ⟨3317957431676819306645693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8847886484471518151055181 3317957431676819306645693)
                      ·
                        rfl

theorem cell23_6461699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_6461699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461699 prefixEnd_6461699 := by exact prefixLift 6461699
  have htrace : WordTrace (prefixWord ++ tailWord_6461699) baseStart_6461699 baseEnd_6461699 := by
    simpa [prefixWord, tailWord_6461699, baseEnd_6461699] using wordTrace_append hprefix tailTrace_6461699
  have hstable : (prefixWord ++ tailWord_6461699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461699).length < 2 ^ (prefixWord ++ tailWord_6461699).sum := by decide
  have hdescent : baseEnd_6461699 < baseStart_6461699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461719 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 8]
def baseStart_6461719 : Nat := 118140960795 + 6461719 * 2 ^ 59
def prefixEnd_6461719 : Nat := 4983230072969 + 3 ^ 40 * 6461719 * 2
def baseEnd_6461719 : Nat := 368663077921101025377289

theorem tailTrace_6461719 : CollatzResearch.WordTrace tailWord_6461719 prefixEnd_6461719 368663077921101025377289 := by
  unfold tailWord_6461719
  simp only [CollatzResearch.WordTrace]
  refine ⟨235678253677303111590316211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157118835784868741060210807 235678253677303111590316211)
  ·
    refine ⟨353517380515954667385474317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235678253677303111590316211 353517380515954667385474317)
    ·
      refine ⟨132569017693483000269552869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353517380515954667385474317 132569017693483000269552869)
      ·
        refine ⟨24856690817528062550541163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132569017693483000269552869 24856690817528062550541163)
        ·
          refine ⟨37285036226292093825811745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24856690817528062550541163 37285036226292093825811745)
          ·
            refine ⟨27963777169719070369358809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37285036226292093825811745 27963777169719070369358809)
            ·
              refine ⟨20972832877289302777019107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27963777169719070369358809 20972832877289302777019107)
              ·
                refine ⟨31459249315933954165528661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20972832877289302777019107 31459249315933954165528661)
                ·
                  refine ⟨368663077921101025377289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31459249315933954165528661 368663077921101025377289)
                  ·
                    rfl

theorem cell23_6461719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 8].length) (baseStart_6461719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461719 prefixEnd_6461719 := by exact prefixLift 6461719
  have htrace : WordTrace (prefixWord ++ tailWord_6461719) baseStart_6461719 baseEnd_6461719 := by
    simpa [prefixWord, tailWord_6461719, baseEnd_6461719] using wordTrace_append hprefix tailTrace_6461719
  have hstable : (prefixWord ++ tailWord_6461719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461719).length < 2 ^ (prefixWord ++ tailWord_6461719).sum := by decide
  have hdescent : baseEnd_6461719 < baseStart_6461719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461786 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2]
def baseStart_6461786 : Nat := 118140960795 + 6461786 * 2 ^ 59
def prefixEnd_6461786 : Nat := 4983230072969 + 3 ^ 40 * 6461786 * 2
def baseEnd_6461786 : Nat := 3318002104493760466257793

theorem tailTrace_6461786 : CollatzResearch.WordTrace tailWord_6461786 prefixEnd_6461786 3318002104493760466257793 := by
  unfold tailWord_6461786
  simp only [CollatzResearch.WordTrace]
  refine ⟨58920174342015095508251303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157120464912040254688670141 58920174342015095508251303)
  ·
    refine ⟨88380261513022643262376955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58920174342015095508251303 88380261513022643262376955)
    ·
      refine ⟨132570392269533964893565433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88380261513022643262376955 132570392269533964893565433)
      ·
        refine ⟨99427794202150473670174075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132570392269533964893565433 99427794202150473670174075)
        ·
          refine ⟨149141691303225710505261113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99427794202150473670174075 149141691303225710505261113)
          ·
            refine ⟨111856268477419282878945835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149141691303225710505261113 111856268477419282878945835)
            ·
              refine ⟨167784402716128924318418753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111856268477419282878945835 167784402716128924318418753)
              ·
                refine ⟨125838302037096693238814065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167784402716128924318418753 125838302037096693238814065)
                ·
                  refine ⟨94378726527822519929110549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125838302037096693238814065 94378726527822519929110549)
                  ·
                    refine ⟨4424002805991680621677057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94378726527822519929110549 4424002805991680621677057)
                    ·
                      refine ⟨3318002104493760466257793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4424002805991680621677057 3318002104493760466257793)
                      ·
                        rfl

theorem cell23_6461786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_6461786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461786 prefixEnd_6461786 := by exact prefixLift 6461786
  have htrace : WordTrace (prefixWord ++ tailWord_6461786) baseStart_6461786 baseEnd_6461786 := by
    simpa [prefixWord, tailWord_6461786, baseEnd_6461786] using wordTrace_append hprefix tailTrace_6461786
  have hstable : (prefixWord ++ tailWord_6461786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461786).length < 2 ^ (prefixWord ++ tailWord_6461786).sum := by decide
  have hdescent : baseEnd_6461786 < baseStart_6461786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461796 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_6461796 : Nat := 118140960795 + 6461796 * 2 ^ 59
def prefixEnd_6461796 : Nat := 4983230072969 + 3 ^ 40 * 6461796 * 2
def baseEnd_6461796 : Nat := 1106002413100101809044249

theorem tailTrace_6461796 : CollatzResearch.WordTrace tailWord_6461796 prefixEnd_6461796 1106002413100101809044249 := by
  unfold tailWord_6461796
  simp only [CollatzResearch.WordTrace]
  refine ⟨117840531049012076870434621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157120708065349435827246161 117840531049012076870434621)
  ·
    refine ⟨44190199143379528826412983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117840531049012076870434621 44190199143379528826412983)
    ·
      refine ⟨66285298715069293239619475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44190199143379528826412983 66285298715069293239619475)
      ·
        refine ⟨99427948072603939859429213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66285298715069293239619475 99427948072603939859429213)
        ·
          refine ⟨37285480527226477447285955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99427948072603939859429213 37285480527226477447285955)
          ·
            refine ⟨55928220790839716170928933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37285480527226477447285955 55928220790839716170928933)
            ·
              refine ⟨10486541398282446782049175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55928220790839716170928933 10486541398282446782049175)
              ·
                refine ⟨15729812097423670173073763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10486541398282446782049175 15729812097423670173073763)
                ·
                  refine ⟨23594718146135505259610645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15729812097423670173073763 23594718146135505259610645)
                  ·
                    refine ⟨1106002413100101809044249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23594718146135505259610645 1106002413100101809044249)
                    ·
                      rfl

theorem cell23_6461796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_6461796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461796 prefixEnd_6461796 := by exact prefixLift 6461796
  have htrace : WordTrace (prefixWord ++ tailWord_6461796) baseStart_6461796 baseEnd_6461796 := by
    simpa [prefixWord, tailWord_6461796, baseEnd_6461796] using wordTrace_append hprefix tailTrace_6461796
  have hstable : (prefixWord ++ tailWord_6461796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461796).length < 2 ^ (prefixWord ++ tailWord_6461796).sum := by decide
  have hdescent : baseEnd_6461796 < baseStart_6461796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461803 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 3, 2, 2]
def baseStart_6461803 : Nat := 118140960795 + 6461803 * 2 ^ 59
def prefixEnd_6461803 : Nat := 4983230072969 + 3 ^ 40 * 6461803 * 2
def baseEnd_6461803 : Nat := 3318010833664886899745215

theorem tailTrace_6461803 : CollatzResearch.WordTrace tailWord_6461803 prefixEnd_6461803 3318010833664886899745215 := by
  unfold tailWord_6461803
  simp only [CollatzResearch.WordTrace]
  refine ⟨235681317408998793936374063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157120878272665862624249375 235681317408998793936374063)
  ·
    refine ⟨353521976113498190904561095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235681317408998793936374063 353521976113498190904561095)
    ·
      refine ⟨530282964170247286356841643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353521976113498190904561095 530282964170247286356841643)
      ·
        refine ⟨795424446255370929535262465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530282964170247286356841643 795424446255370929535262465)
        ·
          refine ⟨596568334691528197151446849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 795424446255370929535262465 596568334691528197151446849)
          ·
            refine ⟨447426251018646147863585137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 596568334691528197151446849 447426251018646147863585137)
            ·
              refine ⟨335569688263984610897688853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447426251018646147863585137 335569688263984610897688853)
              ·
                refine ⟨15729829137374278635829165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 335569688263984610897688853 15729829137374278635829165)
                ·
                  refine ⟨5898685926515354488435937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15729829137374278635829165 5898685926515354488435937)
                  ·
                    refine ⟨4424014444886515866326953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5898685926515354488435937 4424014444886515866326953)
                    ·
                      refine ⟨3318010833664886899745215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4424014444886515866326953 3318010833664886899745215)
                      ·
                        rfl

theorem cell23_6461803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 2, 2].length) (baseStart_6461803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461803 prefixEnd_6461803 := by exact prefixLift 6461803
  have htrace : WordTrace (prefixWord ++ tailWord_6461803) baseStart_6461803 baseEnd_6461803 := by
    simpa [prefixWord, tailWord_6461803, baseEnd_6461803] using wordTrace_append hprefix tailTrace_6461803
  have hstable : (prefixWord ++ tailWord_6461803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461803).length < 2 ^ (prefixWord ++ tailWord_6461803).sum := by decide
  have hdescent : baseEnd_6461803 < baseStart_6461803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461829 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_6461829 : Nat := 118140960795 + 6461829 * 2 ^ 59
def prefixEnd_6461829 : Nat := 4983230072969 + 3 ^ 40 * 6461829 * 2
def baseEnd_6461829 : Nat := 3318024184161903798020095

theorem tailTrace_6461829 : CollatzResearch.WordTrace tailWord_6461829 prefixEnd_6461829 3318024184161903798020095 := by
  unfold tailWord_6461829
  simp only [CollatzResearch.WordTrace]
  refine ⟨235682265706904600376820541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157121510471269733584547027 235682265706904600376820541)
  ·
    refine ⟨88380849640089225141307703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235682265706904600376820541 88380849640089225141307703)
    ·
      refine ⟨132571274460133837711961555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88380849640089225141307703 132571274460133837711961555)
      ·
        refine ⟨198856911690200756567942333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132571274460133837711961555 198856911690200756567942333)
        ·
          refine ⟨74571341883825283712978375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198856911690200756567942333 74571341883825283712978375)
          ·
            refine ⟨111857012825737925569467563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74571341883825283712978375 111857012825737925569467563)
            ·
              refine ⟨167785519238606888354201345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111857012825737925569467563 167785519238606888354201345)
              ·
                refine ⟨125839139428955166265651009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167785519238606888354201345 125839139428955166265651009)
                ·
                  refine ⟨94379354571716374699238257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125839139428955166265651009 94379354571716374699238257)
                  ·
                    refine ⟨70784515928787281024428693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94379354571716374699238257 70784515928787281024428693)
                    ·
                      refine ⟨3318024184161903798020095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70784515928787281024428693 3318024184161903798020095)
                      ·
                        rfl

theorem cell23_6461829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_6461829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461829 prefixEnd_6461829 := by exact prefixLift 6461829
  have htrace : WordTrace (prefixWord ++ tailWord_6461829) baseStart_6461829 baseEnd_6461829 := by
    simpa [prefixWord, tailWord_6461829, baseEnd_6461829] using wordTrace_append hprefix tailTrace_6461829
  have hstable : (prefixWord ++ tailWord_6461829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461829).length < 2 ^ (prefixWord ++ tailWord_6461829).sum := by decide
  have hdescent : baseEnd_6461829 < baseStart_6461829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461857 : List Nat := [1, 2, 3, 5, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6461857 : Nat := 118140960795 + 6461857 * 2 ^ 59
def prefixEnd_6461857 : Nat := 4983230072969 + 3 ^ 40 * 6461857 * 2
def baseEnd_6461857 : Nat := 3318038561620229688469967

theorem tailTrace_6461857 : CollatzResearch.WordTrace tailWord_6461857 prefixEnd_6461857 3318038561620229688469967 := by
  unfold tailWord_6461857
  simp only [CollatzResearch.WordTrace]
  refine ⟨235683286950803161158839825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157122191300535440772559883 235683286950803161158839825)
  ·
    refine ⟨176762465213102370869129869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235683286950803161158839825 176762465213102370869129869)
    ·
      refine ⟨66285924454913389075923701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176762465213102370869129869 66285924454913389075923701)
      ·
        refine ⟨6214305417648130225867847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66285924454913389075923701 6214305417648130225867847)
        ·
          refine ⟨9321458126472195338801771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6214305417648130225867847 9321458126472195338801771)
          ·
            refine ⟨13982187189708293008202657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9321458126472195338801771 13982187189708293008202657)
            ·
              refine ⟨10486640392281219756151993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13982187189708293008202657 10486640392281219756151993)
              ·
                refine ⟨7864980294210914817113995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10486640392281219756151993 7864980294210914817113995)
                ·
                  refine ⟨11797470441316372225670993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7864980294210914817113995 11797470441316372225670993)
                  ·
                    refine ⟨8848102830987279169253245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11797470441316372225670993 8848102830987279169253245)
                    ·
                      refine ⟨3318038561620229688469967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8848102830987279169253245 3318038561620229688469967)
                      ·
                        rfl

theorem cell23_6461857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6461857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461857 prefixEnd_6461857 := by exact prefixLift 6461857
  have htrace : WordTrace (prefixWord ++ tailWord_6461857) baseStart_6461857 baseEnd_6461857 := by
    simpa [prefixWord, tailWord_6461857, baseEnd_6461857] using wordTrace_append hprefix tailTrace_6461857
  have hstable : (prefixWord ++ tailWord_6461857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461857).length < 2 ^ (prefixWord ++ tailWord_6461857).sum := by decide
  have hdescent : baseEnd_6461857 < baseStart_6461857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461886 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_6461886 : Nat := 118140960795 + 6461886 * 2 ^ 59
def prefixEnd_6461886 : Nat := 4983230072969 + 3 ^ 40 * 6461886 * 2
def baseEnd_6461886 : Nat := 1106017817519736691669111

theorem tailTrace_6461886 : CollatzResearch.WordTrace tailWord_6461886 prefixEnd_6461886 1106017817519736691669111 := by
  unfold tailWord_6461886
  simp only [CollatzResearch.WordTrace]
  refine ⟨29460543083462262388955689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157122896445132066074430341 29460543083462262388955689)
  ·
    refine ⟨22095407312596696791716767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29460543083462262388955689 22095407312596696791716767)
    ·
      refine ⟨33143110968895045187575151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22095407312596696791716767 33143110968895045187575151)
      ·
        refine ⟨49714666453342567781362727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33143110968895045187575151 49714666453342567781362727)
        ·
          refine ⟨74571999680013851672044091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49714666453342567781362727 74571999680013851672044091)
          ·
            refine ⟨111857999520020777508066137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74571999680013851672044091 111857999520020777508066137)
            ·
              refine ⟨83893499640015583131049603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111857999520020777508066137 83893499640015583131049603)
              ·
                refine ⟨125840249460023374696574405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83893499640015583131049603 125840249460023374696574405)
                ·
                  refine ⟨23595046773754382755607701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125840249460023374696574405 23595046773754382755607701)
                  ·
                    refine ⟨1106017817519736691669111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23595046773754382755607701 1106017817519736691669111)
                    ·
                      rfl

theorem cell23_6461886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_6461886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461886 prefixEnd_6461886 := by exact prefixLift 6461886
  have htrace : WordTrace (prefixWord ++ tailWord_6461886) baseStart_6461886 baseEnd_6461886 := by
    simpa [prefixWord, tailWord_6461886, baseEnd_6461886] using wordTrace_append hprefix tailTrace_6461886
  have hstable : (prefixWord ++ tailWord_6461886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461886).length < 2 ^ (prefixWord ++ tailWord_6461886).sum := by decide
  have hdescent : baseEnd_6461886 < baseStart_6461886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461946 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 4, 5]
def baseStart_6461946 : Nat := 118140960795 + 6461946 * 2 ^ 59
def prefixEnd_6461946 : Nat := 4983230072969 + 3 ^ 40 * 6461946 * 2
def baseEnd_6461946 : Nat := 1106028087132826613419019

theorem tailTrace_6461946 : CollatzResearch.WordTrace tailWord_6461946 prefixEnd_6461946 1106028087132826613419019 := by
  unfold tailWord_6461946
  simp only [CollatzResearch.WordTrace]
  refine ⟨58921633261870182339707423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157124355364987152905886461 58921633261870182339707423)
  ·
    refine ⟨88382449892805273509561135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58921633261870182339707423 88382449892805273509561135)
    ·
      refine ⟨132573674839207910264341703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88382449892805273509561135 132573674839207910264341703)
      ·
        refine ⟨198860512258811865396512555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132573674839207910264341703 198860512258811865396512555)
        ·
          refine ⟨298290768388217798094768833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198860512258811865396512555 298290768388217798094768833)
          ·
            refine ⟨223718076291163348571076625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298290768388217798094768833 223718076291163348571076625)
            ·
              refine ⟨167788557218372511428307469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223718076291163348571076625 167788557218372511428307469)
              ·
                refine ⟨62920708956889691785615301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167788557218372511428307469 62920708956889691785615301)
                ·
                  refine ⟨11797632929416817209802869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62920708956889691785615301 11797632929416817209802869)
                  ·
                    refine ⟨1106028087132826613419019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11797632929416817209802869 1106028087132826613419019)
                    ·
                      rfl

theorem cell23_6461946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_6461946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461946 prefixEnd_6461946 := by exact prefixLift 6461946
  have htrace : WordTrace (prefixWord ++ tailWord_6461946) baseStart_6461946 baseEnd_6461946 := by
    simpa [prefixWord, tailWord_6461946, baseEnd_6461946] using wordTrace_append hprefix tailTrace_6461946
  have hstable : (prefixWord ++ tailWord_6461946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461946).length < 2 ^ (prefixWord ++ tailWord_6461946).sum := by decide
  have hdescent : baseEnd_6461946 < baseStart_6461946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461980 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 2, 5]
def baseStart_6461980 : Nat := 118140960795 + 6461980 * 2 ^ 59
def prefixEnd_6461980 : Nat := 4983230072969 + 3 ^ 40 * 6461980 * 2
def baseEnd_6461980 : Nat := 1106033906580244235743967

theorem tailTrace_6461980 : CollatzResearch.WordTrace tailWord_6461980 prefixEnd_6461980 1106033906580244235743967 := by
  unfold tailWord_6461980
  simp only [CollatzResearch.WordTrace]
  refine ⟨117843886564678776582783697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157125182086238368777044929 117843886564678776582783697)
  ·
    refine ⟨88382914923509082437087773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117843886564678776582783697 88382914923509082437087773)
    ·
      refine ⟨33143593096315905913907915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88382914923509082437087773 33143593096315905913907915)
      ·
        refine ⟨49715389644473858870861873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33143593096315905913907915 49715389644473858870861873)
        ·
          refine ⟨37286542233355394153146405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49715389644473858870861873 37286542233355394153146405)
          ·
            refine ⟨6991226668754136403714951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37286542233355394153146405 6991226668754136403714951)
            ·
              refine ⟨10486840003131204605572427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6991226668754136403714951 10486840003131204605572427)
              ·
                refine ⟨15730260004696806908358641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10486840003131204605572427 15730260004696806908358641)
                ·
                  refine ⟨11797695003522605181268981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15730260004696806908358641 11797695003522605181268981)
                  ·
                    refine ⟨1106033906580244235743967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11797695003522605181268981 1106033906580244235743967)
                    ·
                      rfl

theorem cell23_6461980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_6461980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461980 prefixEnd_6461980 := by exact prefixLift 6461980
  have htrace : WordTrace (prefixWord ++ tailWord_6461980) baseStart_6461980 baseEnd_6461980 := by
    simpa [prefixWord, tailWord_6461980, baseEnd_6461980] using wordTrace_append hprefix tailTrace_6461980
  have hstable : (prefixWord ++ tailWord_6461980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461980).length < 2 ^ (prefixWord ++ tailWord_6461980).sum := by decide
  have hdescent : baseEnd_6461980 < baseStart_6461980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461983 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 3, 6, 2]
def baseStart_6461983 : Nat := 118140960795 + 6461983 * 2 ^ 59
def prefixEnd_6461983 : Nat := 4983230072969 + 3 ^ 40 * 6461983 * 2
def baseEnd_6461983 : Nat := 3318103260182696195494387

theorem tailTrace_6461983 : CollatzResearch.WordTrace tailWord_6461983 prefixEnd_6461983 3318103260182696195494387 := by
  unfold tailWord_6461983
  simp only [CollatzResearch.WordTrace]
  refine ⟨235687882548346684677926603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157125255032231123118617735 235687882548346684677926603)
  ·
    refine ⟨353531823822520027016889905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235687882548346684677926603 353531823822520027016889905)
    ·
      refine ⟨265148867866890020262667429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353531823822520027016889905 265148867866890020262667429)
      ·
        refine ⟨49715412725041878799250143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265148867866890020262667429 49715412725041878799250143)
        ·
          refine ⟨74573119087562818198875215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49715412725041878799250143 74573119087562818198875215)
          ·
            refine ⟨111859678631344227298312823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74573119087562818198875215 111859678631344227298312823)
            ·
              refine ⟨167789517947016340947469235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111859678631344227298312823 167789517947016340947469235)
              ·
                refine ⟨251684276920524511421203853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167789517947016340947469235 251684276920524511421203853)
                ·
                  refine ⟨94381603845196691782951445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251684276920524511421203853 94381603845196691782951445)
                  ·
                    refine ⟨4424137680243594927325849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94381603845196691782951445 4424137680243594927325849)
                    ·
                      refine ⟨3318103260182696195494387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4424137680243594927325849 3318103260182696195494387)
                      ·
                        rfl

theorem cell23_6461983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_6461983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461983 prefixEnd_6461983 := by exact prefixLift 6461983
  have htrace : WordTrace (prefixWord ++ tailWord_6461983) baseStart_6461983 baseEnd_6461983 := by
    simpa [prefixWord, tailWord_6461983, baseEnd_6461983] using wordTrace_append hprefix tailTrace_6461983
  have hstable : (prefixWord ++ tailWord_6461983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461983).length < 2 ^ (prefixWord ++ tailWord_6461983).sum := by decide
  have hdescent : baseEnd_6461983 < baseStart_6461983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6461996 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_6461996 : Nat := 118140960795 + 6461996 * 2 ^ 59
def prefixEnd_6461996 : Nat := 4983230072969 + 3 ^ 40 * 6461996 * 2
def baseEnd_6461996 : Nat := 3318109935431204644631827

theorem tailTrace_6461996 : CollatzResearch.WordTrace tailWord_6461996 prefixEnd_6461996 3318109935431204644631827 := by
  unfold tailWord_6461996
  simp only [CollatzResearch.WordTrace]
  refine ⟨117844178348649793949074921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157125571131533058598766561 117844178348649793949074921)
  ·
    refine ⟨88383133761487345461806191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117844178348649793949074921 88383133761487345461806191)
    ·
      refine ⟨132574700642231018192709287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88383133761487345461806191 132574700642231018192709287)
      ·
        refine ⟨198862050963346527289063931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132574700642231018192709287 198862050963346527289063931)
        ·
          refine ⟨298293076445019790933595897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198862050963346527289063931 298293076445019790933595897)
          ·
            refine ⟨223719807333764843200196923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298293076445019790933595897 223719807333764843200196923)
            ·
              refine ⟨335579711000647264800295385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223719807333764843200196923 335579711000647264800295385)
              ·
                refine ⟨251684783250485448600221539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335579711000647264800295385 251684783250485448600221539)
                ·
                  refine ⟨377527174875728172900332309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251684783250485448600221539 377527174875728172900332309)
                  ·
                    refine ⟨17696586322299758104703077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 377527174875728172900332309 17696586322299758104703077)
                    ·
                      refine ⟨3318109935431204644631827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17696586322299758104703077 3318109935431204644631827)
                      ·
                        rfl

theorem cell23_6461996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_6461996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6461996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6461996 prefixEnd_6461996 := by exact prefixLift 6461996
  have htrace : WordTrace (prefixWord ++ tailWord_6461996) baseStart_6461996 baseEnd_6461996 := by
    simpa [prefixWord, tailWord_6461996, baseEnd_6461996] using wordTrace_append hprefix tailTrace_6461996
  have hstable : (prefixWord ++ tailWord_6461996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6461996).length < 2 ^ (prefixWord ++ tailWord_6461996).sum := by decide
  have hdescent : baseEnd_6461996 < baseStart_6461996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6461996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462003 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 3]
def baseStart_6462003 : Nat := 118140960795 + 6462003 * 2 ^ 59
def prefixEnd_6462003 : Nat := 4983230072969 + 3 ^ 40 * 6462003 * 2
def baseEnd_6462003 : Nat := 3318113529795786117244295

theorem tailTrace_6462003 : CollatzResearch.WordTrace tailWord_6462003 prefixEnd_6462003 3318113529795786117244295 := by
  unfold tailWord_6462003
  simp only [CollatzResearch.WordTrace]
  refine ⟨235688612008274228093654663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157125741338849485395769775 235688612008274228093654663)
  ·
    refine ⟨353532918012411342140481995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235688612008274228093654663 353532918012411342140481995)
    ·
      refine ⟨530299377018617013210722993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353532918012411342140481995 530299377018617013210722993)
      ·
        refine ⟨397724532763962759908042245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530299377018617013210722993 397724532763962759908042245)
        ·
          refine ⟨74573349893243017482757921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397724532763962759908042245 74573349893243017482757921)
          ·
            refine ⟨55930012419932263112068441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74573349893243017482757921 55930012419932263112068441)
            ·
              refine ⟨41947509314949197334051331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55930012419932263112068441 41947509314949197334051331)
              ·
                refine ⟨62921263972423796001076997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41947509314949197334051331 62921263972423796001076997)
                ·
                  refine ⟨11797736994829461750201937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62921263972423796001076997 11797736994829461750201937)
                  ·
                    refine ⟨8848302746122096312651453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11797736994829461750201937 8848302746122096312651453)
                    ·
                      refine ⟨3318113529795786117244295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8848302746122096312651453 3318113529795786117244295)
                      ·
                        rfl

theorem cell23_6462003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 3].length) (baseStart_6462003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462003 prefixEnd_6462003 := by exact prefixLift 6462003
  have htrace : WordTrace (prefixWord ++ tailWord_6462003) baseStart_6462003 baseEnd_6462003 := by
    simpa [prefixWord, tailWord_6462003, baseEnd_6462003] using wordTrace_append hprefix tailTrace_6462003
  have hstable : (prefixWord ++ tailWord_6462003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462003).length < 2 ^ (prefixWord ++ tailWord_6462003).sum := by decide
  have hdescent : baseEnd_6462003 < baseStart_6462003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462010 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 3, 4]
def baseStart_6462010 : Nat := 118140960795 + 6462010 * 2 ^ 59
def prefixEnd_6462010 : Nat := 4983230072969 + 3 ^ 40 * 6462010 * 2
def baseEnd_6462010 : Nat := 1106039041386789196618921

theorem tailTrace_6462010 : CollatzResearch.WordTrace tailWord_6462010 prefixEnd_6462010 1106039041386789196618921 := by
  unfold tailWord_6462010
  simp only [CollatzResearch.WordTrace]
  refine ⟨58922216829812217072289871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157125911546165912192772989 58922216829812217072289871)
  ·
    refine ⟨88383325244718325608434807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58922216829812217072289871 88383325244718325608434807)
    ·
      refine ⟨132574987867077488412652211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88383325244718325608434807 132574987867077488412652211)
      ·
        refine ⟨198862481800616232618978317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132574987867077488412652211 198862481800616232618978317)
        ·
          refine ⟨74573430675231087232116869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198862481800616232618978317 74573430675231087232116869)
          ·
            refine ⟨13982518251605828856021913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74573430675231087232116869 13982518251605828856021913)
            ·
              refine ⟨10486888688704371642016435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13982518251605828856021913 10486888688704371642016435)
              ·
                refine ⟨15730333033056557463024653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10486888688704371642016435 15730333033056557463024653)
                ·
                  refine ⟨5898874887396209048634245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15730333033056557463024653 5898874887396209048634245)
                  ·
                    refine ⟨1106039041386789196618921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5898874887396209048634245 1106039041386789196618921)
                    ·
                      rfl

theorem cell23_6462010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_6462010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462010 prefixEnd_6462010 := by exact prefixLift 6462010
  have htrace : WordTrace (prefixWord ++ tailWord_6462010) baseStart_6462010 baseEnd_6462010 := by
    simpa [prefixWord, tailWord_6462010, baseEnd_6462010] using wordTrace_append hprefix tailTrace_6462010
  have hstable : (prefixWord ++ tailWord_6462010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462010).length < 2 ^ (prefixWord ++ tailWord_6462010).sum := by decide
  have hdescent : baseEnd_6462010 < baseStart_6462010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462060 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 4, 3, 2]
def baseStart_6462060 : Nat := 118140960795 + 6462060 * 2 ^ 59
def prefixEnd_6462060 : Nat := 4983230072969 + 3 ^ 40 * 6462060 * 2
def baseEnd_6462060 : Nat := 3318142798193092394231533

theorem tailTrace_6462060 : CollatzResearch.WordTrace tailWord_6462060 prefixEnd_6462060 3318142798193092394231533 := by
  unfold tailWord_6462060
  simp only [CollatzResearch.WordTrace]
  refine ⟨117845345484533863414239817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157127127312711817885653089 117845345484533863414239817)
  ·
    refine ⟨88384009113400397560679863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117845345484533863414239817 88384009113400397560679863)
    ·
      refine ⟨132576013670100596341019795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88384009113400397560679863 132576013670100596341019795)
      ·
        refine ⟨198864020505150894511529693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132576013670100596341019795 198864020505150894511529693)
        ·
          refine ⟨74574007689431585441823635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198864020505150894511529693 74574007689431585441823635)
          ·
            refine ⟨111861011534147378162735453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74574007689431585441823635 111861011534147378162735453)
            ·
              refine ⟨41947879325305266811025795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111861011534147378162735453 41947879325305266811025795)
              ·
                refine ⟨62921818987957900216538693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41947879325305266811025795 62921818987957900216538693)
                ·
                  refine ⟨11797841060242106290601005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62921818987957900216538693 11797841060242106290601005)
                  ·
                    refine ⟨4424190397590789858975377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11797841060242106290601005 4424190397590789858975377)
                    ·
                      refine ⟨3318142798193092394231533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4424190397590789858975377 3318142798193092394231533)
                      ·
                        rfl

theorem cell23_6462060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 3, 2].length) (baseStart_6462060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462060 prefixEnd_6462060 := by exact prefixLift 6462060
  have htrace : WordTrace (prefixWord ++ tailWord_6462060) baseStart_6462060 baseEnd_6462060 := by
    simpa [prefixWord, tailWord_6462060, baseEnd_6462060] using wordTrace_append hprefix tailTrace_6462060
  have hstable : (prefixWord ++ tailWord_6462060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462060).length < 2 ^ (prefixWord ++ tailWord_6462060).sum := by decide
  have hdescent : baseEnd_6462060 < baseStart_6462060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462100 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_6462100 : Nat := 118140960795 + 6462100 * 2 ^ 59
def prefixEnd_6462100 : Nat := 4983230072969 + 3 ^ 40 * 6462100 * 2
def baseEnd_6462100 : Nat := 1106054445806424079243783

theorem tailTrace_6462100 : CollatzResearch.WordTrace tailWord_6462100 prefixEnd_6462100 1106054445806424079243783 := by
  unfold tailWord_6462100
  simp only [CollatzResearch.WordTrace]
  refine ⟨117846074944461406829967877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157128099925948542439957169 117846074944461406829967877)
  ·
    refine ⟨22096139052086513780618977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117846074944461406829967877 22096139052086513780618977)
    ·
      refine ⟨16572104289064885335464233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22096139052086513780618977 16572104289064885335464233)
      ·
        refine ⟨12429078216798664001598175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16572104289064885335464233 12429078216798664001598175)
        ·
          refine ⟨18643617325197996002397263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12429078216798664001598175 18643617325197996002397263)
          ·
            refine ⟨27965425987796994003595895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18643617325197996002397263 27965425987796994003595895)
            ·
              refine ⟨41948138981695491005393843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27965425987796994003595895 41948138981695491005393843)
              ·
                refine ⟨62922208472543236508090765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41948138981695491005393843 62922208472543236508090765)
                ·
                  refine ⟨23595828177203713690534037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62922208472543236508090765 23595828177203713690534037)
                  ·
                    refine ⟨1106054445806424079243783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23595828177203713690534037 1106054445806424079243783)
                    ·
                      rfl

theorem cell23_6462100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_6462100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462100 prefixEnd_6462100 := by exact prefixLift 6462100
  have htrace : WordTrace (prefixWord ++ tailWord_6462100) baseStart_6462100 baseEnd_6462100 := by
    simpa [prefixWord, tailWord_6462100, baseEnd_6462100] using wordTrace_append hprefix tailTrace_6462100
  have hstable : (prefixWord ++ tailWord_6462100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462100).length < 2 ^ (prefixWord ++ tailWord_6462100).sum := by decide
  have hdescent : baseEnd_6462100 < baseStart_6462100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462113 : List Nat := [1, 2, 3, 3, 3, 11]
def baseStart_6462113 : Nat := 118140960795 + 6462113 * 2 ^ 59
def prefixEnd_6462113 : Nat := 4983230072969 + 3 ^ 40 * 6462113 * 2
def baseEnd_6462113 : Nat := 13655020628262471962423

theorem tailTrace_6462113 : CollatzResearch.WordTrace tailWord_6462113 prefixEnd_6462113 13655020628262471962423 := by
  unfold tailWord_6462113
  simp only [CollatzResearch.WordTrace]
  refine ⟨235692624037875716880158993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157128416025250477920105995 235692624037875716880158993)
  ·
    refine ⟨176769468028406787660119245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235692624037875716880158993 176769468028406787660119245)
    ·
      refine ⟨66288550510652545372544717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176769468028406787660119245 66288550510652545372544717)
      ·
        refine ⟨24858206441494704514704269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66288550510652545372544717 24858206441494704514704269)
        ·
          refine ⟨9321827415560514193014101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24858206441494704514704269 9321827415560514193014101)
          ·
            refine ⟨13655020628262471962423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9321827415560514193014101 13655020628262471962423)
            ·
              rfl

theorem cell23_6462113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 11].length) (baseStart_6462113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462113 prefixEnd_6462113 := by exact prefixLift 6462113
  have htrace : WordTrace (prefixWord ++ tailWord_6462113) baseStart_6462113 baseEnd_6462113 := by
    simpa [prefixWord, tailWord_6462113, baseEnd_6462113] using wordTrace_append hprefix tailTrace_6462113
  have hstable : (prefixWord ++ tailWord_6462113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462113).length < 2 ^ (prefixWord ++ tailWord_6462113).sum := by decide
  have hdescent : baseEnd_6462113 < baseStart_6462113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462134 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_6462134 : Nat := 118140960795 + 6462134 * 2 ^ 59
def prefixEnd_6462134 : Nat := 4983230072969 + 3 ^ 40 * 6462134 * 2
def baseEnd_6462134 : Nat := 1106060265253841701568731

theorem tailTrace_6462134 : CollatzResearch.WordTrace tailWord_6462134 prefixEnd_6462134 1106060265253841701568731 := by
  unfold tailWord_6462134
  simp only [CollatzResearch.WordTrace]
  refine ⟨14730836873174977341667091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157128926647199758311115637 14730836873174977341667091)
  ·
    refine ⟨22096255309762466012500637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14730836873174977341667091 22096255309762466012500637)
    ·
      refine ⟨8286095741160924754687739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22096255309762466012500637 8286095741160924754687739)
      ·
        refine ⟨12429143611741387132031609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8286095741160924754687739 12429143611741387132031609)
        ·
          refine ⟨9321857708806040349023707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12429143611741387132031609 9321857708806040349023707)
          ·
            refine ⟨13982786563209060523535561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9321857708806040349023707 13982786563209060523535561)
            ·
              refine ⟨10487089922406795392651671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13982786563209060523535561 10487089922406795392651671)
              ·
                refine ⟨15730634883610193088977507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10487089922406795392651671 15730634883610193088977507)
                ·
                  refine ⟨23595952325415289633466261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15730634883610193088977507 23595952325415289633466261)
                  ·
                    refine ⟨1106060265253841701568731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23595952325415289633466261 1106060265253841701568731)
                    ·
                      rfl

theorem cell23_6462134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_6462134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462134 prefixEnd_6462134 := by exact prefixLift 6462134
  have htrace : WordTrace (prefixWord ++ tailWord_6462134) baseStart_6462134 baseEnd_6462134 := by
    simpa [prefixWord, tailWord_6462134, baseEnd_6462134] using wordTrace_append hprefix tailTrace_6462134
  have hstable : (prefixWord ++ tailWord_6462134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462134).length < 2 ^ (prefixWord ++ tailWord_6462134).sum := by decide
  have hdescent : baseEnd_6462134 < baseStart_6462134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462190 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_6462190 : Nat := 118140960795 + 6462190 * 2 ^ 59
def prefixEnd_6462190 : Nat := 4983230072969 + 3 ^ 40 * 6462190 * 2
def baseEnd_6462190 : Nat := 1106069850226058961868645

theorem tailTrace_6462190 : CollatzResearch.WordTrace tailWord_6462190 prefixEnd_6462190 1106069850226058961868645 := by
  unfold tailWord_6462190
  simp only [CollatzResearch.WordTrace]
  refine ⟨29461929057324594878839003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157130288305731172687141349 29461929057324594878839003)
  ·
    refine ⟨44192893585986892318258505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29461929057324594878839003 44192893585986892318258505)
    ·
      refine ⟨33144670189490169238693879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44192893585986892318258505 33144670189490169238693879)
      ·
        refine ⟨49717005284235253858040819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33144670189490169238693879 49717005284235253858040819)
        ·
          refine ⟨74575507926352880787061229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49717005284235253858040819 74575507926352880787061229)
          ·
            refine ⟨27965815472382330295147961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74575507926352880787061229 27965815472382330295147961)
            ·
              refine ⟨20974361604286747721360971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27965815472382330295147961 20974361604286747721360971)
              ·
                refine ⟨31461542406430121582041457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20974361604286747721360971 31461542406430121582041457)
                ·
                  refine ⟨23596156804822591186531093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31461542406430121582041457 23596156804822591186531093)
                  ·
                    refine ⟨1106069850226058961868645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23596156804822591186531093 1106069850226058961868645)
                    ·
                      rfl

theorem cell23_6462190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_6462190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462190 prefixEnd_6462190 := by exact prefixLift 6462190
  have htrace : WordTrace (prefixWord ++ tailWord_6462190) baseStart_6462190 baseEnd_6462190 := by
    simpa [prefixWord, tailWord_6462190, baseEnd_6462190] using wordTrace_append hprefix tailTrace_6462190
  have hstable : (prefixWord ++ tailWord_6462190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462190).length < 2 ^ (prefixWord ++ tailWord_6462190).sum := by decide
  have hdescent : baseEnd_6462190 < baseStart_6462190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462233 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 3, 7]
def baseStart_6462233 : Nat := 118140960795 + 6462233 * 2 ^ 59
def prefixEnd_6462233 : Nat := 4983230072969 + 3 ^ 40 * 6462233 * 2
def baseEnd_6462233 : Nat := 1106077210115440072456079

theorem tailTrace_6462233 : CollatzResearch.WordTrace tailWord_6462233 prefixEnd_6462233 1106077210115440072456079 := by
  unfold tailWord_6462233
  simp only [CollatzResearch.WordTrace]
  refine ⟨235697000797440977374527353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157131333864960651583018235 235697000797440977374527353)
  ·
    refine ⟨176772750598080733030895515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235697000797440977374527353 176772750598080733030895515)
    ·
      refine ⟨265159125897121099546343273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176772750598080733030895515 265159125897121099546343273)
      ·
        refine ⟨198869344422840824659757455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265159125897121099546343273 198869344422840824659757455)
        ·
          refine ⟨298304016634261236989636183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198869344422840824659757455 298304016634261236989636183)
          ·
            refine ⟨447456024951391855484454275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298304016634261236989636183 447456024951391855484454275)
            ·
              refine ⟨671184037427087783226681413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447456024951391855484454275 671184037427087783226681413)
              ·
                refine ⟨125847007017578959355002765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 671184037427087783226681413 125847007017578959355002765)
                ·
                  refine ⟨47192627631592109758126037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125847007017578959355002765 47192627631592109758126037)
                  ·
                    refine ⟨1106077210115440072456079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47192627631592109758126037 1106077210115440072456079)
                    ·
                      rfl

theorem cell23_6462233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_6462233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462233 prefixEnd_6462233 := by exact prefixLift 6462233
  have htrace : WordTrace (prefixWord ++ tailWord_6462233) baseStart_6462233 baseEnd_6462233 := by
    simpa [prefixWord, tailWord_6462233, baseEnd_6462233] using wordTrace_append hprefix tailTrace_6462233
  have hstable : (prefixWord ++ tailWord_6462233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462233).length < 2 ^ (prefixWord ++ tailWord_6462233).sum := by decide
  have hdescent : baseEnd_6462233 < baseStart_6462233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462290 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_6462290 : Nat := 118140960795 + 6462290 * 2 ^ 59
def prefixEnd_6462290 : Nat := 4983230072969 + 3 ^ 40 * 6462290 * 2
def baseEnd_6462290 : Nat := 3318260898743626494355475

theorem tailTrace_6462290 : CollatzResearch.WordTrace tailWord_6462290 prefixEnd_6462290 3318260898743626494355475 := by
  unfold tailWord_6462290
  simp only [CollatzResearch.WordTrace]
  refine ⟨58924769939558619027338081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157132719838822984072901549 58924769939558619027338081)
  ·
    refine ⟨44193577454668964270503561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58924769939558619027338081 44193577454668964270503561)
    ·
      refine ⟨33145183091001723202877671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44193577454668964270503561 33145183091001723202877671)
      ·
        refine ⟨49717774636502584804316507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33145183091001723202877671 49717774636502584804316507)
        ·
          refine ⟨74576661954753877206474761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49717774636502584804316507 74576661954753877206474761)
          ·
            refine ⟨55932496466065407904856071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74576661954753877206474761 55932496466065407904856071)
            ·
              refine ⟨83898744699098111857284107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55932496466065407904856071 83898744699098111857284107)
              ·
                refine ⟨125848117048647167785926161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83898744699098111857284107 125848117048647167785926161)
                ·
                  refine ⟨94386087786485375839444621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125848117048647167785926161 94386087786485375839444621)
                  ·
                    refine ⟨35394782919932015939791733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94386087786485375839444621 35394782919932015939791733)
                    ·
                      refine ⟨3318260898743626494355475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35394782919932015939791733 3318260898743626494355475)
                      ·
                        rfl

theorem cell23_6462290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_6462290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462290 prefixEnd_6462290 := by exact prefixLift 6462290
  have htrace : WordTrace (prefixWord ++ tailWord_6462290) baseStart_6462290 baseEnd_6462290 := by
    simpa [prefixWord, tailWord_6462290, baseEnd_6462290] using wordTrace_append hprefix tailTrace_6462290
  have hstable : (prefixWord ++ tailWord_6462290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462290).length < 2 ^ (prefixWord ++ tailWord_6462290).sum := by decide
  have hdescent : baseEnd_6462290 < baseStart_6462290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462344 : List Nat := [2, 1, 3, 3, 2, 3, 1, 2, 6]
def baseStart_6462344 : Nat := 118140960795 + 6462344 * 2 ^ 59
def prefixEnd_6462344 : Nat := 4983230072969 + 3 ^ 40 * 6462344 * 2
def baseEnd_6462344 : Nat := 368698736299885475897803

theorem tailTrace_6462344 : CollatzResearch.WordTrace tailWord_6462344 prefixEnd_6462344 368698736299885475897803 := by
  unfold tailWord_6462344
  simp only [CollatzResearch.WordTrace]
  refine ⟨117850524650019421665909043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157134032866692562221212057 117850524650019421665909043)
  ·
    refine ⟨176775786975029132498863565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117850524650019421665909043 176775786975029132498863565)
    ·
      refine ⟨66290920115635924687073837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176775786975029132498863565 66290920115635924687073837)
      ·
        refine ⟨24859095043363471757652689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66290920115635924687073837 24859095043363471757652689)
        ·
          refine ⟨18644321282522603818239517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24859095043363471757652689 18644321282522603818239517)
          ·
            refine ⟨6991620480945976431839819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18644321282522603818239517 6991620480945976431839819)
            ·
              refine ⟨10487430721418964647759729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6991620480945976431839819 10487430721418964647759729)
              ·
                refine ⟨7865573041064223485819797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10487430721418964647759729 7865573041064223485819797)
                ·
                  refine ⟨368698736299885475897803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7865573041064223485819797 368698736299885475897803)
                  ·
                    rfl

theorem cell23_6462344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 6].length) (baseStart_6462344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462344 prefixEnd_6462344 := by exact prefixLift 6462344
  have htrace : WordTrace (prefixWord ++ tailWord_6462344) baseStart_6462344 baseEnd_6462344 := by
    simpa [prefixWord, tailWord_6462344, baseEnd_6462344] using wordTrace_append hprefix tailTrace_6462344
  have hstable : (prefixWord ++ tailWord_6462344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462344).length < 2 ^ (prefixWord ++ tailWord_6462344).sum := by decide
  have hdescent : baseEnd_6462344 < baseStart_6462344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462377 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 2, 6, 2]
def baseStart_6462377 : Nat := 118140960795 + 6462377 * 2 ^ 59
def prefixEnd_6462377 : Nat := 4983230072969 + 3 ^ 40 * 6462377 * 2
def baseEnd_6462377 : Nat := 3318305571560567653967575

theorem tailTrace_6462377 : CollatzResearch.WordTrace tailWord_6462377 prefixEnd_6462377 3318305571560567653967575 := by
  unfold tailWord_6462377
  simp only [CollatzResearch.WordTrace]
  refine ⟨235702252908919289967769385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157134835272612859978512923 235702252908919289967769385)
  ·
    refine ⟨176776689681689467475827039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235702252908919289967769385 176776689681689467475827039)
    ·
      refine ⟨265165034522534201213740559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176776689681689467475827039 265165034522534201213740559)
      ·
        refine ⟨397747551783801301820610839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265165034522534201213740559 397747551783801301820610839)
        ·
          refine ⟨596621327675701952730916259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397747551783801301820610839 596621327675701952730916259)
          ·
            refine ⟨894931991513552929096374389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596621327675701952730916259 894931991513552929096374389)
            ·
              refine ⟨83899874204395587102785099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 894931991513552929096374389 83899874204395587102785099)
              ·
                refine ⟨125849811306593380654177649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83899874204395587102785099 125849811306593380654177649)
                ·
                  refine ⟨94387358479945035490633237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125849811306593380654177649 94387358479945035490633237)
                  ·
                    refine ⟨4424407428747423538623433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94387358479945035490633237 4424407428747423538623433)
                    ·
                      refine ⟨3318305571560567653967575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4424407428747423538623433 3318305571560567653967575)
                      ·
                        rfl

theorem cell23_6462377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 6, 2].length) (baseStart_6462377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462377 prefixEnd_6462377 := by exact prefixLift 6462377
  have htrace : WordTrace (prefixWord ++ tailWord_6462377) baseStart_6462377 baseEnd_6462377 := by
    simpa [prefixWord, tailWord_6462377, baseEnd_6462377] using wordTrace_append hprefix tailTrace_6462377
  have hstable : (prefixWord ++ tailWord_6462377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462377).length < 2 ^ (prefixWord ++ tailWord_6462377).sum := by decide
  have hdescent : baseEnd_6462377 < baseStart_6462377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462400 : List Nat := [2, 1, 1, 2, 3, 3, 11]
def baseStart_6462400 : Nat := 118140960795 + 6462400 * 2 ^ 59
def prefixEnd_6462400 : Nat := 4983230072969 + 3 ^ 40 * 6462400 * 2
def baseEnd_6462400 : Nat := 40966881254513840296049

theorem tailTrace_6462400 : CollatzResearch.WordTrace tailWord_6462400 prefixEnd_6462400 40966881254513840296049 := by
  unfold tailWord_6462400
  simp only [CollatzResearch.WordTrace]
  refine ⟨117851545893917982447928327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157135394525223976597237769 117851545893917982447928327)
  ·
    refine ⟨176777318840876973671892491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117851545893917982447928327 176777318840876973671892491)
    ·
      refine ⟨265165978261315460507838737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176777318840876973671892491 265165978261315460507838737)
      ·
        refine ⟨198874483695986595380879053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265165978261315460507838737 198874483695986595380879053)
        ·
          refine ⟨74577931385994973267829645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198874483695986595380879053 74577931385994973267829645)
          ·
            refine ⟨27966724269748114975436117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74577931385994973267829645 27966724269748114975436117)
            ·
              refine ⟨40966881254513840296049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27966724269748114975436117 40966881254513840296049)
              ·
                rfl

theorem cell23_6462400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 11].length) (baseStart_6462400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462400 prefixEnd_6462400 := by exact prefixLift 6462400
  have htrace : WordTrace (prefixWord ++ tailWord_6462400) baseStart_6462400 baseEnd_6462400 := by
    simpa [prefixWord, tailWord_6462400, baseEnd_6462400] using wordTrace_append hprefix tailTrace_6462400
  have hstable : (prefixWord ++ tailWord_6462400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462400).length < 2 ^ (prefixWord ++ tailWord_6462400).sum := by decide
  have hdescent : baseEnd_6462400 < baseStart_6462400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462411 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 3, 2, 2]
def baseStart_6462411 : Nat := 118140960795 + 6462411 * 2 ^ 59
def prefixEnd_6462411 : Nat := 4983230072969 + 3 ^ 40 * 6462411 * 2
def baseEnd_6462411 : Nat := 3318323029902820520942419

theorem tailTrace_6462411 : CollatzResearch.WordTrace tailWord_6462411 prefixEnd_6462411 3318323029902820520942419 := by
  unfold tailWord_6462411
  simp only [CollatzResearch.WordTrace]
  refine ⟨235703492990796113774507087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157135661993864075849671391 235703492990796113774507087)
  ·
    refine ⟨353555239486194170661760631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235703492990796113774507087 353555239486194170661760631)
    ·
      refine ⟨530332859229291255992640947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353555239486194170661760631 530332859229291255992640947)
      ·
        refine ⟨795499288843936883988961421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530332859229291255992640947 795499288843936883988961421)
        ·
          refine ⟨298312233316476331495860533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 795499288843936883988961421 298312233316476331495860533)
          ·
            refine ⟨27966771873419656077736925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 298312233316476331495860533 27966771873419656077736925)
            ·
              refine ⟨10487539452532371029151347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27966771873419656077736925 10487539452532371029151347)
              ·
                refine ⟨15731309178798556543727021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10487539452532371029151347 15731309178798556543727021)
                ·
                  refine ⟨5899240942049458703897633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15731309178798556543727021 5899240942049458703897633)
                  ·
                    refine ⟨4424430706537094027923225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5899240942049458703897633 4424430706537094027923225)
                    ·
                      refine ⟨3318323029902820520942419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4424430706537094027923225 3318323029902820520942419)
                      ·
                        rfl

theorem cell23_6462411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 2, 2].length) (baseStart_6462411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462411 prefixEnd_6462411 := by exact prefixLift 6462411
  have htrace : WordTrace (prefixWord ++ tailWord_6462411) baseStart_6462411 baseEnd_6462411 := by
    simpa [prefixWord, tailWord_6462411, baseEnd_6462411] using wordTrace_append hprefix tailTrace_6462411
  have hstable : (prefixWord ++ tailWord_6462411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462411).length < 2 ^ (prefixWord ++ tailWord_6462411).sum := by decide
  have hdescent : baseEnd_6462411 < baseStart_6462411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462421 : List Nat := [1, 3, 2, 3, 3, 1, 1, 3, 2, 4]
def baseStart_6462421 : Nat := 118140960795 + 6462421 * 2 ^ 59
def prefixEnd_6462421 : Nat := 4983230072969 + 3 ^ 40 * 6462421 * 2
def baseEnd_6462421 : Nat := 1106109388236455160605791

theorem tailTrace_6462421 : CollatzResearch.WordTrace tailWord_6462421 prefixEnd_6462421 1106109388236455160605791 := by
  unfold tailWord_6462421
  simp only [CollatzResearch.WordTrace]
  refine ⟨235703857720759885482371117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157135905147173256988247411 235703857720759885482371117)
  ·
    refine ⟨88388946645284957055889169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235703857720759885482371117 88388946645284957055889169)
    ·
      refine ⟨66291709983963717791916877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88388946645284957055889169 66291709983963717791916877)
      ·
        refine ⟨24859391243986394171968829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66291709983963717791916877 24859391243986394171968829)
        ·
          refine ⟨9322271716494897814488311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24859391243986394171968829 9322271716494897814488311)
          ·
            refine ⟨13983407574742346721732467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9322271716494897814488311 13983407574742346721732467)
            ·
              refine ⟨20975111362113520082598701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13983407574742346721732467 20975111362113520082598701)
              ·
                refine ⟨7865666760792570030974513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20975111362113520082598701 7865666760792570030974513)
                ·
                  refine ⟨5899250070594427523230885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7865666760792570030974513 5899250070594427523230885)
                  ·
                    refine ⟨1106109388236455160605791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5899250070594427523230885 1106109388236455160605791)
                    ·
                      rfl

theorem cell23_6462421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_6462421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462421 prefixEnd_6462421 := by exact prefixLift 6462421
  have htrace : WordTrace (prefixWord ++ tailWord_6462421) baseStart_6462421 baseEnd_6462421 := by
    simpa [prefixWord, tailWord_6462421, baseEnd_6462421] using wordTrace_append hprefix tailTrace_6462421
  have hstable : (prefixWord ++ tailWord_6462421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462421).length < 2 ^ (prefixWord ++ tailWord_6462421).sum := by decide
  have hdescent : baseEnd_6462421 < baseStart_6462421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462434 : List Nat := [3, 3, 3, 1, 1, 1, 2, 9]
def baseStart_6462434 : Nat := 118140960795 + 6462434 * 2 ^ 59
def prefixEnd_6462434 : Nat := 4983230072969 + 3 ^ 40 * 6462434 * 2
def baseEnd_6462434 : Nat := 122901290368810145590919

theorem tailTrace_6462434 : CollatzResearch.WordTrace tailWord_6462434 prefixEnd_6462434 122901290368810145590919 := by
  unfold tailWord_6462434
  simp only [CollatzResearch.WordTrace]
  refine ⟨58926082967428197175648589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157136221246475192468396237 58926082967428197175648589)
  ·
    refine ⟨22097281112785573940868221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58926082967428197175648589 22097281112785573940868221)
    ·
      refine ⟨8286480417294590227825583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22097281112785573940868221 8286480417294590227825583)
      ·
        refine ⟨12429720625941885341738375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8286480417294590227825583 12429720625941885341738375)
        ·
          refine ⟨18644580938912828012607563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12429720625941885341738375 18644580938912828012607563)
          ·
            refine ⟨27966871408369242018911345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18644580938912828012607563 27966871408369242018911345)
            ·
              refine ⟨20975153556276931514183509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27966871408369242018911345 20975153556276931514183509)
              ·
                refine ⟨122901290368810145590919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20975153556276931514183509 122901290368810145590919)
                ·
                  rfl

theorem cell23_6462434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 9].length) (baseStart_6462434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462434 prefixEnd_6462434 := by exact prefixLift 6462434
  have htrace : WordTrace (prefixWord ++ tailWord_6462434) baseStart_6462434 baseEnd_6462434 := by
    simpa [prefixWord, tailWord_6462434, baseEnd_6462434] using wordTrace_append hprefix tailTrace_6462434
  have hstable : (prefixWord ++ tailWord_6462434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462434).length < 2 ^ (prefixWord ++ tailWord_6462434).sum := by decide
  have hdescent : baseEnd_6462434 < baseStart_6462434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462462 : List Nat := [4, 2, 2, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_6462462 : Nat := 118140960795 + 6462462 * 2 ^ 59
def prefixEnd_6462462 : Nat := 4983230072969 + 3 ^ 40 * 6462462 * 2
def baseEnd_6462462 : Nat := 3318349217416199821404685

theorem tailTrace_6462462 : CollatzResearch.WordTrace tailWord_6462462 prefixEnd_6462462 3318349217416199821404685 := by
  unfold tailWord_6462462
  simp only [CollatzResearch.WordTrace]
  refine ⟨29463169139201418685576705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157136902075740899656409093 29463169139201418685576705)
  ·
    refine ⟨22097376854401064014182529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29463169139201418685576705 22097376854401064014182529)
    ·
      refine ⟨16573032640800798010636897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22097376854401064014182529 16573032640800798010636897)
      ·
        refine ⟨12429774480600598507977673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16573032640800798010636897 12429774480600598507977673)
        ·
          refine ⟨9322330860450448880983255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12429774480600598507977673 9322330860450448880983255)
          ·
            refine ⟨13983496290675673321474883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9322330860450448880983255 13983496290675673321474883)
            ·
              refine ⟨20975244436013509982212325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13983496290675673321474883 20975244436013509982212325)
              ·
                refine ⟨3932858331752533121664811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20975244436013509982212325 3932858331752533121664811)
                ·
                  refine ⟨5899287497628799682497217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3932858331752533121664811 5899287497628799682497217)
                  ·
                    refine ⟨4424465623221599761872913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5899287497628799682497217 4424465623221599761872913)
                    ·
                      refine ⟨3318349217416199821404685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4424465623221599761872913 3318349217416199821404685)
                      ·
                        rfl

theorem cell23_6462462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_6462462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462462 prefixEnd_6462462 := by exact prefixLift 6462462
  have htrace : WordTrace (prefixWord ++ tailWord_6462462) baseStart_6462462 baseEnd_6462462 := by
    simpa [prefixWord, tailWord_6462462, baseEnd_6462462] using wordTrace_append hprefix tailTrace_6462462
  have hstable : (prefixWord ++ tailWord_6462462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462462).length < 2 ^ (prefixWord ++ tailWord_6462462).sum := by decide
  have hdescent : baseEnd_6462462 < baseStart_6462462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462501 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 4, 2, 2]
def baseStart_6462501 : Nat := 118140960795 + 6462501 * 2 ^ 59
def prefixEnd_6462501 : Nat := 4983230072969 + 3 ^ 40 * 6462501 * 2
def baseEnd_6462501 : Nat := 3318369243161725168817005

theorem tailTrace_6462501 : CollatzResearch.WordTrace tailWord_6462501 prefixEnd_6462501 3318369243161725168817005 := by
  unfold tailWord_6462501
  simp only [CollatzResearch.WordTrace]
  refine ⟨235706775560470059145283357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157137850373646706096855571 235706775560470059145283357)
  ·
    refine ⟨88390040835176272179481259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235706775560470059145283357 88390040835176272179481259)
    ·
      refine ⟨132585061252764408269221889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88390040835176272179481259 132585061252764408269221889)
      ·
        refine ⟨99438795939573306201916417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132585061252764408269221889 99438795939573306201916417)
        ·
          refine ⟨74579096954679979651437313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99438795939573306201916417 74579096954679979651437313)
          ·
            refine ⟨55934322716009984738577985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74579096954679979651437313 55934322716009984738577985)
            ·
              refine ⟨41950742037007488553933489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55934322716009984738577985 41950742037007488553933489)
              ·
                refine ⟨31463056527755616415450117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41950742037007488553933489 31463056527755616415450117)
                ·
                  refine ⟨5899323098954178077896897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31463056527755616415450117 5899323098954178077896897)
                  ·
                    refine ⟨4424492324215633558422673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5899323098954178077896897 4424492324215633558422673)
                    ·
                      refine ⟨3318369243161725168817005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4424492324215633558422673 3318369243161725168817005)
                      ·
                        rfl

theorem cell23_6462501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_6462501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462501 prefixEnd_6462501 := by exact prefixLift 6462501
  have htrace : WordTrace (prefixWord ++ tailWord_6462501) baseStart_6462501 baseEnd_6462501 := by
    simpa [prefixWord, tailWord_6462501, baseEnd_6462501] using wordTrace_append hprefix tailTrace_6462501
  have hstable : (prefixWord ++ tailWord_6462501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462501).length < 2 ^ (prefixWord ++ tailWord_6462501).sum := by decide
  have hdescent : baseEnd_6462501 < baseStart_6462501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462524 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 7]
def baseStart_6462524 : Nat := 118140960795 + 6462524 * 2 ^ 59
def prefixEnd_6462524 : Nat := 4983230072969 + 3 ^ 40 * 6462524 * 2
def baseEnd_6462524 : Nat := 368709005912975397647711

theorem tailTrace_6462524 : CollatzResearch.WordTrace tailWord_6462524 prefixEnd_6462524 368709005912975397647711 := by
  unfold tailWord_6462524
  simp only [CollatzResearch.WordTrace]
  refine ⟨117853807219693367036685313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157138409626257822715580417 117853807219693367036685313)
  ·
    refine ⟨88390355414770025277513985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117853807219693367036685313 88390355414770025277513985)
    ·
      refine ⟨66292766561077518958135489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88390355414770025277513985 66292766561077518958135489)
      ·
        refine ⟨49719574920808139218601617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66292766561077518958135489 49719574920808139218601617)
        ·
          refine ⟨37289681190606104413951213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49719574920808139218601617 37289681190606104413951213)
          ·
            refine ⟨13983630446477289155231705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37289681190606104413951213 13983630446477289155231705)
            ·
              refine ⟨10487722834857966866423779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13983630446477289155231705 10487722834857966866423779)
              ·
                refine ⟨15731584252286950299635669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10487722834857966866423779 15731584252286950299635669)
                ·
                  refine ⟨368709005912975397647711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15731584252286950299635669 368709005912975397647711)
                  ·
                    rfl

theorem cell23_6462524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 7].length) (baseStart_6462524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462524 prefixEnd_6462524 := by exact prefixLift 6462524
  have htrace : WordTrace (prefixWord ++ tailWord_6462524) baseStart_6462524 baseEnd_6462524 := by
    simpa [prefixWord, tailWord_6462524, baseEnd_6462524] using wordTrace_append hprefix tailTrace_6462524
  have hstable : (prefixWord ++ tailWord_6462524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462524).length < 2 ^ (prefixWord ++ tailWord_6462524).sum := by decide
  have hdescent : baseEnd_6462524 < baseStart_6462524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462535 : List Nat := [1, 1, 4, 1, 3, 3, 3, 1, 2, 2, 2]
def baseStart_6462535 : Nat := 118140960795 + 6462535 * 2 ^ 59
def prefixEnd_6462535 : Nat := 4983230072969 + 3 ^ 40 * 6462535 * 2
def baseEnd_6462535 : Nat := 3318386701503978035791849

theorem tailTrace_6462535 : CollatzResearch.WordTrace tailWord_6462535 prefixEnd_6462535 3318386701503978035791849 := by
  unfold tailWord_6462535
  simp only [CollatzResearch.WordTrace]
  refine ⟨235708015642346882952021059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157138677094897921968014039 235708015642346882952021059)
  ·
    refine ⟨353562023463520324428031589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235708015642346882952021059 353562023463520324428031589)
    ·
      refine ⟨66292879399410060830255923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353562023463520324428031589 66292879399410060830255923)
      ·
        refine ⟨99439319099115091245383885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66292879399410060830255923 99439319099115091245383885)
        ·
          refine ⟨37289744662168159217018957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99439319099115091245383885 37289744662168159217018957)
          ·
            refine ⟨13983654248313059706382109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37289744662168159217018957 13983654248313059706382109)
            ·
              refine ⟨5243870343117397389893291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13983654248313059706382109 5243870343117397389893291)
              ·
                refine ⟨7865805514676096084839937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5243870343117397389893291 7865805514676096084839937)
                ·
                  refine ⟨5899354136007072063629953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7865805514676096084839937 5899354136007072063629953)
                  ·
                    refine ⟨4424515602005304047722465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5899354136007072063629953 4424515602005304047722465)
                    ·
                      refine ⟨3318386701503978035791849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4424515602005304047722465 3318386701503978035791849)
                      ·
                        rfl

theorem cell23_6462535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_6462535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462535 prefixEnd_6462535 := by exact prefixLift 6462535
  have htrace : WordTrace (prefixWord ++ tailWord_6462535) baseStart_6462535 baseEnd_6462535 := by
    simpa [prefixWord, tailWord_6462535, baseEnd_6462535] using wordTrace_append hprefix tailTrace_6462535
  have hstable : (prefixWord ++ tailWord_6462535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462535).length < 2 ^ (prefixWord ++ tailWord_6462535).sum := by decide
  have hdescent : baseEnd_6462535 < baseStart_6462535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462537 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 6, 5]
def baseStart_6462537 : Nat := 118140960795 + 6462537 * 2 ^ 59
def prefixEnd_6462537 : Nat := 4983230072969 + 3 ^ 40 * 6462537 * 2
def baseEnd_6462537 : Nat := 1106129242821762342655613

theorem tailTrace_6462537 : CollatzResearch.WordTrace tailWord_6462537 prefixEnd_6462537 1106129242821762342655613 := by
  unfold tailWord_6462537
  simp only [CollatzResearch.WordTrace]
  refine ⟨235708088588339637293593865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157138725725559758195729243 235708088588339637293593865)
  ·
    refine ⟨176781066441254727970195399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235708088588339637293593865 176781066441254727970195399)
    ·
      refine ⟨265171599661882091955293099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176781066441254727970195399 265171599661882091955293099)
      ·
        refine ⟨397757399492823137932939649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265171599661882091955293099 397757399492823137932939649)
        ·
          refine ⟨298318049619617353449704737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397757399492823137932939649 298318049619617353449704737)
          ·
            refine ⟨223738537214713015087278553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298318049619617353449704737 223738537214713015087278553)
            ·
              refine ⟨167803902911034761315458915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223738537214713015087278553 167803902911034761315458915)
              ·
                refine ⟨251705854366552141973188373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167803902911034761315458915 251705854366552141973188373)
                ·
                  refine ⟨11798711923432131654993205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 251705854366552141973188373 11798711923432131654993205)
                  ·
                    refine ⟨1106129242821762342655613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11798711923432131654993205 1106129242821762342655613)
                    ·
                      rfl

theorem cell23_6462537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 5].length) (baseStart_6462537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462537 prefixEnd_6462537 := by exact prefixLift 6462537
  have htrace : WordTrace (prefixWord ++ tailWord_6462537) baseStart_6462537 baseEnd_6462537 := by
    simpa [prefixWord, tailWord_6462537, baseEnd_6462537] using wordTrace_append hprefix tailTrace_6462537
  have hstable : (prefixWord ++ tailWord_6462537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462537).length < 2 ^ (prefixWord ++ tailWord_6462537).sum := by decide
  have hdescent : baseEnd_6462537 < baseStart_6462537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462544 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 2, 5, 2]
def baseStart_6462544 : Nat := 118140960795 + 6462544 * 2 ^ 59
def prefixEnd_6462544 : Nat := 4983230072969 + 3 ^ 40 * 6462544 * 2
def baseEnd_6462544 : Nat := 3318391322829868500579307

theorem tailTrace_6462544 : CollatzResearch.WordTrace tailWord_6462544 prefixEnd_6462544 3318391322829868500579307 := by
  unfold tailWord_6462544
  simp only [CollatzResearch.WordTrace]
  refine ⟨117854171949657138744549343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157138895932876184992732457 117854171949657138744549343)
  ·
    refine ⟨176781257924485708116824015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117854171949657138744549343 176781257924485708116824015)
    ·
      refine ⟨265171886886728562175236023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176781257924485708116824015 265171886886728562175236023)
      ·
        refine ⟨397757830330092843262854035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265171886886728562175236023 397757830330092843262854035)
        ·
          refine ⟨596636745495139264894281053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397757830330092843262854035 596636745495139264894281053)
          ·
            refine ⟨223738779560677224335355395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 596636745495139264894281053 223738779560677224335355395)
            ·
              refine ⟨335608169341015836503033093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223738779560677224335355395 335608169341015836503033093)
              ·
                refine ⟨62926531751440469344318705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335608169341015836503033093 62926531751440469344318705)
                ·
                  refine ⟨47194898813580352008239029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62926531751440469344318705 47194898813580352008239029)
                  ·
                    refine ⟨4424521763773158000772409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47194898813580352008239029 4424521763773158000772409)
                    ·
                      refine ⟨3318391322829868500579307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4424521763773158000772409 3318391322829868500579307)
                      ·
                        rfl

theorem cell23_6462544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 5, 2].length) (baseStart_6462544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462544 prefixEnd_6462544 := by exact prefixLift 6462544
  have htrace : WordTrace (prefixWord ++ tailWord_6462544) baseStart_6462544 baseEnd_6462544 := by
    simpa [prefixWord, tailWord_6462544, baseEnd_6462544] using wordTrace_append hprefix tailTrace_6462544
  have hstable : (prefixWord ++ tailWord_6462544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462544).length < 2 ^ (prefixWord ++ tailWord_6462544).sum := by decide
  have hdescent : baseEnd_6462544 < baseStart_6462544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462577 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_6462577 : Nat := 118140960795 + 6462577 * 2 ^ 59
def prefixEnd_6462577 : Nat := 4983230072969 + 3 ^ 40 * 6462577 * 2
def baseEnd_6462577 : Nat := 3318408267691466871466655

theorem tailTrace_6462577 : CollatzResearch.WordTrace tailWord_6462577 prefixEnd_6462577 3318408267691466871466655 := by
  unfold tailWord_6462577
  simp only [CollatzResearch.WordTrace]
  refine ⟨235709547508194724125049985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157139698338796482750033323 235709547508194724125049985)
  ·
    refine ⟨176782160631146043093787489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235709547508194724125049985 176782160631146043093787489)
    ·
      refine ⟨132586620473359532320340617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176782160631146043093787489 132586620473359532320340617)
      ·
        refine ⟨99439965355019649240255463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132586620473359532320340617 99439965355019649240255463)
        ·
          refine ⟨149159948032529473860383195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99439965355019649240255463 149159948032529473860383195)
          ·
            refine ⟨223739922048794210790574793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149159948032529473860383195 223739922048794210790574793)
            ·
              refine ⟨167804941536595658092931095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223739922048794210790574793 167804941536595658092931095)
              ·
                refine ⟨251707412304893487139396643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167804941536595658092931095 251707412304893487139396643)
                ·
                  refine ⟨377561118457340230709094965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251707412304893487139396643 377561118457340230709094965)
                  ·
                    refine ⟨35396354855375646628977653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 377561118457340230709094965 35396354855375646628977653)
                    ·
                      refine ⟨3318408267691466871466655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35396354855375646628977653 3318408267691466871466655)
                      ·
                        rfl

theorem cell23_6462577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_6462577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462577 prefixEnd_6462577 := by exact prefixLift 6462577
  have htrace : WordTrace (prefixWord ++ tailWord_6462577) baseStart_6462577 baseEnd_6462577 := by
    simpa [prefixWord, tailWord_6462577, baseEnd_6462577] using wordTrace_append hprefix tailTrace_6462577
  have hstable : (prefixWord ++ tailWord_6462577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462577).length < 2 ^ (prefixWord ++ tailWord_6462577).sum := by decide
  have hdescent : baseEnd_6462577 < baseStart_6462577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462587 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 6]
def baseStart_6462587 : Nat := 118140960795 + 6462587 * 2 ^ 59
def prefixEnd_6462587 : Nat := 4983230072969 + 3 ^ 40 * 6462587 * 2
def baseEnd_6462587 : Nat := 3318413402498011832341609

theorem tailTrace_6462587 : CollatzResearch.WordTrace tailWord_6462587 prefixEnd_6462587 3318413402498011832341609 := by
  unfold tailWord_6462587
  simp only [CollatzResearch.WordTrace]
  refine ⟨235709912238158495832914015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157139941492105663888609343 235709912238158495832914015)
  ·
    refine ⟨353564868357237743749371023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235709912238158495832914015 353564868357237743749371023)
    ·
      refine ⟨530347302535856615624056535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353564868357237743749371023 530347302535856615624056535)
      ·
        refine ⟨795520953803784923436084803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530347302535856615624056535 795520953803784923436084803)
        ·
          refine ⟨1193281430705677385154127205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795520953803784923436084803 1193281430705677385154127205)
          ·
            refine ⟨223740268257314509716398851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1193281430705677385154127205 223740268257314509716398851)
            ·
              refine ⟨335610402385971764574598277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223740268257314509716398851 335610402385971764574598277)
              ·
                refine ⟨62926950447369705857737177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335610402385971764574598277 62926950447369705857737177)
                ·
                  refine ⟨47195212835527279393302883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62926950447369705857737177 47195212835527279393302883)
                  ·
                    refine ⟨70792819253290919089954325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47195212835527279393302883 70792819253290919089954325)
                    ·
                      refine ⟨3318413402498011832341609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70792819253290919089954325 3318413402498011832341609)
                      ·
                        rfl

theorem cell23_6462587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 6].length) (baseStart_6462587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462587 prefixEnd_6462587 := by exact prefixLift 6462587
  have htrace : WordTrace (prefixWord ++ tailWord_6462587) baseStart_6462587 baseEnd_6462587 := by
    simpa [prefixWord, tailWord_6462587, baseEnd_6462587] using wordTrace_append hprefix tailTrace_6462587
  have hstable : (prefixWord ++ tailWord_6462587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462587).length < 2 ^ (prefixWord ++ tailWord_6462587).sum := by decide
  have hdescent : baseEnd_6462587 < baseStart_6462587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462617 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 8]
def baseStart_6462617 : Nat := 118140960795 + 6462617 * 2 ^ 59
def prefixEnd_6462617 : Nat := 4983230072969 + 3 ^ 40 * 6462617 * 2
def baseEnd_6462617 : Nat := 3318428806917646714966471

theorem tailTrace_6462617 : CollatzResearch.WordTrace tailWord_6462617 prefixEnd_6462617 3318428806917646714966471 := by
  unfold tailWord_6462617
  simp only [CollatzResearch.WordTrace]
  refine ⟨235711006428049810956506105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157140670952033207304337403 235711006428049810956506105)
  ·
    refine ⟨176783254821037358217379579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235711006428049810956506105 176783254821037358217379579)
    ·
      refine ⟨265174882231556037326069369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176783254821037358217379579 265174882231556037326069369)
      ·
        refine ⟨198881161673667027994552027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265174882231556037326069369 198881161673667027994552027)
        ·
          refine ⟨298321742510500541991828041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198881161673667027994552027 298321742510500541991828041)
          ·
            refine ⟨223741306882875406493871031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298321742510500541991828041 223741306882875406493871031)
            ·
              refine ⟨335611960324313109740806547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223741306882875406493871031 335611960324313109740806547)
              ·
                refine ⟨503417940486469664611209821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335611960324313109740806547 503417940486469664611209821)
                ·
                  refine ⟨188781727682426124229203683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503417940486469664611209821 188781727682426124229203683)
                  ·
                    refine ⟨283172591523639186343805525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188781727682426124229203683 283172591523639186343805525)
                    ·
                      refine ⟨3318428806917646714966471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 283172591523639186343805525 3318428806917646714966471)
                      ·
                        rfl

theorem cell23_6462617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_6462617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462617 prefixEnd_6462617 := by exact prefixLift 6462617
  have htrace : WordTrace (prefixWord ++ tailWord_6462617) baseStart_6462617 baseEnd_6462617 := by
    simpa [prefixWord, tailWord_6462617, baseEnd_6462617] using wordTrace_append hprefix tailTrace_6462617
  have hstable : (prefixWord ++ tailWord_6462617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462617).length < 2 ^ (prefixWord ++ tailWord_6462617).sum := by decide
  have hdescent : baseEnd_6462617 < baseStart_6462617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462631 : List Nat := [1, 1, 6, 2, 1, 1, 1, 4, 6]
def baseStart_6462631 : Nat := 118140960795 + 6462631 * 2 ^ 59
def prefixEnd_6462631 : Nat := 4983230072969 + 3 ^ 40 * 6462631 * 2
def baseEnd_6462631 : Nat := 368715110627423295576823

theorem tailTrace_6462631 : CollatzResearch.WordTrace tailWord_6462631 prefixEnd_6462631 368715110627423295576823 := by
  unfold tailWord_6462631
  simp only [CollatzResearch.WordTrace]
  refine ⟨235711517049999091347515747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157141011366666060898343831 235711517049999091347515747)
  ·
    refine ⟨353567275574998637021273621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235711517049999091347515747 353567275574998637021273621)
    ·
      refine ⟨16573466042578061110372201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 353567275574998637021273621 16573466042578061110372201)
      ·
        refine ⟨12430099531933545832779151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16573466042578061110372201 12430099531933545832779151)
        ·
          refine ⟨18645149297900318749168727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12430099531933545832779151 18645149297900318749168727)
          ·
            refine ⟨27967723946850478123753091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18645149297900318749168727 27967723946850478123753091)
            ·
              refine ⟨41951585920275717185629637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27967723946850478123753091 41951585920275717185629637)
              ·
                refine ⟨7865922360051696972305557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41951585920275717185629637 7865922360051696972305557)
                ·
                  refine ⟨368715110627423295576823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7865922360051696972305557 368715110627423295576823)
                  ·
                    rfl

theorem cell23_6462631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 6].length) (baseStart_6462631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462631 prefixEnd_6462631 := by exact prefixLift 6462631
  have htrace : WordTrace (prefixWord ++ tailWord_6462631) baseStart_6462631 baseEnd_6462631 := by
    simpa [prefixWord, tailWord_6462631, baseEnd_6462631] using wordTrace_append hprefix tailTrace_6462631
  have hstable : (prefixWord ++ tailWord_6462631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462631).length < 2 ^ (prefixWord ++ tailWord_6462631).sum := by decide
  have hdescent : baseEnd_6462631 < baseStart_6462631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462662 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_6462662 : Nat := 118140960795 + 6462662 * 2 ^ 59
def prefixEnd_6462662 : Nat := 4983230072969 + 3 ^ 40 * 6462662 * 2
def baseEnd_6462662 : Nat := 3318451913547099038903765

theorem tailTrace_6462662 : CollatzResearch.WordTrace tailWord_6462662 prefixEnd_6462662 3318451913547099038903765 := by
  unfold tailWord_6462662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7366020241027711988809195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157141765141924522427929493 7366020241027711988809195)
  ·
    refine ⟨11049030361541567983213793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7366020241027711988809195 11049030361541567983213793)
    ·
      refine ⟨8286772771156175987410345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11049030361541567983213793 8286772771156175987410345)
      ·
        refine ⟨6215079578367131990557759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8286772771156175987410345 6215079578367131990557759)
        ·
          refine ⟨9322619367550697985836639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215079578367131990557759 9322619367550697985836639)
          ·
            refine ⟨13983929051326046978754959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9322619367550697985836639 13983929051326046978754959)
            ·
              refine ⟨20975893576989070468132439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13983929051326046978754959 20975893576989070468132439)
              ·
                refine ⟨31463840365483605702198659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20975893576989070468132439 31463840365483605702198659)
                ·
                  refine ⟨47195760548225408553297989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31463840365483605702198659 47195760548225408553297989)
                  ·
                    refine ⟨8849205102792264103743373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47195760548225408553297989 8849205102792264103743373)
                    ·
                      refine ⟨3318451913547099038903765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8849205102792264103743373 3318451913547099038903765)
                      ·
                        rfl

theorem cell23_6462662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_6462662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462662 prefixEnd_6462662 := by exact prefixLift 6462662
  have htrace : WordTrace (prefixWord ++ tailWord_6462662) baseStart_6462662 baseEnd_6462662 := by
    simpa [prefixWord, tailWord_6462662, baseEnd_6462662] using wordTrace_append hprefix tailTrace_6462662
  have hstable : (prefixWord ++ tailWord_6462662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462662).length < 2 ^ (prefixWord ++ tailWord_6462662).sum := by decide
  have hdescent : baseEnd_6462662 < baseStart_6462662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462669 : List Nat := [1, 6, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_6462669 : Nat := 118140960795 + 6462669 * 2 ^ 59
def prefixEnd_6462669 : Nat := 4983230072969 + 3 ^ 40 * 6462669 * 2
def baseEnd_6462669 : Nat := 1106151835970560170505411

theorem tailTrace_6462669 : CollatzResearch.WordTrace tailWord_6462669 prefixEnd_6462669 1106151835970560170505411 := by
  unfold tailWord_6462669
  simp only [CollatzResearch.WordTrace]
  refine ⟨235712903023861423837399061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157141935349240949224932707 235712903023861423837399061)
  ·
    refine ⟨11049042329243504242378081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 235712903023861423837399061 11049042329243504242378081)
    ·
      refine ⟨8286781746932628181783561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11049042329243504242378081 8286781746932628181783561)
      ·
        refine ⟨6215086310199471136337671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8286781746932628181783561 6215086310199471136337671)
        ·
          refine ⟨9322629465299206704506507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215086310199471136337671 9322629465299206704506507)
          ·
            refine ⟨13983944197948810056759761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9322629465299206704506507 13983944197948810056759761)
            ·
              refine ⟨10487958148461607542569821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13983944197948810056759761 10487958148461607542569821)
              ·
                refine ⟨3932984305673102828463683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10487958148461607542569821 3932984305673102828463683)
                ·
                  refine ⟨5899476458509654242695525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3932984305673102828463683 5899476458509654242695525)
                  ·
                    refine ⟨1106151835970560170505411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5899476458509654242695525 1106151835970560170505411)
                    ·
                      rfl

theorem cell23_6462669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_6462669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462669 prefixEnd_6462669 := by exact prefixLift 6462669
  have htrace : WordTrace (prefixWord ++ tailWord_6462669) baseStart_6462669 baseEnd_6462669 := by
    simpa [prefixWord, tailWord_6462669, baseEnd_6462669] using wordTrace_append hprefix tailTrace_6462669
  have hstable : (prefixWord ++ tailWord_6462669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462669).length < 2 ^ (prefixWord ++ tailWord_6462669).sum := by decide
  have hdescent : baseEnd_6462669 < baseStart_6462669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462701 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_6462701 : Nat := 118140960795 + 6462701 * 2 ^ 59
def prefixEnd_6462701 : Nat := 4983230072969 + 3 ^ 40 * 6462701 * 2
def baseEnd_6462701 : Nat := 3318471939292624386316085

theorem tailTrace_6462701 : CollatzResearch.WordTrace tailWord_6462701 prefixEnd_6462701 3318471939292624386316085 := by
  unfold tailWord_6462701
  simp only [CollatzResearch.WordTrace]
  refine ⟨235714070159745493302563957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157142713439830328868375971 235714070159745493302563957)
  ·
    refine ⟨22098194077476139997115371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235714070159745493302563957 22098194077476139997115371)
    ·
      refine ⟨33147291116214209995673057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22098194077476139997115371 33147291116214209995673057)
      ·
        refine ⟨24860468337160657496754793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33147291116214209995673057 24860468337160657496754793)
        ·
          refine ⟨18645351252870493122566095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24860468337160657496754793 18645351252870493122566095)
          ·
            refine ⟨27968026879305739683849143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18645351252870493122566095 27968026879305739683849143)
            ·
              refine ⟨41952040318958609525773715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27968026879305739683849143 41952040318958609525773715)
              ·
                refine ⟨62928060478437914288660573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41952040318958609525773715 62928060478437914288660573)
                ·
                  refine ⟨23598022679414217858247715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62928060478437914288660573 23598022679414217858247715)
                  ·
                    refine ⟨35397034019121326787371573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23598022679414217858247715 35397034019121326787371573)
                    ·
                      refine ⟨3318471939292624386316085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35397034019121326787371573 3318471939292624386316085)
                      ·
                        rfl

theorem cell23_6462701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_6462701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462701 prefixEnd_6462701 := by exact prefixLift 6462701
  have htrace : WordTrace (prefixWord ++ tailWord_6462701) baseStart_6462701 baseEnd_6462701 := by
    simpa [prefixWord, tailWord_6462701, baseEnd_6462701] using wordTrace_append hprefix tailTrace_6462701
  have hstable : (prefixWord ++ tailWord_6462701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462701).length < 2 ^ (prefixWord ++ tailWord_6462701).sum := by decide
  have hdescent : baseEnd_6462701 < baseStart_6462701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462721 : List Nat := [1, 2, 4, 1, 1, 3, 4, 7]
def baseStart_6462721 : Nat := 118140960795 + 6462721 * 2 ^ 59
def prefixEnd_6462721 : Nat := 4983230072969 + 3 ^ 40 * 6462721 * 2
def baseEnd_6462721 : Nat := 122906748477989418817259

theorem tailTrace_6462721 : CollatzResearch.WordTrace tailWord_6462721 prefixEnd_6462721 122906748477989418817259 := by
  unfold tailWord_6462721
  simp only [CollatzResearch.WordTrace]
  refine ⟨235714799619673036718292017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157143199746448691145528011 235714799619673036718292017)
  ·
    refine ⟨176786099714754777538719013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235714799619673036718292017 176786099714754777538719013)
    ·
      refine ⟨33147393696516520788509815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176786099714754777538719013 33147393696516520788509815)
      ·
        refine ⟨49721090544774781182764723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33147393696516520788509815 49721090544774781182764723)
        ·
          refine ⟨74581635817162171774147085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49721090544774781182764723 74581635817162171774147085)
          ·
            refine ⟨27968113431435814415305157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74581635817162171774147085 27968113431435814415305157)
            ·
              refine ⟨5244021268394215202869717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27968113431435814415305157 5244021268394215202869717)
              ·
                refine ⟨122906748477989418817259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5244021268394215202869717 122906748477989418817259)
                ·
                  rfl

theorem cell23_6462721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 7].length) (baseStart_6462721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462721 prefixEnd_6462721 := by exact prefixLift 6462721
  have htrace : WordTrace (prefixWord ++ tailWord_6462721) baseStart_6462721 baseEnd_6462721 := by
    simpa [prefixWord, tailWord_6462721, baseEnd_6462721] using wordTrace_append hprefix tailTrace_6462721
  have hstable : (prefixWord ++ tailWord_6462721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462721).length < 2 ^ (prefixWord ++ tailWord_6462721).sum := by decide
  have hdescent : baseEnd_6462721 < baseStart_6462721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462732 : List Nat := [2, 2, 1, 2, 2, 3, 3, 3, 1, 2, 2]
def baseStart_6462732 : Nat := 118140960795 + 6462732 * 2 ^ 59
def prefixEnd_6462732 : Nat := 4983230072969 + 3 ^ 40 * 6462732 * 2
def baseEnd_6462732 : Nat := 3318487857192913765028443

theorem tailTrace_6462732 : CollatzResearch.WordTrace tailWord_6462732 prefixEnd_6462732 3318487857192913765028443 := by
  unfold tailWord_6462732
  simp only [CollatzResearch.WordTrace]
  refine ⟨117857600411316592798471225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157143467215088790397961633 117857600411316592798471225)
  ·
    refine ⟨88393200308487444598853419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117857600411316592798471225 88393200308487444598853419)
    ·
      refine ⟨132589800462731166898280129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88393200308487444598853419 132589800462731166898280129)
      ·
        refine ⟨99442350347048375173710097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132589800462731166898280129 99442350347048375173710097)
        ·
          refine ⟨74581762760286281380282573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99442350347048375173710097 74581762760286281380282573)
          ·
            refine ⟨27968161035107355517605965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74581762760286281380282573 27968161035107355517605965)
            ·
              refine ⟨10488060388165258319102237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27968161035107355517605965 10488060388165258319102237)
              ·
                refine ⟨3933022645561971869663339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10488060388165258319102237 3933022645561971869663339)
                ·
                  refine ⟨5899533968342957804495009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3933022645561971869663339 5899533968342957804495009)
                  ·
                    refine ⟨4424650476257218353371257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5899533968342957804495009 4424650476257218353371257)
                    ·
                      refine ⟨3318487857192913765028443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4424650476257218353371257 3318487857192913765028443)
                      ·
                        rfl

theorem cell23_6462732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_6462732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462732 prefixEnd_6462732 := by exact prefixLift 6462732
  have htrace : WordTrace (prefixWord ++ tailWord_6462732) baseStart_6462732 baseEnd_6462732 := by
    simpa [prefixWord, tailWord_6462732, baseEnd_6462732] using wordTrace_append hprefix tailTrace_6462732
  have hstable : (prefixWord ++ tailWord_6462732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462732).length < 2 ^ (prefixWord ++ tailWord_6462732).sum := by decide
  have hdescent : baseEnd_6462732 < baseStart_6462732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462748 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_6462748 : Nat := 118140960795 + 6462748 * 2 ^ 59
def prefixEnd_6462748 : Nat := 4983230072969 + 3 ^ 40 * 6462748 * 2
def baseEnd_6462748 : Nat := 3318496072883385702428369

theorem tailTrace_6462748 : CollatzResearch.WordTrace tailWord_6462748 prefixEnd_6462748 3318496072883385702428369 := by
  unfold tailWord_6462748
  simp only [CollatzResearch.WordTrace]
  refine ⟨117857892195287610164762449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157143856260383480219683265 117857892195287610164762449)
  ·
    refine ⟨88393419146465707623571837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117857892195287610164762449 88393419146465707623571837)
    ·
      refine ⟨33147532179924640358839439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88393419146465707623571837 33147532179924640358839439)
      ·
        refine ⟨49721298269886960538259159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33147532179924640358839439 49721298269886960538259159)
        ·
          refine ⟨74581947404830440807388739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49721298269886960538259159 74581947404830440807388739)
          ·
            refine ⟨111872921107245661211083109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74581947404830440807388739 111872921107245661211083109)
            ·
              refine ⟨20976172707608561477078083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111872921107245661211083109 20976172707608561477078083)
              ·
                refine ⟨31464259061412842215617125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20976172707608561477078083 31464259061412842215617125)
                ·
                  refine ⟨5899548574014907915428211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31464259061412842215617125 5899548574014907915428211)
                  ·
                    refine ⟨8849322861022361873142317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5899548574014907915428211 8849322861022361873142317)
                    ·
                      refine ⟨3318496072883385702428369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8849322861022361873142317 3318496072883385702428369)
                      ·
                        rfl

theorem cell23_6462748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_6462748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462748 prefixEnd_6462748 := by exact prefixLift 6462748
  have htrace : WordTrace (prefixWord ++ tailWord_6462748) baseStart_6462748 baseEnd_6462748 := by
    simpa [prefixWord, tailWord_6462748, baseEnd_6462748] using wordTrace_append hprefix tailTrace_6462748
  have hstable : (prefixWord ++ tailWord_6462748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462748).length < 2 ^ (prefixWord ++ tailWord_6462748).sum := by decide
  have hdescent : baseEnd_6462748 < baseStart_6462748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462764 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 1, 8]
def baseStart_6462764 : Nat := 118140960795 + 6462764 * 2 ^ 59
def prefixEnd_6462764 : Nat := 4983230072969 + 3 ^ 40 * 6462764 * 2
def baseEnd_6462764 : Nat := 1106168096191285879942765

theorem tailTrace_6462764 : CollatzResearch.WordTrace tailWord_6462764 prefixEnd_6462764 1106168096191285879942765 := by
  unfold tailWord_6462764
  simp only [CollatzResearch.WordTrace]
  refine ⟨117858183979258627531053673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157144245305678170041404897 117858183979258627531053673)
  ·
    refine ⟨88393637984443970648290255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117858183979258627531053673 88393637984443970648290255)
    ·
      refine ⟨132590456976665955972435383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88393637984443970648290255 132590456976665955972435383)
      ·
        refine ⟨198885685464998933958653075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132590456976665955972435383 198885685464998933958653075)
        ·
          refine ⟨298328528197498400937979613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198885685464998933958653075 298328528197498400937979613)
          ·
            refine ⟨111873198074061900351742355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298328528197498400937979613 111873198074061900351742355)
            ·
              refine ⟨167809797111092850527613533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111873198074061900351742355 167809797111092850527613533)
              ·
                refine ⟨62928673916659818947855075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167809797111092850527613533 62928673916659818947855075)
                ·
                  refine ⟨94393010874989728421782613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62928673916659818947855075 94393010874989728421782613)
                  ·
                    refine ⟨1106168096191285879942765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94393010874989728421782613 1106168096191285879942765)
                    ·
                      rfl

theorem cell23_6462764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_6462764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462764 prefixEnd_6462764 := by exact prefixLift 6462764
  have htrace : WordTrace (prefixWord ++ tailWord_6462764) baseStart_6462764 baseEnd_6462764 := by
    simpa [prefixWord, tailWord_6462764, baseEnd_6462764] using wordTrace_append hprefix tailTrace_6462764
  have hstable : (prefixWord ++ tailWord_6462764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462764).length < 2 ^ (prefixWord ++ tailWord_6462764).sum := by decide
  have hdescent : baseEnd_6462764 < baseStart_6462764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462791 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_6462791 : Nat := 118140960795 + 6462791 * 2 ^ 59
def prefixEnd_6462791 : Nat := 4983230072969 + 3 ^ 40 * 6462791 * 2
def baseEnd_6462791 : Nat := 3318518152551529034190671

theorem tailTrace_6462791 : CollatzResearch.WordTrace tailWord_6462791 prefixEnd_6462791 3318518152551529034190671 := by
  unfold tailWord_6462791
  simp only [CollatzResearch.WordTrace]
  refine ⟨235717352729419438673340227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157144901819612959115560151 235717352729419438673340227)
  ·
    refine ⟨353576029094129158010010341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235717352729419438673340227 353576029094129158010010341)
    ·
      refine ⟨66295505455149217126876939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353576029094129158010010341 66295505455149217126876939)
      ·
        refine ⟨99443258182723825690315409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66295505455149217126876939 99443258182723825690315409)
        ·
          refine ⟨74582443637042869267736557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99443258182723825690315409 74582443637042869267736557)
          ·
            refine ⟨27968416363891075975401209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74582443637042869267736557 27968416363891075975401209)
            ·
              refine ⟨20976312272918306981550907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27968416363891075975401209 20976312272918306981550907)
              ·
                refine ⟨31464468409377460472326361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20976312272918306981550907 31464468409377460472326361)
                ·
                  refine ⟨23598351307033095354244771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31464468409377460472326361 23598351307033095354244771)
                  ·
                    refine ⟨35397526960549643031367157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23598351307033095354244771 35397526960549643031367157)
                    ·
                      refine ⟨3318518152551529034190671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35397526960549643031367157 3318518152551529034190671)
                      ·
                        rfl

theorem cell23_6462791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_6462791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462791 prefixEnd_6462791 := by exact prefixLift 6462791
  have htrace : WordTrace (prefixWord ++ tailWord_6462791) baseStart_6462791 baseEnd_6462791 := by
    simpa [prefixWord, tailWord_6462791, baseEnd_6462791] using wordTrace_append hprefix tailTrace_6462791
  have hstable : (prefixWord ++ tailWord_6462791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462791).length < 2 ^ (prefixWord ++ tailWord_6462791).sum := by decide
  have hdescent : baseEnd_6462791 < baseStart_6462791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462801 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_6462801 : Nat := 118140960795 + 6462801 * 2 ^ 59
def prefixEnd_6462801 : Nat := 4983230072969 + 3 ^ 40 * 6462801 * 2
def baseEnd_6462801 : Nat := 3318523287358073995065625

theorem tailTrace_6462801 : CollatzResearch.WordTrace tailWord_6462801 prefixEnd_6462801 3318523287358073995065625 := by
  unfold tailWord_6462801
  simp only [CollatzResearch.WordTrace]
  refine ⟨235717717459383210381204257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157145144972922140254136171 235717717459383210381204257)
  ·
    refine ⟨176788288094537407785903193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235717717459383210381204257 176788288094537407785903193)
    ·
      refine ⟨132591216070903055839427395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176788288094537407785903193 132591216070903055839427395)
      ·
        refine ⟨198886824106354583759141093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132591216070903055839427395 198886824106354583759141093)
        ·
          refine ⟨37291279519941484454838955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198886824106354583759141093 37291279519941484454838955)
          ·
            refine ⟨55936919279912226682258433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37291279519941484454838955 55936919279912226682258433)
            ·
              refine ⟨41952689459934170011693825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55936919279912226682258433 41952689459934170011693825)
              ·
                refine ⟨31464517094950627508770369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41952689459934170011693825 31464517094950627508770369)
                ·
                  refine ⟨23598387821212970631577777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31464517094950627508770369 23598387821212970631577777)
                  ·
                    refine ⟨17698790865909727973683333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23598387821212970631577777 17698790865909727973683333)
                    ·
                      refine ⟨3318523287358073995065625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17698790865909727973683333 3318523287358073995065625)
                      ·
                        rfl

theorem cell23_6462801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_6462801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462801 prefixEnd_6462801 := by exact prefixLift 6462801
  have htrace : WordTrace (prefixWord ++ tailWord_6462801) baseStart_6462801 baseEnd_6462801 := by
    simpa [prefixWord, tailWord_6462801, baseEnd_6462801] using wordTrace_append hprefix tailTrace_6462801
  have hstable : (prefixWord ++ tailWord_6462801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462801).length < 2 ^ (prefixWord ++ tailWord_6462801).sum := by decide
  have hdescent : baseEnd_6462801 < baseStart_6462801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462818 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_6462818 : Nat := 118140960795 + 6462818 * 2 ^ 59
def prefixEnd_6462818 : Nat := 4983230072969 + 3 ^ 40 * 6462818 * 2
def baseEnd_6462818 : Nat := 3318532016529200428553047

theorem tailTrace_6462818 : CollatzResearch.WordTrace tailWord_6462818 prefixEnd_6462818 3318532016529200428553047 := by
  unfold tailWord_6462818
  simp only [CollatzResearch.WordTrace]
  refine ⟨58929584375080405571143277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157145558333547748189715405 58929584375080405571143277)
  ·
    refine ⟨22098594140655152089178729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58929584375080405571143277 22098594140655152089178729)
    ·
      refine ⟨16573945605491364066884047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22098594140655152089178729 16573945605491364066884047)
      ·
        refine ⟨24860918408237046100326071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16573945605491364066884047 24860918408237046100326071)
        ·
          refine ⟨37291377612355569150489107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24860918408237046100326071 37291377612355569150489107)
          ·
            refine ⟨55937066418533353725733661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37291377612355569150489107 55937066418533353725733661)
            ·
              refine ⟨20976399906950007647150123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55937066418533353725733661 20976399906950007647150123)
              ·
                refine ⟨31464599860425011470725185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20976399906950007647150123 31464599860425011470725185)
                ·
                  refine ⟨23598449895318758603043889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31464599860425011470725185 23598449895318758603043889)
                  ·
                    refine ⟨17698837421489068952282917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23598449895318758603043889 17698837421489068952282917)
                    ·
                      refine ⟨3318532016529200428553047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17698837421489068952282917 3318532016529200428553047)
                      ·
                        rfl

theorem cell23_6462818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_6462818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462818 prefixEnd_6462818 := by exact prefixLift 6462818
  have htrace : WordTrace (prefixWord ++ tailWord_6462818) baseStart_6462818 baseEnd_6462818 := by
    simpa [prefixWord, tailWord_6462818, baseEnd_6462818] using wordTrace_append hprefix tailTrace_6462818
  have hstable : (prefixWord ++ tailWord_6462818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462818).length < 2 ^ (prefixWord ++ tailWord_6462818).sum := by decide
  have hdescent : baseEnd_6462818 < baseStart_6462818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6462995 : List Nat := [1, 1, 1, 2, 1, 6, 2, 3, 2, 4]
def baseStart_6462995 : Nat := 118140960795 + 6462995 * 2 ^ 59
def prefixEnd_6462995 : Nat := 4983230072969 + 3 ^ 40 * 6462995 * 2
def baseEnd_6462995 : Nat := 1106207634201682078679911

theorem tailTrace_6462995 : CollatzResearch.WordTrace tailWord_6462995 prefixEnd_6462995 1106207634201682078679911 := by
  unfold tailWord_6462995
  simp only [CollatzResearch.WordTrace]
  refine ⟨235724793220680381513766439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157149862147120254342510959 235724793220680381513766439)
  ·
    refine ⟨353587189831020572270649659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235724793220680381513766439 353587189831020572270649659)
    ·
      refine ⟨530380784746530858405974489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353587189831020572270649659 530380784746530858405974489)
      ·
        refine ⟨397785588559898143804480867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530380784746530858405974489 397785588559898143804480867)
        ·
          refine ⟨596678382839847215706721301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397785588559898143804480867 596678382839847215706721301)
          ·
            refine ⟨27969299195617838236252561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 596678382839847215706721301 27969299195617838236252561)
            ·
              refine ⟨20976974396713378677189421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27969299195617838236252561 20976974396713378677189421)
              ·
                refine ⟨7866365398767517003946033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20976974396713378677189421 7866365398767517003946033)
                ·
                  refine ⟨5899774049075637752959525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7866365398767517003946033 5899774049075637752959525)
                  ·
                    refine ⟨1106207634201682078679911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5899774049075637752959525 1106207634201682078679911)
                    ·
                      rfl

theorem cell23_6462995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 4].length) (baseStart_6462995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6462995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6462995 prefixEnd_6462995 := by exact prefixLift 6462995
  have htrace : WordTrace (prefixWord ++ tailWord_6462995) baseStart_6462995 baseEnd_6462995 := by
    simpa [prefixWord, tailWord_6462995, baseEnd_6462995] using wordTrace_append hprefix tailTrace_6462995
  have hstable : (prefixWord ++ tailWord_6462995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6462995).length < 2 ^ (prefixWord ++ tailWord_6462995).sum := by decide
  have hdescent : baseEnd_6462995 < baseStart_6462995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6462995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463005 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_6463005 : Nat := 118140960795 + 6463005 * 2 ^ 59
def prefixEnd_6463005 : Nat := 4983230072969 + 3 ^ 40 * 6463005 * 2
def baseEnd_6463005 : Nat := 3318628037411591196914687

theorem tailTrace_6463005 : CollatzResearch.WordTrace tailWord_6463005 prefixEnd_6463005 3318628037411591196914687 := by
  unfold tailWord_6463005
  simp only [CollatzResearch.WordTrace]
  refine ⟨235725157950644153221630469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157150105300429435481086979 235725157950644153221630469)
  ·
    refine ⟨44198467115745778729055713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235725157950644153221630469 44198467115745778729055713)
    ·
      refine ⟨33148850336809334046791785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44198467115745778729055713 33148850336809334046791785)
      ·
        refine ⟨24861637752607000535093839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33148850336809334046791785 24861637752607000535093839)
        ·
          refine ⟨37292456628910500802640759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24861637752607000535093839 37292456628910500802640759)
          ·
            refine ⟨55938684943365751203961139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37292456628910500802640759 55938684943365751203961139)
            ·
              refine ⟨83908027415048626805941709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55938684943365751203961139 83908027415048626805941709)
              ·
                refine ⟨31465510280643235052228141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83908027415048626805941709 31465510280643235052228141)
                ·
                  refine ⟨11799566355241213144585553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31465510280643235052228141 11799566355241213144585553)
                  ·
                    refine ⟨8849674766430909858439165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11799566355241213144585553 8849674766430909858439165)
                    ·
                      refine ⟨3318628037411591196914687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8849674766430909858439165 3318628037411591196914687)
                      ·
                        rfl

theorem cell23_6463005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_6463005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463005 prefixEnd_6463005 := by exact prefixLift 6463005
  have htrace : WordTrace (prefixWord ++ tailWord_6463005) baseStart_6463005 baseEnd_6463005 := by
    simpa [prefixWord, tailWord_6463005, baseEnd_6463005] using wordTrace_append hprefix tailTrace_6463005
  have hstable : (prefixWord ++ tailWord_6463005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463005).length < 2 ^ (prefixWord ++ tailWord_6463005).sum := by decide
  have hdescent : baseEnd_6463005 < baseStart_6463005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463016 : List Nat := [2, 1, 5, 2, 3, 1, 2, 1, 1, 5]
def baseStart_6463016 : Nat := 118140960795 + 6463016 * 2 ^ 59
def prefixEnd_6463016 : Nat := 4983230072969 + 3 ^ 40 * 6463016 * 2
def baseEnd_6463016 : Nat := 1106211228566263551292379

theorem tailTrace_6463016 : CollatzResearch.WordTrace tailWord_6463016 prefixEnd_6463016 1106211228566263551292379 := by
  unfold tailWord_6463016
  simp only [CollatzResearch.WordTrace]
  refine ⟨117862779576802151050140451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157150372769069534733520601 117862779576802151050140451)
  ·
    refine ⟨176794169365203226575210677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117862779576802151050140451 176794169365203226575210677)
    ·
      refine ⟨16574453377987802491426001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176794169365203226575210677 16574453377987802491426001)
      ·
        refine ⟨12430840033490851868569501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16574453377987802491426001 12430840033490851868569501)
        ·
          refine ⟨4661565012559069450713563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12430840033490851868569501 4661565012559069450713563)
          ·
            refine ⟨6992347518838604176070345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4661565012559069450713563 6992347518838604176070345)
            ·
              refine ⟨5244260639128953132052759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6992347518838604176070345 5244260639128953132052759)
              ·
                refine ⟨7866390958693429698079139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5244260639128953132052759 7866390958693429698079139)
                ·
                  refine ⟨11799586438040144547118709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7866390958693429698079139 11799586438040144547118709)
                  ·
                    refine ⟨1106211228566263551292379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11799586438040144547118709 1106211228566263551292379)
                    ·
                      rfl

theorem cell23_6463016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_6463016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463016 prefixEnd_6463016 := by exact prefixLift 6463016
  have htrace : WordTrace (prefixWord ++ tailWord_6463016) baseStart_6463016 baseEnd_6463016 := by
    simpa [prefixWord, tailWord_6463016, baseEnd_6463016] using wordTrace_append hprefix tailTrace_6463016
  have hstable : (prefixWord ++ tailWord_6463016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463016).length < 2 ^ (prefixWord ++ tailWord_6463016).sum := by decide
  have hdescent : baseEnd_6463016 < baseStart_6463016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463046 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_6463046 : Nat := 118140960795 + 6463046 * 2 ^ 59
def prefixEnd_6463046 : Nat := 4983230072969 + 3 ^ 40 * 6463046 * 2
def baseEnd_6463046 : Nat := 1106216363372808512167333

theorem tailTrace_6463046 : CollatzResearch.WordTrace tailWord_6463046 prefixEnd_6463046 1106216363372808512167333 := by
  unfold tailWord_6463046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7366457916984238038246031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157151102228997078149248661 7366457916984238038246031)
  ·
    refine ⟨11049686875476357057369047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7366457916984238038246031 11049686875476357057369047)
    ·
      refine ⟨16574530313214535586053571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11049686875476357057369047 16574530313214535586053571)
      ·
        refine ⟨24861795469821803379080357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16574530313214535586053571 24861795469821803379080357)
        ·
          refine ⟨4661586650591588133577567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24861795469821803379080357 4661586650591588133577567)
          ·
            refine ⟨6992379975887382200366351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4661586650591588133577567 6992379975887382200366351)
            ·
              refine ⟨10488569963831073300549527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6992379975887382200366351 10488569963831073300549527)
              ·
                refine ⟨15732854945746609950824291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10488569963831073300549527 15732854945746609950824291)
                ·
                  refine ⟨23599282418619914926236437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15732854945746609950824291 23599282418619914926236437)
                  ·
                    refine ⟨1106216363372808512167333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23599282418619914926236437 1106216363372808512167333)
                    ·
                      rfl

theorem cell23_6463046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_6463046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463046 prefixEnd_6463046 := by exact prefixLift 6463046
  have htrace : WordTrace (prefixWord ++ tailWord_6463046) baseStart_6463046 baseEnd_6463046 := by
    simpa [prefixWord, tailWord_6463046, baseEnd_6463046] using wordTrace_append hprefix tailTrace_6463046
  have hstable : (prefixWord ++ tailWord_6463046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463046).length < 2 ^ (prefixWord ++ tailWord_6463046).sum := by decide
  have hdescent : baseEnd_6463046 < baseStart_6463046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463052 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 1, 3, 3]
def baseStart_6463052 : Nat := 118140960795 + 6463052 * 2 ^ 59
def prefixEnd_6463052 : Nat := 4983230072969 + 3 ^ 40 * 6463052 * 2
def baseEnd_6463052 : Nat := 3318652171002352513026971

theorem tailTrace_6463052 : CollatzResearch.WordTrace tailWord_6463052 prefixEnd_6463052 3318652171002352513026971 := by
  unfold tailWord_6463052
  simp only [CollatzResearch.WordTrace]
  refine ⟨117863436090736940124295705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157151248120982586832394273 117863436090736940124295705)
  ·
    refine ⟨88397577068052705093221779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117863436090736940124295705 88397577068052705093221779)
    ·
      refine ⟨132596365602079057639832669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88397577068052705093221779 132596365602079057639832669)
      ·
        refine ⟨49723637100779646614937251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132596365602079057639832669 49723637100779646614937251)
        ·
          refine ⟨74585455651169469922405877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49723637100779646614937251 74585455651169469922405877)
          ·
            refine ⟨6992386467297137805225551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74585455651169469922405877 6992386467297137805225551)
            ·
              refine ⟨10488579700945706707838327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6992386467297137805225551 10488579700945706707838327)
              ·
                refine ⟨15732869551418560061757491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10488579700945706707838327 15732869551418560061757491)
                ·
                  refine ⟨23599304327127840092636237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15732869551418560061757491 23599304327127840092636237)
                  ·
                    refine ⟨8849739122672940034738589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23599304327127840092636237 8849739122672940034738589)
                    ·
                      refine ⟨3318652171002352513026971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8849739122672940034738589 3318652171002352513026971)
                      ·
                        rfl

theorem cell23_6463052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_6463052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463052 prefixEnd_6463052 := by exact prefixLift 6463052
  have htrace : WordTrace (prefixWord ++ tailWord_6463052) baseStart_6463052 baseEnd_6463052 := by
    simpa [prefixWord, tailWord_6463052, baseEnd_6463052] using wordTrace_append hprefix tailTrace_6463052
  have hstable : (prefixWord ++ tailWord_6463052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463052).length < 2 ^ (prefixWord ++ tailWord_6463052).sum := by decide
  have hdescent : baseEnd_6463052 < baseStart_6463052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463098 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 7]
def baseStart_6463098 : Nat := 118140960795 + 6463098 * 2 ^ 59
def prefixEnd_6463098 : Nat := 4983230072969 + 3 ^ 40 * 6463098 * 2
def baseEnd_6463098 : Nat := 368741754568051037005751

theorem tailTrace_6463098 : CollatzResearch.WordTrace tailWord_6463098 prefixEnd_6463098 368741754568051037005751 := by
  unfold tailWord_6463098
  simp only [CollatzResearch.WordTrace]
  refine ⟨58932137484826807526191487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157152366626204820069843965 58932137484826807526191487)
  ·
    refine ⟨88398206227240211289287231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58932137484826807526191487 88398206227240211289287231)
    ·
      refine ⟨132597309340860316933930847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88398206227240211289287231 132597309340860316933930847)
      ·
        refine ⟨198895964011290475400896271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132597309340860316933930847 198895964011290475400896271)
        ·
          refine ⟨298343946016935713101344407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198895964011290475400896271 298343946016935713101344407)
          ·
            refine ⟨447515919025403569652016611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298343946016935713101344407 447515919025403569652016611)
            ·
              refine ⟨671273878538105354478024917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447515919025403569652016611 671273878538105354478024917)
              ·
                refine ⟨15732981528236844245578709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 671273878538105354478024917 15732981528236844245578709)
                ·
                  refine ⟨368741754568051037005751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15732981528236844245578709 368741754568051037005751)
                  ·
                    rfl

theorem cell23_6463098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_6463098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463098 prefixEnd_6463098 := by exact prefixLift 6463098
  have htrace : WordTrace (prefixWord ++ tailWord_6463098) baseStart_6463098 baseEnd_6463098 := by
    simpa [prefixWord, tailWord_6463098, baseEnd_6463098] using wordTrace_append hprefix tailTrace_6463098
  have hstable : (prefixWord ++ tailWord_6463098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463098).length < 2 ^ (prefixWord ++ tailWord_6463098).sum := by decide
  have hdescent : baseEnd_6463098 < baseStart_6463098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463109 : List Nat := [1, 3, 1, 1, 4, 1, 3, 3, 2, 2, 2]
def baseStart_6463109 : Nat := 118140960795 + 6463109 * 2 ^ 59
def prefixEnd_6463109 : Nat := 4983230072969 + 3 ^ 40 * 6463109 * 2
def baseEnd_6463109 : Nat := 3318681439399658790014209

theorem tailTrace_6463109 : CollatzResearch.WordTrace tailWord_6463109 prefixEnd_6463109 3318681439399658790014209 := by
  unfold tailWord_6463109
  simp only [CollatzResearch.WordTrace]
  refine ⟨235728951142267378983416381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157152634094844919322277587 235728951142267378983416381)
  ·
    refine ⟨88398356678350267118781143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235728951142267378983416381 88398356678350267118781143)
    ·
      refine ⟨132597535017525400678171715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88398356678350267118781143 132597535017525400678171715)
      ·
        refine ⟨198896302526288101017257573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132597535017525400678171715 198896302526288101017257573)
        ·
          refine ⟨37293056723679018940735795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198896302526288101017257573 37293056723679018940735795)
          ·
            refine ⟨55939585085518528411103693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37293056723679018940735795 55939585085518528411103693)
            ·
              refine ⟨20977344407069448154163885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55939585085518528411103693 20977344407069448154163885)
              ·
                refine ⟨7866504152651043057811457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20977344407069448154163885 7866504152651043057811457)
                ·
                  refine ⟨5899878114488282293358593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7866504152651043057811457 5899878114488282293358593)
                  ·
                    refine ⟨4424908585866211720018945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5899878114488282293358593 4424908585866211720018945)
                    ·
                      refine ⟨3318681439399658790014209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4424908585866211720018945 3318681439399658790014209)
                      ·
                        rfl

theorem cell23_6463109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 2, 2].length) (baseStart_6463109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463109 prefixEnd_6463109 := by exact prefixLift 6463109
  have htrace : WordTrace (prefixWord ++ tailWord_6463109) baseStart_6463109 baseEnd_6463109 := by
    simpa [prefixWord, tailWord_6463109, baseEnd_6463109] using wordTrace_append hprefix tailTrace_6463109
  have hstable : (prefixWord ++ tailWord_6463109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463109).length < 2 ^ (prefixWord ++ tailWord_6463109).sum := by decide
  have hdescent : baseEnd_6463109 < baseStart_6463109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463165 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_6463165 : Nat := 118140960795 + 6463165 * 2 ^ 59
def prefixEnd_6463165 : Nat := 4983230072969 + 3 ^ 40 * 6463165 * 2
def baseEnd_6463165 : Nat := 3318710194316310570913951

theorem tailTrace_6463165 : CollatzResearch.WordTrace tailWord_6463165 prefixEnd_6463165 3318710194316310570913951 := by
  unfold tailWord_6463165
  simp only [CollatzResearch.WordTrace]
  refine ⟨235730993630064500547454949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157153995753376333698303299 235730993630064500547454949)
  ·
    refine ⟨44199561305637093852647803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235730993630064500547454949 44199561305637093852647803)
    ·
      refine ⟨66299341958455640778971705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44199561305637093852647803 66299341958455640778971705)
      ·
        refine ⟨49724506468841730584228779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66299341958455640778971705 49724506468841730584228779)
        ·
          refine ⟨74586759703262595876343169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49724506468841730584228779 74586759703262595876343169)
          ·
            refine ⟨55940069777446946907257377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74586759703262595876343169 55940069777446946907257377)
            ·
              refine ⟨41955052333085210180443033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55940069777446946907257377 41955052333085210180443033)
              ·
                refine ⟨31466289249813907635332275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41955052333085210180443033 31466289249813907635332275)
                ·
                  refine ⟨47199433874720861452998413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31466289249813907635332275 47199433874720861452998413)
                  ·
                    refine ⟨17699787703020323044874405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47199433874720861452998413 17699787703020323044874405)
                    ·
                      refine ⟨3318710194316310570913951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17699787703020323044874405 3318710194316310570913951)
                      ·
                        rfl

theorem cell23_6463165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_6463165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463165 prefixEnd_6463165 := by exact prefixLift 6463165
  have htrace : WordTrace (prefixWord ++ tailWord_6463165) baseStart_6463165 baseEnd_6463165 := by
    simpa [prefixWord, tailWord_6463165, baseEnd_6463165] using wordTrace_append hprefix tailTrace_6463165
  have hstable : (prefixWord ++ tailWord_6463165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463165).length < 2 ^ (prefixWord ++ tailWord_6463165).sum := by decide
  have hdescent : baseEnd_6463165 < baseStart_6463165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463182 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2]
def baseStart_6463182 : Nat := 118140960795 + 6463182 * 2 ^ 59
def prefixEnd_6463182 : Nat := 4983230072969 + 3 ^ 40 * 6463182 * 2
def baseEnd_6463182 : Nat := 3318718923487437004401373

theorem tailTrace_6463182 : CollatzResearch.WordTrace tailWord_6463182 prefixEnd_6463182 3318718923487437004401373 := by
  unfold tailWord_6463182
  simp only [CollatzResearch.WordTrace]
  refine ⟨29466451708875364056352975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157154409114001941633882533 29466451708875364056352975)
  ·
    refine ⟨44199677563313046084529463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29466451708875364056352975 44199677563313046084529463)
    ·
      refine ⟨66299516344969569126794195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44199677563313046084529463 66299516344969569126794195)
      ·
        refine ⟨99449274517454353690191293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66299516344969569126794195 99449274517454353690191293)
        ·
          refine ⟨37293477944045382633821735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99449274517454353690191293 37293477944045382633821735)
          ·
            refine ⟨55940216916068073950732603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37293477944045382633821735 55940216916068073950732603)
            ·
              refine ⟨83910325374102110926098905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55940216916068073950732603 83910325374102110926098905)
              ·
                refine ⟨62932744030576583194574179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83910325374102110926098905 62932744030576583194574179)
                ·
                  refine ⟨94399116045864874791861269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62932744030576583194574179 94399116045864874791861269)
                  ·
                    refine ⟨4424958564649916005868497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94399116045864874791861269 4424958564649916005868497)
                    ·
                      refine ⟨3318718923487437004401373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4424958564649916005868497 3318718923487437004401373)
                      ·
                        rfl

theorem cell23_6463182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_6463182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463182 prefixEnd_6463182 := by exact prefixLift 6463182
  have htrace : WordTrace (prefixWord ++ tailWord_6463182) baseStart_6463182 baseEnd_6463182 := by
    simpa [prefixWord, tailWord_6463182, baseEnd_6463182] using wordTrace_append hprefix tailTrace_6463182
  have hstable : (prefixWord ++ tailWord_6463182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463182).length < 2 ^ (prefixWord ++ tailWord_6463182).sum := by decide
  have hdescent : baseEnd_6463182 < baseStart_6463182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463205 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 8]
def baseStart_6463205 : Nat := 118140960795 + 6463205 * 2 ^ 59
def prefixEnd_6463205 : Nat := 4983230072969 + 3 ^ 40 * 6463205 * 2
def baseEnd_6463205 : Nat := 368747859282498934934863

theorem tailTrace_6463205 : CollatzResearch.WordTrace tailWord_6463205 prefixEnd_6463205 368747859282498934934863 := by
  unfold tailWord_6463205
  simp only [CollatzResearch.WordTrace]
  refine ⟨235732452549919587378911069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157154968366613058252607379 235732452549919587378911069)
  ·
    refine ⟨88399669706219845267091651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235732452549919587378911069 88399669706219845267091651)
    ·
      refine ⟨132599504559329767900637477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88399669706219845267091651 132599504559329767900637477)
      ·
        refine ⟨24862407104874331481369527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132599504559329767900637477 24862407104874331481369527)
        ·
          refine ⟨37293610657311497222054291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24862407104874331481369527 37293610657311497222054291)
          ·
            refine ⟨55940415985967245833081437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37293610657311497222054291 55940415985967245833081437)
            ·
              refine ⟨20977655994737717187405539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55940415985967245833081437 20977655994737717187405539)
              ·
                refine ⟨31466483992106575781108309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20977655994737717187405539 31466483992106575781108309)
                ·
                  refine ⟨368747859282498934934863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31466483992106575781108309 368747859282498934934863)
                  ·
                    rfl

theorem cell23_6463205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_6463205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463205 prefixEnd_6463205 := by exact prefixLift 6463205
  have htrace : WordTrace (prefixWord ++ tailWord_6463205) baseStart_6463205 baseEnd_6463205 := by
    simpa [prefixWord, tailWord_6463205, baseEnd_6463205] using wordTrace_append hprefix tailTrace_6463205
  have hstable : (prefixWord ++ tailWord_6463205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463205).length < 2 ^ (prefixWord ++ tailWord_6463205).sum := by decide
  have hdescent : baseEnd_6463205 < baseStart_6463205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463235 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 3, 5]
def baseStart_6463235 : Nat := 118140960795 + 6463235 * 2 ^ 59
def prefixEnd_6463235 : Nat := 4983230072969 + 3 ^ 40 * 6463235 * 2
def baseEnd_6463235 : Nat := 1106248712654041765679543

theorem tailTrace_6463235 : CollatzResearch.WordTrace tailWord_6463235 prefixEnd_6463235 1106248712654041765679543 := by
  unfold tailWord_6463235
  simp only [CollatzResearch.WordTrace]
  refine ⟨235733546739810902502503159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157155697826540601668335439 235733546739810902502503159)
  ·
    refine ⟨353600320109716353753754739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235733546739810902502503159 353600320109716353753754739)
    ·
      refine ⟨530400480164574530630632109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353600320109716353753754739 530400480164574530630632109)
      ·
        refine ⟨198900180061715448986487041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 530400480164574530630632109 198900180061715448986487041)
        ·
          refine ⟨149175135046286586739865281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198900180061715448986487041 149175135046286586739865281)
          ·
            refine ⟨111881351284714940054898961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149175135046286586739865281 111881351284714940054898961)
            ·
              refine ⟨83911013463536205041174221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111881351284714940054898961 83911013463536205041174221)
              ·
                refine ⟨31466630048826076890440333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83911013463536205041174221 31466630048826076890440333)
                ·
                  refine ⟨11799986268309778833915125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31466630048826076890440333 11799986268309778833915125)
                  ·
                    refine ⟨1106248712654041765679543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11799986268309778833915125 1106248712654041765679543)
                    ·
                      rfl

theorem cell23_6463235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 5].length) (baseStart_6463235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463235 prefixEnd_6463235 := by exact prefixLift 6463235
  have htrace : WordTrace (prefixWord ++ tailWord_6463235) baseStart_6463235 baseEnd_6463235 := by
    simpa [prefixWord, tailWord_6463235, baseEnd_6463235] using wordTrace_append hprefix tailTrace_6463235
  have hstable : (prefixWord ++ tailWord_6463235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463235).length < 2 ^ (prefixWord ++ tailWord_6463235).sum := by decide
  have hdescent : baseEnd_6463235 < baseStart_6463235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463286 : List Nat := [5, 1, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_6463286 : Nat := 118140960795 + 6463286 * 2 ^ 59
def prefixEnd_6463286 : Nat := 4983230072969 + 3 ^ 40 * 6463286 * 2
def baseEnd_6463286 : Nat := 1106257441825168199166965

theorem tailTrace_6463286 : CollatzResearch.WordTrace tailWord_6463286 prefixEnd_6463286 1106257441825168199166965 := by
  unfold tailWord_6463286
  simp only [CollatzResearch.WordTrace]
  refine ⟨14733462928914133638288107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157156937908417425475073141 14733462928914133638288107)
  ·
    refine ⟨22100194393371200457432161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14733462928914133638288107 22100194393371200457432161)
    ·
      refine ⟨16575145795028400343074121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22100194393371200457432161 16575145795028400343074121)
      ·
        refine ⟨12431359346271300257305591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16575145795028400343074121 12431359346271300257305591)
        ·
          refine ⟨18647039019406950385958387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12431359346271300257305591 18647039019406950385958387)
          ·
            refine ⟨27970558529110425578937581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18647039019406950385958387 27970558529110425578937581)
            ·
              refine ⟨10488959448416409592101593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27970558529110425578937581 10488959448416409592101593)
              ·
                refine ⟨7866719586312307194076195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10488959448416409592101593 7866719586312307194076195)
                ·
                  refine ⟨11800079379468460791114293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7866719586312307194076195 11800079379468460791114293)
                  ·
                    refine ⟨1106257441825168199166965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11800079379468460791114293 1106257441825168199166965)
                    ·
                      rfl

theorem cell23_6463286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_6463286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463286 prefixEnd_6463286 := by exact prefixLift 6463286
  have htrace : WordTrace (prefixWord ++ tailWord_6463286) baseStart_6463286 baseEnd_6463286 := by
    simpa [prefixWord, tailWord_6463286, baseEnd_6463286] using wordTrace_append hprefix tailTrace_6463286
  have hstable : (prefixWord ++ tailWord_6463286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463286).length < 2 ^ (prefixWord ++ tailWord_6463286).sum := by decide
  have hdescent : baseEnd_6463286 < baseStart_6463286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463316 : List Nat := [2, 4, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_6463316 : Nat := 118140960795 + 6463316 * 2 ^ 59
def prefixEnd_6463316 : Nat := 4983230072969 + 3 ^ 40 * 6463316 * 2
def baseEnd_6463316 : Nat := 1106262576631713160041919

theorem tailTrace_6463316 : CollatzResearch.WordTrace tailWord_6463316 prefixEnd_6463316 1106262576631713160041919 := by
  unfold tailWord_6463316
  simp only [CollatzResearch.WordTrace]
  refine ⟨117868250526258726668100901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157157667368344968890801201 117868250526258726668100901)
  ·
    refine ⟨22100296973673511250268919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117868250526258726668100901 22100296973673511250268919)
    ·
      refine ⟨33150445460510266875403379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22100296973673511250268919 33150445460510266875403379)
      ·
        refine ⟨49725668190765400313105069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33150445460510266875403379 49725668190765400313105069)
        ·
          refine ⟨18647125571537025117414401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49725668190765400313105069 18647125571537025117414401)
          ·
            refine ⟨13985344178652768838060801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18647125571537025117414401 13985344178652768838060801)
            ·
              refine ⟨10489008133989576628545601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13985344178652768838060801 10489008133989576628545601)
              ·
                refine ⟨7866756100492182471409201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10489008133989576628545601 7866756100492182471409201)
                ·
                  refine ⟨5900067075369136853556901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7866756100492182471409201 5900067075369136853556901)
                  ·
                    refine ⟨1106262576631713160041919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5900067075369136853556901 1106262576631713160041919)
                    ·
                      rfl

theorem cell23_6463316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_6463316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463316 prefixEnd_6463316 := by exact prefixLift 6463316
  have htrace : WordTrace (prefixWord ++ tailWord_6463316) baseStart_6463316 baseEnd_6463316 := by
    simpa [prefixWord, tailWord_6463316, baseEnd_6463316] using wordTrace_append hprefix tailTrace_6463316
  have hstable : (prefixWord ++ tailWord_6463316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463316).length < 2 ^ (prefixWord ++ tailWord_6463316).sum := by decide
  have hdescent : baseEnd_6463316 < baseStart_6463316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463322 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3]
def baseStart_6463322 : Nat := 118140960795 + 6463322 * 2 ^ 59
def prefixEnd_6463322 : Nat := 4983230072969 + 3 ^ 40 * 6463322 * 2
def baseEnd_6463322 : Nat := 3318790810779066456650729

theorem tailTrace_6463322 : CollatzResearch.WordTrace tailWord_6463322 prefixEnd_6463322 3318790810779066456650729 := by
  unfold tailWord_6463322
  simp only [CollatzResearch.WordTrace]
  refine ⟨58934179972623929090230055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157157813260330477573946813 58934179972623929090230055)
  ·
    refine ⟨88401269958935893635345083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58934179972623929090230055 88401269958935893635345083)
    ·
      refine ⟨132601904938403840453017625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88401269958935893635345083 132601904938403840453017625)
      ·
        refine ⟨99451428703802880339763219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132601904938403840453017625 99451428703802880339763219)
        ·
          refine ⟨149177143055704320509644829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99451428703802880339763219 149177143055704320509644829)
          ·
            refine ⟨55941428645889120191116811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149177143055704320509644829 55941428645889120191116811)
            ·
              refine ⟨83912142968833680286675217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55941428645889120191116811 83912142968833680286675217)
              ·
                refine ⟨62934107226625260215006413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83912142968833680286675217 62934107226625260215006413)
                ·
                  refine ⟨23600290209984472580627405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62934107226625260215006413 23600290209984472580627405)
                  ·
                    refine ⟨8850108828744177217735277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23600290209984472580627405 8850108828744177217735277)
                    ·
                      refine ⟨3318790810779066456650729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8850108828744177217735277 3318790810779066456650729)
                      ·
                        rfl

theorem cell23_6463322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_6463322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463322 prefixEnd_6463322 := by exact prefixLift 6463322
  have htrace : WordTrace (prefixWord ++ tailWord_6463322) baseStart_6463322 baseEnd_6463322 := by
    simpa [prefixWord, tailWord_6463322, baseEnd_6463322] using wordTrace_append hprefix tailTrace_6463322
  have hstable : (prefixWord ++ tailWord_6463322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463322).length < 2 ^ (prefixWord ++ tailWord_6463322).sum := by decide
  have hdescent : baseEnd_6463322 < baseStart_6463322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463355 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 3, 8]
def baseStart_6463355 : Nat := 118140960795 + 6463355 * 2 ^ 59
def prefixEnd_6463355 : Nat := 4983230072969 + 3 ^ 40 * 6463355 * 2
def baseEnd_6463355 : Nat := 1106269251880221609179359

theorem tailTrace_6463355 : CollatzResearch.WordTrace tailWord_6463355 prefixEnd_6463355 1106269251880221609179359 := by
  unfold tailWord_6463355
  simp only [CollatzResearch.WordTrace]
  refine ⟨235737923499376162996871519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157158615666250775331247679 235737923499376162996871519)
  ·
    refine ⟨353606885249064244495307279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235737923499376162996871519 353606885249064244495307279)
    ·
      refine ⟨530410327873596366742960919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353606885249064244495307279 530410327873596366742960919)
      ·
        refine ⟨795615491810394550114441379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530410327873596366742960919 795615491810394550114441379)
        ·
          refine ⟨1193423237715591825171662069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795615491810394550114441379 1193423237715591825171662069)
          ·
            refine ⟨111883428535836733609843319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1193423237715591825171662069 111883428535836733609843319)
            ·
              refine ⟨167825142803755100414764979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111883428535836733609843319 167825142803755100414764979)
              ·
                refine ⟨251737714205632650622147469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167825142803755100414764979 251737714205632650622147469)
                ·
                  refine ⟨94401642827112243983305301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251737714205632650622147469 94401642827112243983305301)
                  ·
                    refine ⟨1106269251880221609179359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94401642827112243983305301 1106269251880221609179359)
                    ·
                      rfl

theorem cell23_6463355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 8].length) (baseStart_6463355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463355 prefixEnd_6463355 := by exact prefixLift 6463355
  have htrace : WordTrace (prefixWord ++ tailWord_6463355) baseStart_6463355 baseEnd_6463355 := by
    simpa [prefixWord, tailWord_6463355, baseEnd_6463355] using wordTrace_append hprefix tailTrace_6463355
  have hstable : (prefixWord ++ tailWord_6463355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463355).length < 2 ^ (prefixWord ++ tailWord_6463355).sum := by decide
  have hdescent : baseEnd_6463355 < baseStart_6463355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463390 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_6463390 : Nat := 118140960795 + 6463390 * 2 ^ 59
def prefixEnd_6463390 : Nat := 4983230072969 + 3 ^ 40 * 6463390 * 2
def baseEnd_6463390 : Nat := 3318825727463572190600417

theorem tailTrace_6463390 : CollatzResearch.WordTrace tailWord_6463390 prefixEnd_6463390 3318825727463572190600417 := by
  unfold tailWord_6463390
  simp only [CollatzResearch.WordTrace]
  refine ⟨29467400006781170496799453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157159466702832909316263749 29467400006781170496799453)
  ·
    refine ⟨11050275002542938936299795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29467400006781170496799453 11050275002542938936299795)
    ·
      refine ⟨16575412503814408404449693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11050275002542938936299795 16575412503814408404449693)
      ·
        refine ⟨6215779688930403151668635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16575412503814408404449693 6215779688930403151668635)
        ·
          refine ⟨9323669533395604727502953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215779688930403151668635 9323669533395604727502953)
          ·
            refine ⟨6992752150046703545627215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9323669533395604727502953 6992752150046703545627215)
            ·
              refine ⟨10489128225070055318440823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6992752150046703545627215 10489128225070055318440823)
              ·
                refine ⟨15733692337605082977661235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10489128225070055318440823 15733692337605082977661235)
                ·
                  refine ⟨23600538506407624466491853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15733692337605082977661235 23600538506407624466491853)
                  ·
                    refine ⟨8850201939902859174934445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23600538506407624466491853 8850201939902859174934445)
                    ·
                      refine ⟨3318825727463572190600417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8850201939902859174934445 3318825727463572190600417)
                      ·
                        rfl

theorem cell23_6463390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_6463390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463390 prefixEnd_6463390 := by exact prefixLift 6463390
  have htrace : WordTrace (prefixWord ++ tailWord_6463390) baseStart_6463390 baseEnd_6463390 := by
    simpa [prefixWord, tailWord_6463390, baseEnd_6463390] using wordTrace_append hprefix tailTrace_6463390
  have hstable : (prefixWord ++ tailWord_6463390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463390).length < 2 ^ (prefixWord ++ tailWord_6463390).sum := by decide
  have hdescent : baseEnd_6463390 < baseStart_6463390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463396 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 1, 4, 2]
def baseStart_6463396 : Nat := 118140960795 + 6463396 * 2 ^ 59
def prefixEnd_6463396 : Nat := 4983230072969 + 3 ^ 40 * 6463396 * 2
def baseEnd_6463396 : Nat := 3318828808347499167125389

theorem tailTrace_6463396 : CollatzResearch.WordTrace tailWord_6463396 prefixEnd_6463396 3318828808347499167125389 := by
  unfold tailWord_6463396
  simp only [CollatzResearch.WordTrace]
  refine ⟨117869709446113813499557021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157159612594818417999409361 117869709446113813499557021)
  ·
    refine ⟨44201141042292680062333883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117869709446113813499557021 44201141042292680062333883)
    ·
      refine ⟨66301711563439020093500825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44201141042292680062333883 66301711563439020093500825)
      ·
        refine ⟨49726283672579265070125619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66301711563439020093500825 49726283672579265070125619)
        ·
          refine ⟨74589425508868897605188429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49726283672579265070125619 74589425508868897605188429)
          ·
            refine ⟨27971034565825836601945661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74589425508868897605188429 27971034565825836601945661)
            ·
              refine ⟨10489137962184688725729623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27971034565825836601945661 10489137962184688725729623)
              ·
                refine ⟨15733706943277033088594435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10489137962184688725729623 15733706943277033088594435)
                ·
                  refine ⟨23600560414915549632891653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15733706943277033088594435 23600560414915549632891653)
                  ·
                    refine ⟨4425105077796665556167185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23600560414915549632891653 4425105077796665556167185)
                    ·
                      refine ⟨3318828808347499167125389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425105077796665556167185 3318828808347499167125389)
                      ·
                        rfl

theorem cell23_6463396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_6463396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463396 prefixEnd_6463396 := by exact prefixLift 6463396
  have htrace : WordTrace (prefixWord ++ tailWord_6463396) baseStart_6463396 baseEnd_6463396 := by
    simpa [prefixWord, tailWord_6463396, baseEnd_6463396] using wordTrace_append hprefix tailTrace_6463396
  have hstable : (prefixWord ++ tailWord_6463396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463396).length < 2 ^ (prefixWord ++ tailWord_6463396).sum := by decide
  have hdescent : baseEnd_6463396 < baseStart_6463396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463439 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 2, 5, 2]
def baseStart_6463439 : Nat := 118140960795 + 6463439 * 2 ^ 59
def prefixEnd_6463439 : Nat := 4983230072969 + 3 ^ 40 * 6463439 * 2
def baseEnd_6463439 : Nat := 3318850888015642498887691

theorem tailTrace_6463439 : CollatzResearch.WordTrace tailWord_6463439 prefixEnd_6463439 3318850888015642498887691 := by
  unfold tailWord_6463439
  simp only [CollatzResearch.WordTrace]
  refine ⟨235740987231071845342929371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157160658154047896895286247 235740987231071845342929371)
  ·
    refine ⟨353611480846607768014394057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235740987231071845342929371 353611480846607768014394057)
    ·
      refine ⟨265208610634955826010795543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353611480846607768014394057 265208610634955826010795543)
      ·
        refine ⟨397812915952433739016193315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265208610634955826010795543 397812915952433739016193315)
        ·
          refine ⟨596719373928650608524289973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397812915952433739016193315 596719373928650608524289973)
          ·
            refine ⟨55942441305810994549152185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 596719373928650608524289973 55942441305810994549152185)
            ·
              refine ⟨41956830979358245911864139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55942441305810994549152185 41956830979358245911864139)
              ·
                refine ⟨62935246469037368867796209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41956830979358245911864139 62935246469037368867796209)
                ·
                  refine ⟨47201434851778026650847157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62935246469037368867796209 47201434851778026650847157)
                  ·
                    refine ⟨4425134517354189998516921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47201434851778026650847157 4425134517354189998516921)
                    ·
                      refine ⟨3318850888015642498887691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425134517354189998516921 3318850888015642498887691)
                      ·
                        rfl

theorem cell23_6463439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 5, 2].length) (baseStart_6463439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463439 prefixEnd_6463439 := by exact prefixLift 6463439
  have htrace : WordTrace (prefixWord ++ tailWord_6463439) baseStart_6463439 baseEnd_6463439 := by
    simpa [prefixWord, tailWord_6463439, baseEnd_6463439] using wordTrace_append hprefix tailTrace_6463439
  have hstable : (prefixWord ++ tailWord_6463439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463439).length < 2 ^ (prefixWord ++ tailWord_6463439).sum := by decide
  have hdescent : baseEnd_6463439 < baseStart_6463439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463530 : List Nat := [3, 1, 4, 1, 2, 2, 2, 3, 1, 4]
def baseStart_6463530 : Nat := 118140960795 + 6463530 * 2 ^ 59
def prefixEnd_6463530 : Nat := 4983230072969 + 3 ^ 40 * 6463530 * 2
def baseEnd_6463530 : Nat := 1106299204918400547616591

theorem tailTrace_6463530 : CollatzResearch.WordTrace tailWord_6463530 prefixEnd_6463530 1106299204918400547616591 := by
  unfold tailWord_6463530
  simp only [CollatzResearch.WordTrace]
  refine ⟨58936076568435541971123011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157162870849161445256328029 58936076568435541971123011)
  ·
    refine ⟨88404114852653312956684517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58936076568435541971123011 88404114852653312956684517)
    ·
      refine ⟨16575771534872496179378347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88404114852653312956684517 16575771534872496179378347)
      ·
        refine ⟨24863657302308744269067521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16575771534872496179378347 24863657302308744269067521)
        ·
          refine ⟨18647742976731558201800641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24863657302308744269067521 18647742976731558201800641)
          ·
            refine ⟨13985807232548668651350481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18647742976731558201800641 13985807232548668651350481)
            ·
              refine ⟨10489355424411501488512861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13985807232548668651350481 10489355424411501488512861)
              ·
                refine ⟨3933508284154313058192323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10489355424411501488512861 3933508284154313058192323)
                ·
                  refine ⟨5900262426231469587288485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3933508284154313058192323 5900262426231469587288485)
                  ·
                    refine ⟨1106299204918400547616591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5900262426231469587288485 1106299204918400547616591)
                    ·
                      rfl

theorem cell23_6463530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_6463530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463530 prefixEnd_6463530 := by exact prefixLift 6463530
  have htrace : WordTrace (prefixWord ++ tailWord_6463530) baseStart_6463530 baseEnd_6463530 := by
    simpa [prefixWord, tailWord_6463530, baseEnd_6463530] using wordTrace_append hprefix tailTrace_6463530
  have hstable : (prefixWord ++ tailWord_6463530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463530).length < 2 ^ (prefixWord ++ tailWord_6463530).sum := by decide
  have hdescent : baseEnd_6463530 < baseStart_6463530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463546 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2]
def baseStart_6463546 : Nat := 118140960795 + 6463546 * 2 ^ 59
def prefixEnd_6463546 : Nat := 4983230072969 + 3 ^ 40 * 6463546 * 2
def baseEnd_6463546 : Nat := 3318905830445673580249699

theorem tailTrace_6463546 : CollatzResearch.WordTrace tailWord_6463546 prefixEnd_6463546 3318905830445673580249699 := by
  unfold tailWord_6463546
  simp only [CollatzResearch.WordTrace]
  refine ⟨58936222460421050654268623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157163259894456135078049661 58936222460421050654268623)
  ·
    refine ⟨88404333690631575981402935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58936222460421050654268623 88404333690631575981402935)
    ·
      refine ⟨132606500535947363972104403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88404333690631575981402935 132606500535947363972104403)
      ·
        refine ⟨198909750803921045958156605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132606500535947363972104403 198909750803921045958156605)
        ·
          refine ⟨74591156551470392234308727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198909750803921045958156605 74591156551470392234308727)
          ·
            refine ⟨111886734827205588351463091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74591156551470392234308727 111886734827205588351463091)
            ·
              refine ⟨167830102240808382527194637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111886734827205588351463091 167830102240808382527194637)
              ·
                refine ⟨62936288340303143447697989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167830102240808382527194637 62936288340303143447697989)
                ·
                  refine ⟨11800554063806839396443373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62936288340303143447697989 11800554063806839396443373)
                  ·
                    refine ⟨4425207773927564773666265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11800554063806839396443373 4425207773927564773666265)
                    ·
                      refine ⟨3318905830445673580249699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425207773927564773666265 3318905830445673580249699)
                      ·
                        rfl

theorem cell23_6463546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2].length) (baseStart_6463546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463546 prefixEnd_6463546 := by exact prefixLift 6463546
  have htrace : WordTrace (prefixWord ++ tailWord_6463546) baseStart_6463546 baseEnd_6463546 := by
    simpa [prefixWord, tailWord_6463546, baseEnd_6463546] using wordTrace_append hprefix tailTrace_6463546
  have hstable : (prefixWord ++ tailWord_6463546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463546).length < 2 ^ (prefixWord ++ tailWord_6463546).sum := by decide
  have hdescent : baseEnd_6463546 < baseStart_6463546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463553 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_6463553 : Nat := 118140960795 + 6463553 * 2 ^ 59
def prefixEnd_6463553 : Nat := 4983230072969 + 3 ^ 40 * 6463553 * 2
def baseEnd_6463553 : Nat := 3318909424810255052862167

theorem tailTrace_6463553 : CollatzResearch.WordTrace tailWord_6463553 prefixEnd_6463553 3318909424810255052862167 := by
  unfold tailWord_6463553
  simp only [CollatzResearch.WordTrace]
  refine ⟨235745145152658842812579313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157163430101772561875052875 235745145152658842812579313)
  ·
    refine ⟨176808858864494132109434485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235745145152658842812579313 176808858864494132109434485)
    ·
      refine ⟨16575830518546324885259483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176808858864494132109434485 16575830518546324885259483)
      ·
        refine ⟨24863745777819487327889225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16575830518546324885259483 24863745777819487327889225)
        ·
          refine ⟨18647809333364615495916919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24863745777819487327889225 18647809333364615495916919)
          ·
            refine ⟨27971714000046923243875379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18647809333364615495916919 27971714000046923243875379)
            ·
              refine ⟨41957571000070384865813069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27971714000046923243875379 41957571000070384865813069)
              ·
                refine ⟨15734089125026394324679901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41957571000070384865813069 15734089125026394324679901)
                ·
                  refine ⟨5900283421884897871754963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15734089125026394324679901 5900283421884897871754963)
                  ·
                    refine ⟨8850425132827346807632445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5900283421884897871754963 8850425132827346807632445)
                    ·
                      refine ⟨3318909424810255052862167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8850425132827346807632445 3318909424810255052862167)
                      ·
                        rfl

theorem cell23_6463553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_6463553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463553 prefixEnd_6463553 := by exact prefixLift 6463553
  have htrace : WordTrace (prefixWord ++ tailWord_6463553) baseStart_6463553 baseEnd_6463553 := by
    simpa [prefixWord, tailWord_6463553, baseEnd_6463553] using wordTrace_append hprefix tailTrace_6463553
  have hstable : (prefixWord ++ tailWord_6463553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463553).length < 2 ^ (prefixWord ++ tailWord_6463553).sum := by decide
  have hdescent : baseEnd_6463553 < baseStart_6463553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463576 : List Nat := [2, 1, 2, 2, 1, 4, 1, 4, 1, 1, 4]
def baseStart_6463576 : Nat := 118140960795 + 6463576 * 2 ^ 59
def prefixEnd_6463576 : Nat := 4983230072969 + 3 ^ 40 * 6463576 * 2
def baseEnd_6463576 : Nat := 3318921234865308462874561

theorem tailTrace_6463576 : CollatzResearch.WordTrace tailWord_6463576 prefixEnd_6463576 3318921234865308462874561 := by
  unfold tailWord_6463576
  simp only [CollatzResearch.WordTrace]
  refine ⟨117872992015787758870333291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157163989354383678493777721 117872992015787758870333291)
  ·
    refine ⟨176809488023681638305499937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117872992015787758870333291 176809488023681638305499937)
    ·
      refine ⟨132607116017761228729124953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176809488023681638305499937 132607116017761228729124953)
      ·
        refine ⟨99455337013320921546843715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132607116017761228729124953 99455337013320921546843715)
        ·
          refine ⟨149183005519981382320265573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99455337013320921546843715 149183005519981382320265573)
          ·
            refine ⟨27971813534996509185049795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149183005519981382320265573 27971813534996509185049795)
            ·
              refine ⟨41957720302494763777574693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27971813534996509185049795 41957720302494763777574693)
              ·
                refine ⟨7867072556717768208295255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41957720302494763777574693 7867072556717768208295255)
                ·
                  refine ⟨11800608835076652312442883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7867072556717768208295255 11800608835076652312442883)
                  ·
                    refine ⟨17700913252614978468664325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11800608835076652312442883 17700913252614978468664325)
                    ·
                      refine ⟨3318921234865308462874561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17700913252614978468664325 3318921234865308462874561)
                      ·
                        rfl

theorem cell23_6463576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_6463576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463576 prefixEnd_6463576 := by exact prefixLift 6463576
  have htrace : WordTrace (prefixWord ++ tailWord_6463576) baseStart_6463576 baseEnd_6463576 := by
    simpa [prefixWord, tailWord_6463576, baseEnd_6463576] using wordTrace_append hprefix tailTrace_6463576
  have hstable : (prefixWord ++ tailWord_6463576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463576).length < 2 ^ (prefixWord ++ tailWord_6463576).sum := by decide
  have hdescent : baseEnd_6463576 < baseStart_6463576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463596 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 5]
def baseStart_6463596 : Nat := 118140960795 + 6463596 * 2 ^ 59
def prefixEnd_6463596 : Nat := 4983230072969 + 3 ^ 40 * 6463596 * 2
def baseEnd_6463596 : Nat := 3318931504478398384624469

theorem tailTrace_6463596 : CollatzResearch.WordTrace tailWord_6463596 prefixEnd_6463596 3318931504478398384624469 := by
  unfold tailWord_6463596
  simp only [CollatzResearch.WordTrace]
  refine ⟨117873356745751530578197321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157164475661002040770929761 117873356745751530578197321)
  ·
    refine ⟨88405017559313647933647991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117873356745751530578197321 88405017559313647933647991)
    ·
      refine ⟨132607526338970471900471987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88405017559313647933647991 132607526338970471900471987)
      ·
        refine ⟨198911289508455707850707981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132607526338970471900471987 198911289508455707850707981)
        ·
          refine ⟨74591733565670890444015493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198911289508455707850707981 74591733565670890444015493)
          ·
            refine ⟨13985950043563291958252905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74591733565670890444015493 13985950043563291958252905)
            ·
              refine ⟨10489462532672468968689679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13985950043563291958252905 10489462532672468968689679)
              ·
                refine ⟨15734193799008703453034519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10489462532672468968689679 15734193799008703453034519)
                ·
                  refine ⟨23601290698513055179551779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15734193799008703453034519 23601290698513055179551779)
                  ·
                    refine ⟨35401936047769582769327669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23601290698513055179551779 35401936047769582769327669)
                    ·
                      refine ⟨3318931504478398384624469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35401936047769582769327669 3318931504478398384624469)
                      ·
                        rfl

theorem cell23_6463596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_6463596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463596 prefixEnd_6463596 := by exact prefixLift 6463596
  have htrace : WordTrace (prefixWord ++ tailWord_6463596) baseStart_6463596 baseEnd_6463596 := by
    simpa [prefixWord, tailWord_6463596, baseEnd_6463596] using wordTrace_append hprefix tailTrace_6463596
  have hstable : (prefixWord ++ tailWord_6463596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463596).length < 2 ^ (prefixWord ++ tailWord_6463596).sum := by decide
  have hdescent : baseEnd_6463596 < baseStart_6463596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463599 : List Nat := [1, 1, 2, 1, 3, 6, 9]
def baseStart_6463599 : Nat := 118140960795 + 6463599 * 2 ^ 59
def prefixEnd_6463599 : Nat := 4983230072969 + 3 ^ 40 * 6463599 * 2
def baseEnd_6463599 : Nat := 40974482036053850282555

theorem tailTrace_6463599 : CollatzResearch.WordTrace tailWord_6463599 prefixEnd_6463599 40974482036053850282555 := by
  unfold tailWord_6463599
  simp only [CollatzResearch.WordTrace]
  refine ⟨235746822910492192668753851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157164548606994795112502567 235746822910492192668753851)
  ·
    refine ⟨353620234365738289003130777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235746822910492192668753851 353620234365738289003130777)
    ·
      refine ⟨265215175774303716752348083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353620234365738289003130777 265215175774303716752348083)
      ·
        refine ⟨397822763661455575128522125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265215175774303716752348083 397822763661455575128522125)
        ·
          refine ⟨149183536373045840673195797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397822763661455575128522125 149183536373045840673195797)
          ·
            refine ⟨6992978267486523781556053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149183536373045840673195797 6992978267486523781556053)
            ·
              refine ⟨40974482036053850282555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6992978267486523781556053 40974482036053850282555)
              ·
                rfl

theorem cell23_6463599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 9].length) (baseStart_6463599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463599 prefixEnd_6463599 := by exact prefixLift 6463599
  have htrace : WordTrace (prefixWord ++ tailWord_6463599) baseStart_6463599 baseEnd_6463599 := by
    simpa [prefixWord, tailWord_6463599, baseEnd_6463599] using wordTrace_append hprefix tailTrace_6463599
  have hstable : (prefixWord ++ tailWord_6463599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463599).length < 2 ^ (prefixWord ++ tailWord_6463599).sum := by decide
  have hdescent : baseEnd_6463599 < baseStart_6463599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463606 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_6463606 : Nat := 118140960795 + 6463606 * 2 ^ 59
def prefixEnd_6463606 : Nat := 4983230072969 + 3 ^ 40 * 6463606 * 2
def baseEnd_6463606 : Nat := 3318936639284943345499423

theorem tailTrace_6463606 : CollatzResearch.WordTrace tailWord_6463606 prefixEnd_6463606 3318936639284943345499423 := by
  unfold tailWord_6463606
  simp only [CollatzResearch.WordTrace]
  refine ⟨14734192388841677054016167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157164718814311221909505781 14734192388841677054016167)
  ·
    refine ⟨22101288583262515581024251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14734192388841677054016167 22101288583262515581024251)
    ·
      refine ⟨33151932874893773371536377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22101288583262515581024251 33151932874893773371536377)
      ·
        refine ⟨24863949656170330028652283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33151932874893773371536377 24863949656170330028652283)
        ·
          refine ⟨37295924484255495042978425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24863949656170330028652283 37295924484255495042978425)
          ·
            refine ⟨27971943363191621282233819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37295924484255495042978425 27971943363191621282233819)
            ·
              refine ⟨41957915044787431923350729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27971943363191621282233819 41957915044787431923350729)
              ·
                refine ⟨31468436283590573942513047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41957915044787431923350729 31468436283590573942513047)
                ·
                  refine ⟨47202654425385860913769571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31468436283590573942513047 47202654425385860913769571)
                  ·
                    refine ⟨70803981638078791370654357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47202654425385860913769571 70803981638078791370654357)
                    ·
                      refine ⟨3318936639284943345499423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70803981638078791370654357 3318936639284943345499423)
                      ·
                        rfl

theorem cell23_6463606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_6463606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463606 prefixEnd_6463606 := by exact prefixLift 6463606
  have htrace : WordTrace (prefixWord ++ tailWord_6463606) baseStart_6463606 baseEnd_6463606 := by
    simpa [prefixWord, tailWord_6463606, baseEnd_6463606] using wordTrace_append hprefix tailTrace_6463606
  have hstable : (prefixWord ++ tailWord_6463606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463606).length < 2 ^ (prefixWord ++ tailWord_6463606).sum := by decide
  have hdescent : baseEnd_6463606 < baseStart_6463606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463661 : List Nat := [1, 5, 2, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_6463661 : Nat := 118140960795 + 6463661 * 2 ^ 59
def prefixEnd_6463661 : Nat := 4983230072969 + 3 ^ 40 * 6463661 * 2
def baseEnd_6463661 : Nat := 3318964880720940630311671

theorem tailTrace_6463661 : CollatzResearch.WordTrace tailWord_6463661 prefixEnd_6463661 3318964880720940630311671 := by
  unfold tailWord_6463661
  simp only [CollatzResearch.WordTrace]
  refine ⟨235749084236267577257510837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157166056157511718171673891 235749084236267577257510837)
  ·
    refine ⟨22101476647150085367891641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235749084236267577257510837 22101476647150085367891641)
    ·
      refine ⟨16576107485362564025918731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22101476647150085367891641 16576107485362564025918731)
      ·
        refine ⟨24864161228043846038878097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16576107485362564025918731 24864161228043846038878097)
        ·
          refine ⟨18648120921032884529158573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24864161228043846038878097 18648120921032884529158573)
          ·
            refine ⟨6993045345387331698434465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18648120921032884529158573 6993045345387331698434465)
            ·
              refine ⟨5244784009040498773825849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6993045345387331698434465 5244784009040498773825849)
              ·
                refine ⟨3933588006780374080369387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5244784009040498773825849 3933588006780374080369387)
                ·
                  refine ⟨5900382010170561120554081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3933588006780374080369387 5900382010170561120554081)
                  ·
                    refine ⟨4425286507627920840415561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5900382010170561120554081 4425286507627920840415561)
                    ·
                      refine ⟨3318964880720940630311671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425286507627920840415561 3318964880720940630311671)
                      ·
                        rfl

theorem cell23_6463661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_6463661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463661 prefixEnd_6463661 := by exact prefixLift 6463661
  have htrace : WordTrace (prefixWord ++ tailWord_6463661) baseStart_6463661 baseEnd_6463661 := by
    simpa [prefixWord, tailWord_6463661, baseEnd_6463661] using wordTrace_append hprefix tailTrace_6463661
  have hstable : (prefixWord ++ tailWord_6463661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463661).length < 2 ^ (prefixWord ++ tailWord_6463661).sum := by decide
  have hdescent : baseEnd_6463661 < baseStart_6463661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463717 : List Nat := [1, 3, 1, 4, 2, 1, 3, 2, 2, 2, 2]
def baseStart_6463717 : Nat := 118140960795 + 6463717 * 2 ^ 59
def prefixEnd_6463717 : Nat := 4983230072969 + 3 ^ 40 * 6463717 * 2
def baseEnd_6463717 : Nat := 3318993635637592411211413

theorem tailTrace_6463717 : CollatzResearch.WordTrace tailWord_6463717 prefixEnd_6463717 3318993635637592411211413 := by
  unfold tailWord_6463717
  simp only [CollatzResearch.WordTrace]
  refine ⟨235751126724064698821549405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157167417816043132547699603 235751126724064698821549405)
  ·
    refine ⟨88406672521524262058081027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235751126724064698821549405 88406672521524262058081027)
    ·
      refine ⟨132610008782286393087121541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88406672521524262058081027 132610008782286393087121541)
      ·
        refine ⟨24864376646678698703835289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132610008782286393087121541 24864376646678698703835289)
        ·
          refine ⟨18648282485009024027876467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24864376646678698703835289 18648282485009024027876467)
          ·
            refine ⟨27972423727513536041814701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18648282485009024027876467 27972423727513536041814701)
            ·
              refine ⟨10489658897817576015680513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27972423727513536041814701 10489658897817576015680513)
              ·
                refine ⟨7867244173363182011760385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10489658897817576015680513 7867244173363182011760385)
                ·
                  refine ⟨5900433130022386508820289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7867244173363182011760385 5900433130022386508820289)
                  ·
                    refine ⟨4425324847516789881615217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5900433130022386508820289 4425324847516789881615217)
                    ·
                      refine ⟨3318993635637592411211413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425324847516789881615217 3318993635637592411211413)
                      ·
                        rfl

theorem cell23_6463717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_6463717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463717 prefixEnd_6463717 := by exact prefixLift 6463717
  have htrace : WordTrace (prefixWord ++ tailWord_6463717) baseStart_6463717 baseEnd_6463717 := by
    simpa [prefixWord, tailWord_6463717, baseEnd_6463717] using wordTrace_append hprefix tailTrace_6463717
  have hstable : (prefixWord ++ tailWord_6463717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463717).length < 2 ^ (prefixWord ++ tailWord_6463717).sum := by decide
  have hdescent : baseEnd_6463717 < baseStart_6463717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463756 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_6463756 : Nat := 118140960795 + 6463756 * 2 ^ 59
def prefixEnd_6463756 : Nat := 4983230072969 + 3 ^ 40 * 6463756 * 2
def baseEnd_6463756 : Nat := 3319013661383117758623733

theorem tailTrace_6463756 : CollatzResearch.WordTrace tailWord_6463756 prefixEnd_6463756 3319013661383117758623733 := by
  unfold tailWord_6463756
  simp only [CollatzResearch.WordTrace]
  refine ⟨117876274585461704241109561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157168366113948938988146081 117876274585461704241109561)
  ·
    refine ⟨88407205939096278180832171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117876274585461704241109561 88407205939096278180832171)
    ·
      refine ⟨132610808908644417271248257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88407205939096278180832171 132610808908644417271248257)
      ·
        refine ⟨99458106681483312953436193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132610808908644417271248257 99458106681483312953436193)
        ·
          refine ⟨74593580011112484715077145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99458106681483312953436193 74593580011112484715077145)
          ·
            refine ⟨55945185008334363536307859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74593580011112484715077145 55945185008334363536307859)
            ·
              refine ⟨83917777512501545304461789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55945185008334363536307859 83917777512501545304461789)
              ·
                refine ⟨31469166567188079489173171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83917777512501545304461789 31469166567188079489173171)
                ·
                  refine ⟨47203749850782119233759757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31469166567188079489173171 47203749850782119233759757)
                  ·
                    refine ⟨17701406194043294712659909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47203749850782119233759757 17701406194043294712659909)
                    ·
                      refine ⟨3319013661383117758623733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17701406194043294712659909 3319013661383117758623733)
                      ·
                        rfl

theorem cell23_6463756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_6463756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463756 prefixEnd_6463756 := by exact prefixLift 6463756
  have htrace : WordTrace (prefixWord ++ tailWord_6463756) baseStart_6463756 baseEnd_6463756 := by
    simpa [prefixWord, tailWord_6463756, baseEnd_6463756] using wordTrace_append hprefix tailTrace_6463756
  have hstable : (prefixWord ++ tailWord_6463756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463756).length < 2 ^ (prefixWord ++ tailWord_6463756).sum := by decide
  have hdescent : baseEnd_6463756 < baseStart_6463756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463774 : List Nat := [4, 3, 2, 1, 1, 2, 3, 2, 5]
def baseStart_6463774 : Nat := 118140960795 + 6463774 * 2 ^ 59
def prefixEnd_6463774 : Nat := 4983230072969 + 3 ^ 40 * 6463774 * 2
def baseEnd_6463774 : Nat := 368780322670544298688739

theorem tailTrace_6463774 : CollatzResearch.WordTrace tailWord_6463774 prefixEnd_6463774 368780322670544298688739 := by
  unfold tailWord_6463774
  simp only [CollatzResearch.WordTrace]
  refine ⟨29469150710607274694546797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157168803789905465037582917 29469150710607274694546797)
  ·
    refine ⟨11050931516477728010455049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29469150710607274694546797 11050931516477728010455049)
    ·
      refine ⟨8288198637358296007841287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11050931516477728010455049 8288198637358296007841287)
      ·
        refine ⟨12432297956037444011761931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8288198637358296007841287 12432297956037444011761931)
        ·
          refine ⟨18648446934056166017642897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12432297956037444011761931 18648446934056166017642897)
          ·
            refine ⟨13986335200542124513232173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18648446934056166017642897 13986335200542124513232173)
            ·
              refine ⟨5244875700203296692462065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13986335200542124513232173 5244875700203296692462065)
              ·
                refine ⟨3933656775152472519346549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5244875700203296692462065 3933656775152472519346549)
                ·
                  refine ⟨368780322670544298688739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3933656775152472519346549 368780322670544298688739)
                  ·
                    rfl

theorem cell23_6463774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_6463774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463774 prefixEnd_6463774 := by exact prefixLift 6463774
  have htrace : WordTrace (prefixWord ++ tailWord_6463774) baseStart_6463774 baseEnd_6463774 := by
    simpa [prefixWord, tailWord_6463774, baseEnd_6463774] using wordTrace_append hprefix tailTrace_6463774
  have hstable : (prefixWord ++ tailWord_6463774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463774).length < 2 ^ (prefixWord ++ tailWord_6463774).sum := by decide
  have hdescent : baseEnd_6463774 < baseStart_6463774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463823 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 7, 1, 3]
def baseStart_6463823 : Nat := 118140960795 + 6463823 * 2 ^ 59
def prefixEnd_6463823 : Nat := 4983230072969 + 3 ^ 40 * 6463823 * 2
def baseEnd_6463823 : Nat := 3319048064586968996485925

theorem tailTrace_6463823 : CollatzResearch.WordTrace tailWord_6463823 prefixEnd_6463823 3319048064586968996485925 := by
  unfold tailWord_6463823
  simp only [CollatzResearch.WordTrace]
  refine ⟨235754992861680678924908123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157169995241120452616605415 235754992861680678924908123)
  ·
    refine ⟨353632489292521018387362185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235754992861680678924908123 353632489292521018387362185)
    ·
      refine ⟨265224366969390763790521639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353632489292521018387362185 265224366969390763790521639)
      ·
        refine ⟨397836550454086145685782459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265224366969390763790521639 397836550454086145685782459)
        ·
          refine ⟨596754825681129218528673689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397836550454086145685782459 596754825681129218528673689)
          ·
            refine ⟨447566119260846913896505267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 596754825681129218528673689 447566119260846913896505267)
            ·
              refine ⟨671349178891270370844757901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447566119260846913896505267 671349178891270370844757901)
              ·
                refine ⟨251755942084226389066784213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 671349178891270370844757901 251755942084226389066784213)
                ·
                  refine ⟨5900529892599055993752755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 251755942084226389066784213 5900529892599055993752755)
                  ·
                    refine ⟨8850794838898583990629133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5900529892599055993752755 8850794838898583990629133)
                    ·
                      refine ⟨3319048064586968996485925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8850794838898583990629133 3319048064586968996485925)
                      ·
                        rfl

theorem cell23_6463823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 1, 3].length) (baseStart_6463823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463823 prefixEnd_6463823 := by exact prefixLift 6463823
  have htrace : WordTrace (prefixWord ++ tailWord_6463823) baseStart_6463823 baseEnd_6463823 := by
    simpa [prefixWord, tailWord_6463823, baseEnd_6463823] using wordTrace_append hprefix tailTrace_6463823
  have hstable : (prefixWord ++ tailWord_6463823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463823).length < 2 ^ (prefixWord ++ tailWord_6463823).sum := by decide
  have hdescent : baseEnd_6463823 < baseStart_6463823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463833 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 3, 5, 2]
def baseStart_6463833 : Nat := 118140960795 + 6463833 * 2 ^ 59
def prefixEnd_6463833 : Nat := 4983230072969 + 3 ^ 40 * 6463833 * 2
def baseEnd_6463833 : Nat := 3319053199393513957360879

theorem tailTrace_6463833 : CollatzResearch.WordTrace tailWord_6463833 prefixEnd_6463833 3319053199393513957360879 := by
  unfold tailWord_6463833
  simp only [CollatzResearch.WordTrace]
  refine ⟨235755357591644450632772153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157170238394429633755181435 235755357591644450632772153)
  ·
    refine ⟨176816518193733337974579115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235755357591644450632772153 176816518193733337974579115)
    ·
      refine ⟨265224777290600006961868673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176816518193733337974579115 265224777290600006961868673)
      ·
        refine ⟨198918582967950005221401505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265224777290600006961868673 198918582967950005221401505)
        ·
          refine ⟨149188937225962503916051129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198918582967950005221401505 149188937225962503916051129)
          ·
            refine ⟨111891702919471877937038347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149188937225962503916051129 111891702919471877937038347)
            ·
              refine ⟨167837554379207816905557521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111891702919471877937038347 167837554379207816905557521)
              ·
                refine ⟨125878165784405862679168141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167837554379207816905557521 125878165784405862679168141)
                ·
                  refine ⟨47204312169152198504688053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125878165784405862679168141 47204312169152198504688053)
                  ·
                    refine ⟨4425404265858018609814505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47204312169152198504688053 4425404265858018609814505)
                    ·
                      refine ⟨3319053199393513957360879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425404265858018609814505 3319053199393513957360879)
                      ·
                        rfl

theorem cell23_6463833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 5, 2].length) (baseStart_6463833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463833 prefixEnd_6463833 := by exact prefixLift 6463833
  have htrace : WordTrace (prefixWord ++ tailWord_6463833) baseStart_6463833 baseEnd_6463833 := by
    simpa [prefixWord, tailWord_6463833, baseEnd_6463833] using wordTrace_append hprefix tailTrace_6463833
  have hstable : (prefixWord ++ tailWord_6463833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463833).length < 2 ^ (prefixWord ++ tailWord_6463833).sum := by decide
  have hdescent : baseEnd_6463833 < baseStart_6463833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463863 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 1, 8, 2]
def baseStart_6463863 : Nat := 118140960795 + 6463863 * 2 ^ 59
def prefixEnd_6463863 : Nat := 4983230072969 + 3 ^ 40 * 6463863 * 2
def baseEnd_6463863 : Nat := 3319068603813148839985741

theorem tailTrace_6463863 : CollatzResearch.WordTrace tailWord_6463863 prefixEnd_6463863 3319068603813148839985741 := by
  unfold tailWord_6463863
  simp only [CollatzResearch.WordTrace]
  refine ⟨235756451781535765756364243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157170967854357177170909495 235756451781535765756364243)
  ·
    refine ⟨353634677672303648634546365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235756451781535765756364243 353634677672303648634546365)
    ·
      refine ⟨132613004127113868237954887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353634677672303648634546365 132613004127113868237954887)
      ·
        refine ⟨198919506190670802356932331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132613004127113868237954887 198919506190670802356932331)
        ·
          refine ⟨298379259286006203535398497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198919506190670802356932331 298379259286006203535398497)
          ·
            refine ⟨223784444464504652651548873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298379259286006203535398497 223784444464504652651548873)
            ·
              refine ⟨167838333348378489488661655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223784444464504652651548873 167838333348378489488661655)
              ·
                refine ⟨251757500022567734232992483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167838333348378489488661655 251757500022567734232992483)
                ·
                  refine ⟨377636250033851601349488725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251757500022567734232992483 377636250033851601349488725)
                  ·
                    refine ⟨4425424805084198453314321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 377636250033851601349488725 4425424805084198453314321)
                    ·
                      refine ⟨3319068603813148839985741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425424805084198453314321 3319068603813148839985741)
                      ·
                        rfl

theorem cell23_6463863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 8, 2].length) (baseStart_6463863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463863 prefixEnd_6463863 := by exact prefixLift 6463863
  have htrace : WordTrace (prefixWord ++ tailWord_6463863) baseStart_6463863 baseEnd_6463863 := by
    simpa [prefixWord, tailWord_6463863, baseEnd_6463863] using wordTrace_append hprefix tailTrace_6463863
  have hstable : (prefixWord ++ tailWord_6463863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463863).length < 2 ^ (prefixWord ++ tailWord_6463863).sum := by decide
  have hdescent : baseEnd_6463863 < baseStart_6463863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463866 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_6463866 : Nat := 118140960795 + 6463866 * 2 ^ 59
def prefixEnd_6463866 : Nat := 4983230072969 + 3 ^ 40 * 6463866 * 2
def baseEnd_6463866 : Nat := 3319070144255112328248227

theorem tailTrace_6463866 : CollatzResearch.WordTrace tailWord_6463866 prefixEnd_6463866 3319070144255112328248227 := by
  unfold tailWord_6463866
  simp only [CollatzResearch.WordTrace]
  refine ⟨58939140300131224317180863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157171040800349931512482301 58939140300131224317180863)
  ·
    refine ⟨88408710450196836475771295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58939140300131224317180863 88408710450196836475771295)
    ·
      refine ⟨132613065675295254713656943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88408710450196836475771295 132613065675295254713656943)
      ·
        refine ⟨198919598512942882070485415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132613065675295254713656943 198919598512942882070485415)
        ·
          refine ⟨298379397769414323105728123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198919598512942882070485415 298379397769414323105728123)
          ·
            refine ⟨447569096654121484658592185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298379397769414323105728123 447569096654121484658592185)
            ·
              refine ⟨335676822490591113493944139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447569096654121484658592185 335676822490591113493944139)
              ·
                refine ⟨503515233735886670240916209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335676822490591113493944139 503515233735886670240916209)
                ·
                  refine ⟨377636425301915002680687157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503515233735886670240916209 377636425301915002680687157)
                  ·
                    refine ⟨35403414872054531501314421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 377636425301915002680687157 35403414872054531501314421)
                    ·
                      refine ⟨3319070144255112328248227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35403414872054531501314421 3319070144255112328248227)
                      ·
                        rfl

theorem cell23_6463866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_6463866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463866 prefixEnd_6463866 := by exact prefixLift 6463866
  have htrace : WordTrace (prefixWord ++ tailWord_6463866) baseStart_6463866 baseEnd_6463866 := by
    simpa [prefixWord, tailWord_6463866, baseEnd_6463866] using wordTrace_append hprefix tailTrace_6463866
  have hstable : (prefixWord ++ tailWord_6463866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463866).length < 2 ^ (prefixWord ++ tailWord_6463866).sum := by decide
  have hdescent : baseEnd_6463866 < baseStart_6463866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463867 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 2, 3, 2]
def baseStart_6463867 : Nat := 118140960795 + 6463867 * 2 ^ 59
def prefixEnd_6463867 : Nat := 4983230072969 + 3 ^ 40 * 6463867 * 2
def baseEnd_6463867 : Nat := 3319070657735766824335723

theorem tailTrace_6463867 : CollatzResearch.WordTrace tailWord_6463867 prefixEnd_6463867 3319070657735766824335723 := by
  unfold tailWord_6463867
  simp only [CollatzResearch.WordTrace]
  refine ⟨235756597673521274439509855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157171065115680849626339903 235756597673521274439509855)
  ·
    refine ⟨353634896510281911659264783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235756597673521274439509855 353634896510281911659264783)
    ·
      refine ⟨530452344765422867488897175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353634896510281911659264783 530452344765422867488897175)
      ·
        refine ⟨795678517148134301233345763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530452344765422867488897175 795678517148134301233345763)
        ·
          refine ⟨1193517775722201451850018645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795678517148134301233345763 1193517775722201451850018645)
          ·
            refine ⟨6993268217122274131933703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1193517775722201451850018645 6993268217122274131933703)
            ·
              refine ⟨10489902325683411197900555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6993268217122274131933703 10489902325683411197900555)
              ·
                refine ⟨15734853488525116796850833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10489902325683411197900555 15734853488525116796850833)
                ·
                  refine ⟨11801140116393837597638125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15734853488525116796850833 11801140116393837597638125)
                  ·
                    refine ⟨4425427543647689099114297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11801140116393837597638125 4425427543647689099114297)
                    ·
                      refine ⟨3319070657735766824335723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425427543647689099114297 3319070657735766824335723)
                      ·
                        rfl

theorem cell23_6463867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 3, 2].length) (baseStart_6463867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463867 prefixEnd_6463867 := by exact prefixLift 6463867
  have htrace : WordTrace (prefixWord ++ tailWord_6463867) baseStart_6463867 baseEnd_6463867 := by
    simpa [prefixWord, tailWord_6463867, baseEnd_6463867] using wordTrace_append hprefix tailTrace_6463867
  have hstable : (prefixWord ++ tailWord_6463867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463867).length < 2 ^ (prefixWord ++ tailWord_6463867).sum := by decide
  have hdescent : baseEnd_6463867 < baseStart_6463867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463880 : List Nat := [2, 1, 3, 3, 1, 1, 3, 3, 1, 1, 4]
def baseStart_6463880 : Nat := 118140960795 + 6463880 * 2 ^ 59
def prefixEnd_6463880 : Nat := 4983230072969 + 3 ^ 40 * 6463880 * 2
def baseEnd_6463880 : Nat := 3319077332984275273473163

theorem tailTrace_6463880 : CollatzResearch.WordTrace tailWord_6463880 prefixEnd_6463880 3319077332984275273473163 := by
  unfold tailWord_6463880
  simp only [CollatzResearch.WordTrace]
  refine ⟨117878535911237088829866547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157171381214982785106488729 117878535911237088829866547)
  ·
    refine ⟨176817803866855633244799821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117878535911237088829866547 176817803866855633244799821)
    ·
      refine ⟨66306676450070862466799933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176817803866855633244799821 66306676450070862466799933)
      ·
        refine ⟨24865003668776573425049975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66306676450070862466799933 24865003668776573425049975)
        ·
          refine ⟨37297505503164860137574963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24865003668776573425049975 37297505503164860137574963)
          ·
            refine ⟨55946258254747290206362445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37297505503164860137574963 55946258254747290206362445)
            ·
              refine ⟨20979846845530233827385917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55946258254747290206362445 20979846845530233827385917)
              ·
                refine ⟨7867442567073837685269719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20979846845530233827385917 7867442567073837685269719)
                ·
                  refine ⟨11801163850610756527904579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7867442567073837685269719 11801163850610756527904579)
                  ·
                    refine ⟨17701745775916134791856869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11801163850610756527904579 17701745775916134791856869)
                    ·
                      refine ⟨3319077332984275273473163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17701745775916134791856869 3319077332984275273473163)
                      ·
                        rfl

theorem cell23_6463880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_6463880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463880 prefixEnd_6463880 := by exact prefixLift 6463880
  have htrace : WordTrace (prefixWord ++ tailWord_6463880) baseStart_6463880 baseEnd_6463880 := by
    simpa [prefixWord, tailWord_6463880, baseEnd_6463880] using wordTrace_append hprefix tailTrace_6463880
  have hstable : (prefixWord ++ tailWord_6463880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463880).length < 2 ^ (prefixWord ++ tailWord_6463880).sum := by decide
  have hdescent : baseEnd_6463880 < baseStart_6463880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463897 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 3, 2, 2]
def baseStart_6463897 : Nat := 118140960795 + 6463897 * 2 ^ 59
def prefixEnd_6463897 : Nat := 4983230072969 + 3 ^ 40 * 6463897 * 2
def baseEnd_6463897 : Nat := 3319086062155401706960585

theorem tailTrace_6463897 : CollatzResearch.WordTrace tailWord_6463897 prefixEnd_6463897 3319086062155401706960585 := by
  unfold tailWord_6463897
  simp only [CollatzResearch.WordTrace]
  refine ⟨235757691863412589563101945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157171794575608393042067963 235757691863412589563101945)
  ·
    refine ⟨176818268897559442172326459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235757691863412589563101945 176818268897559442172326459)
    ·
      refine ⟨265227403346339163258489689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176818268897559442172326459 265227403346339163258489689)
      ·
        refine ⟨198920552509754372443867267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265227403346339163258489689 198920552509754372443867267)
        ·
          refine ⟨298380828764631558665800901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198920552509754372443867267 298380828764631558665800901)
          ·
            refine ⟨55946405393368417249837669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 298380828764631558665800901 55946405393368417249837669)
            ·
              refine ⟨10489951011256578234344563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55946405393368417249837669 10489951011256578234344563)
              ·
                refine ⟨15734926516884867351516845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10489951011256578234344563 15734926516884867351516845)
                ·
                  refine ⟨5900597443831825256818817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15734926516884867351516845 5900597443831825256818817)
                  ·
                    refine ⟨4425448082873868942614113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5900597443831825256818817 4425448082873868942614113)
                    ·
                      refine ⟨3319086062155401706960585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425448082873868942614113 3319086062155401706960585)
                      ·
                        rfl

theorem cell23_6463897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 2, 2].length) (baseStart_6463897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463897 prefixEnd_6463897 := by exact prefixLift 6463897
  have htrace : WordTrace (prefixWord ++ tailWord_6463897) baseStart_6463897 baseEnd_6463897 := by
    simpa [prefixWord, tailWord_6463897, baseEnd_6463897] using wordTrace_append hprefix tailTrace_6463897
  have hstable : (prefixWord ++ tailWord_6463897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463897).length < 2 ^ (prefixWord ++ tailWord_6463897).sum := by decide
  have hdescent : baseEnd_6463897 < baseStart_6463897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463907 : List Nat := [1, 1, 1, 4, 1, 5, 3, 1, 2, 4]
def baseStart_6463907 : Nat := 118140960795 + 6463907 * 2 ^ 59
def prefixEnd_6463907 : Nat := 4983230072969 + 3 ^ 40 * 6463907 * 2
def baseEnd_6463907 : Nat := 1106363732320648889278513

theorem tailTrace_6463907 : CollatzResearch.WordTrace tailWord_6463907 prefixEnd_6463907 1106363732320648889278513 := by
  unfold tailWord_6463907
  simp only [CollatzResearch.WordTrace]
  refine ⟨235758056593376361270965975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157172037728917574180643983 235758056593376361270965975)
  ·
    refine ⟨353637084890064541906448963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235758056593376361270965975 353637084890064541906448963)
    ·
      refine ⟨530455627335096812859673445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353637084890064541906448963 530455627335096812859673445)
      ·
        refine ⟨99460430125330652411188771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 530455627335096812859673445 99460430125330652411188771)
        ·
          refine ⟨149190645187995978616783157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99460430125330652411188771 149190645187995978616783157)
          ·
            refine ⟨13986622986374622995323421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149190645187995978616783157 13986622986374622995323421)
            ·
              refine ⟨5244983619890483623246283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13986622986374622995323421 5244983619890483623246283)
              ·
                refine ⟨7867475429835725434869425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5244983619890483623246283 7867475429835725434869425)
                ·
                  refine ⟨5900606572376794076152069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7867475429835725434869425 5900606572376794076152069)
                  ·
                    refine ⟨1106363732320648889278513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5900606572376794076152069 1106363732320648889278513)
                    ·
                      rfl

theorem cell23_6463907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 2, 4].length) (baseStart_6463907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463907 prefixEnd_6463907 := by exact prefixLift 6463907
  have htrace : WordTrace (prefixWord ++ tailWord_6463907) baseStart_6463907 baseEnd_6463907 := by
    simpa [prefixWord, tailWord_6463907, baseEnd_6463907] using wordTrace_append hprefix tailTrace_6463907
  have hstable : (prefixWord ++ tailWord_6463907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463907).length < 2 ^ (prefixWord ++ tailWord_6463907).sum := by decide
  have hdescent : baseEnd_6463907 < baseStart_6463907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463948 : List Nat := [2, 2, 1, 4, 3, 1, 3, 2, 1, 2, 2]
def baseStart_6463948 : Nat := 118140960795 + 6463948 * 2 ^ 59
def prefixEnd_6463948 : Nat := 4983230072969 + 3 ^ 40 * 6463948 * 2
def baseEnd_6463948 : Nat := 3319112249668781007422851

theorem tailTrace_6463948 : CollatzResearch.WordTrace tailWord_6463948 prefixEnd_6463948 3319112249668781007422851 := by
  unfold tailWord_6463948
  simp only [CollatzResearch.WordTrace]
  refine ⟨117879775993113912636604249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157173034657485216848805665 117879775993113912636604249)
  ·
    refine ⟨88409831994835434477453187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117879775993113912636604249 88409831994835434477453187)
    ·
      refine ⟨132614747992253151716179781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88409831994835434477453187 132614747992253151716179781)
      ·
        refine ⟨24865265248547465946783709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132614747992253151716179781 24865265248547465946783709)
        ·
          refine ⟨9324474468205299730043891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24865265248547465946783709 9324474468205299730043891)
          ·
            refine ⟨13986711702307949595065837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9324474468205299730043891 13986711702307949595065837)
            ·
              refine ⟨5245016888365481098149689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13986711702307949595065837 5245016888365481098149689)
              ·
                refine ⟨3933762666274110823612267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5245016888365481098149689 3933762666274110823612267)
                ·
                  refine ⟨5900643999411166235418401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3933762666274110823612267 5900643999411166235418401)
                  ·
                    refine ⟨4425482999558374676563801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5900643999411166235418401 4425482999558374676563801)
                    ·
                      refine ⟨3319112249668781007422851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425482999558374676563801 3319112249668781007422851)
                      ·
                        rfl

theorem cell23_6463948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_6463948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463948 prefixEnd_6463948 := by exact prefixLift 6463948
  have htrace : WordTrace (prefixWord ++ tailWord_6463948) baseStart_6463948 baseEnd_6463948 := by
    simpa [prefixWord, tailWord_6463948, baseEnd_6463948] using wordTrace_append hprefix tailTrace_6463948
  have hstable : (prefixWord ++ tailWord_6463948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463948).length < 2 ^ (prefixWord ++ tailWord_6463948).sum := by decide
  have hdescent : baseEnd_6463948 < baseStart_6463948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463983 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 4]
def baseStart_6463983 : Nat := 118140960795 + 6463983 * 2 ^ 59
def prefixEnd_6463983 : Nat := 4983230072969 + 3 ^ 40 * 6463983 * 2
def baseEnd_6463983 : Nat := 3319130221491688370485189

theorem tailTrace_6463983 : CollatzResearch.WordTrace tailWord_6463983 prefixEnd_6463983 3319130221491688370485189 := by
  unfold tailWord_6463983
  simp only [CollatzResearch.WordTrace]
  refine ⟨235760828541101026250732603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157173885694067350833821735 235760828541101026250732603)
  ·
    refine ⟨353641242811651539376098905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235760828541101026250732603 353641242811651539376098905)
    ·
      refine ⟨265230932108738654532074179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353641242811651539376098905 265230932108738654532074179)
      ·
        refine ⟨397846398163107981798111269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265230932108738654532074179 397846398163107981798111269)
        ·
          refine ⟨74596199655582746587145863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397846398163107981798111269 74596199655582746587145863)
          ·
            refine ⟨111894299483374119880718795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74596199655582746587145863 111894299483374119880718795)
            ·
              refine ⟨167841449225061179821078193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111894299483374119880718795 167841449225061179821078193)
              ·
                refine ⟨125881086918795884865808645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167841449225061179821078193 125881086918795884865808645)
                ·
                  refine ⟨23602703797274228412339121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125881086918795884865808645 23602703797274228412339121)
                  ·
                    refine ⟨17702027847955671309254341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23602703797274228412339121 17702027847955671309254341)
                    ·
                      refine ⟨3319130221491688370485189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17702027847955671309254341 3319130221491688370485189)
                      ·
                        rfl

theorem cell23_6463983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_6463983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463983 prefixEnd_6463983 := by exact prefixLift 6463983
  have htrace : WordTrace (prefixWord ++ tailWord_6463983) baseStart_6463983 baseEnd_6463983 := by
    simpa [prefixWord, tailWord_6463983, baseEnd_6463983] using wordTrace_append hprefix tailTrace_6463983
  have hstable : (prefixWord ++ tailWord_6463983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463983).length < 2 ^ (prefixWord ++ tailWord_6463983).sum := by decide
  have hdescent : baseEnd_6463983 < baseStart_6463983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6463990 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_6463990 : Nat := 118140960795 + 6463990 * 2 ^ 59
def prefixEnd_6463990 : Nat := 4983230072969 + 3 ^ 40 * 6463990 * 2
def baseEnd_6463990 : Nat := 3319133815856269843097657

theorem tailTrace_6463990 : CollatzResearch.WordTrace tailWord_6463990 prefixEnd_6463990 3319133815856269843097657 := by
  unfold tailWord_6463990
  simp only [CollatzResearch.WordTrace]
  refine ⟨14735067740754729152889839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157174055901383777630824949 14735067740754729152889839)
  ·
    refine ⟨22102601611132093729334759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14735067740754729152889839 22102601611132093729334759)
    ·
      refine ⟨33153902416698140594002139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22102601611132093729334759 33153902416698140594002139)
      ·
        refine ⟨49730853625047210891003209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33153902416698140594002139 49730853625047210891003209)
        ·
          refine ⟨37298140218785408168252407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49730853625047210891003209 37298140218785408168252407)
          ·
            refine ⟨55947210328178112252378611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37298140218785408168252407 55947210328178112252378611)
            ·
              refine ⟨83920815492267168378567917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55947210328178112252378611 83920815492267168378567917)
              ·
                refine ⟨31470305809600188141962969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83920815492267168378567917 31470305809600188141962969)
                ·
                  refine ⟨23602729357200141106472227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31470305809600188141962969 23602729357200141106472227)
                  ·
                    refine ⟨35404094035800211659708341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23602729357200141106472227 35404094035800211659708341)
                    ·
                      refine ⟨3319133815856269843097657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35404094035800211659708341 3319133815856269843097657)
                      ·
                        rfl

theorem cell23_6463990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_6463990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6463990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6463990 prefixEnd_6463990 := by exact prefixLift 6463990
  have htrace : WordTrace (prefixWord ++ tailWord_6463990) baseStart_6463990 baseEnd_6463990 := by
    simpa [prefixWord, tailWord_6463990, baseEnd_6463990] using wordTrace_append hprefix tailTrace_6463990
  have hstable : (prefixWord ++ tailWord_6463990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6463990).length < 2 ^ (prefixWord ++ tailWord_6463990).sum := by decide
  have hdescent : baseEnd_6463990 < baseStart_6463990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6463990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464077 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_6464077 : Nat := 118140960795 + 6464077 * 2 ^ 59
def prefixEnd_6464077 : Nat := 4983230072969 + 3 ^ 40 * 6464077 * 2
def baseEnd_6464077 : Nat := 3319178488673211002709757

theorem tailTrace_6464077 : CollatzResearch.WordTrace tailWord_6464077 prefixEnd_6464077 3319178488673211002709757 := by
  unfold tailWord_6464077
  simp only [CollatzResearch.WordTrace]
  refine ⟨235764257002760480304654485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157176171335173653536436323 235764257002760480304654485)
  ·
    refine ⟨11051449547004397514280679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 235764257002760480304654485 11051449547004397514280679)
    ·
      refine ⟨16577174320506596271421019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11051449547004397514280679 16577174320506596271421019)
      ·
        refine ⟨24865761480759894407131529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16577174320506596271421019 24865761480759894407131529)
        ·
          refine ⟨18649321110569920805348647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24865761480759894407131529 18649321110569920805348647)
          ·
            refine ⟨27973981665854881208022971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18649321110569920805348647 27973981665854881208022971)
            ·
              refine ⟨41960972498782321812034457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27973981665854881208022971 41960972498782321812034457)
              ·
                refine ⟨31470729374086741359025843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41960972498782321812034457 31470729374086741359025843)
                ·
                  refine ⟨47206094061130112038538765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31470729374086741359025843 47206094061130112038538765)
                  ·
                    refine ⟨17702285272923792014452037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47206094061130112038538765 17702285272923792014452037)
                    ·
                      refine ⟨3319178488673211002709757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17702285272923792014452037 3319178488673211002709757)
                      ·
                        rfl

theorem cell23_6464077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_6464077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464077 prefixEnd_6464077 := by exact prefixLift 6464077
  have htrace : WordTrace (prefixWord ++ tailWord_6464077) baseStart_6464077 baseEnd_6464077 := by
    simpa [prefixWord, tailWord_6464077, baseEnd_6464077] using wordTrace_append hprefix tailTrace_6464077
  have hstable : (prefixWord ++ tailWord_6464077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464077).length < 2 ^ (prefixWord ++ tailWord_6464077).sum := by decide
  have hdescent : baseEnd_6464077 < baseStart_6464077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464080 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 3]
def baseStart_6464080 : Nat := 118140960795 + 6464080 * 2 ^ 59
def prefixEnd_6464080 : Nat := 4983230072969 + 3 ^ 40 * 6464080 * 2
def baseEnd_6464080 : Nat := 3319180029115174490972243

theorem tailTrace_6464080 : CollatzResearch.WordTrace tailWord_6464080 prefixEnd_6464080 3319180029115174490972243 := by
  unfold tailWord_6464080
  simp only [CollatzResearch.WordTrace]
  refine ⟨117882183210874805908506847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157176244281166407878009129 117882183210874805908506847)
  ·
    refine ⟨176823274816312208862760271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117882183210874805908506847 176823274816312208862760271)
    ·
      refine ⟨265234912224468313294140407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176823274816312208862760271 265234912224468313294140407)
      ·
        refine ⟨397852368336702469941210611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265234912224468313294140407 397852368336702469941210611)
        ·
          refine ⟨596778552505053704911815917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397852368336702469941210611 596778552505053704911815917)
          ·
            refine ⟨223791957189395139341930969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 596778552505053704911815917 223791957189395139341930969)
            ·
              refine ⟨167843967892046354506448227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223791957189395139341930969 167843967892046354506448227)
              ·
                refine ⟨251765951838069531759672341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167843967892046354506448227 251765951838069531759672341)
                ·
                  refine ⟨11801528992409509301234641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 251765951838069531759672341 11801528992409509301234641)
                  ·
                    refine ⟨8851146744307131975925981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11801528992409509301234641 8851146744307131975925981)
                    ·
                      refine ⟨3319180029115174490972243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8851146744307131975925981 3319180029115174490972243)
                      ·
                        rfl

theorem cell23_6464080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 3].length) (baseStart_6464080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464080 prefixEnd_6464080 := by exact prefixLift 6464080
  have htrace : WordTrace (prefixWord ++ tailWord_6464080) baseStart_6464080 baseEnd_6464080 := by
    simpa [prefixWord, tailWord_6464080, baseEnd_6464080] using wordTrace_append hprefix tailTrace_6464080
  have hstable : (prefixWord ++ tailWord_6464080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464080).length < 2 ^ (prefixWord ++ tailWord_6464080).sum := by decide
  have hdescent : baseEnd_6464080 < baseStart_6464080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464114 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_6464114 : Nat := 118140960795 + 6464114 * 2 ^ 59
def prefixEnd_6464114 : Nat := 4983230072969 + 3 ^ 40 * 6464114 * 2
def baseEnd_6464114 : Nat := 3319197487457427357947087

theorem tailTrace_6464114 : CollatzResearch.WordTrace tailWord_6464114 prefixEnd_6464114 3319197487457427357947087 := by
  unfold tailWord_6464114
  simp only [CollatzResearch.WordTrace]
  refine ⟨58941401625906608905937849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157177071002417623749167597 58941401625906608905937849)
  ·
    refine ⟨44206051219429956679453387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58941401625906608905937849 44206051219429956679453387)
    ·
      refine ⟨66309076829144935019180081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44206051219429956679453387 66309076829144935019180081)
      ·
        refine ⟨49731807621858701264385061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66309076829144935019180081 49731807621858701264385061)
        ·
          refine ⟨9324713929098506487072199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49731807621858701264385061 9324713929098506487072199)
          ·
            refine ⟨13987070893647759730608299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9324713929098506487072199 13987070893647759730608299)
            ·
              refine ⟨20980606340471639595912449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13987070893647759730608299 20980606340471639595912449)
              ·
                refine ⟨15735454755353729696934337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20980606340471639595912449 15735454755353729696934337)
                ·
                  refine ⟨11801591066515297272700753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15735454755353729696934337 11801591066515297272700753)
                  ·
                    refine ⟨8851193299886472954525565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11801591066515297272700753 8851193299886472954525565)
                    ·
                      refine ⟨3319197487457427357947087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8851193299886472954525565 3319197487457427357947087)
                      ·
                        rfl

theorem cell23_6464114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_6464114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464114 prefixEnd_6464114 := by exact prefixLift 6464114
  have htrace : WordTrace (prefixWord ++ tailWord_6464114) baseStart_6464114 baseEnd_6464114 := by
    simpa [prefixWord, tailWord_6464114, baseEnd_6464114] using wordTrace_append hprefix tailTrace_6464114
  have hstable : (prefixWord ++ tailWord_6464114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464114).length < 2 ^ (prefixWord ++ tailWord_6464114).sum := by decide
  have hdescent : baseEnd_6464114 < baseStart_6464114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464121 : List Nat := [1, 2, 1, 3, 3, 3, 3, 2, 1, 4]
def baseStart_6464121 : Nat := 118140960795 + 6464121 * 2 ^ 59
def prefixEnd_6464121 : Nat := 4983230072969 + 3 ^ 40 * 6464121 * 2
def baseEnd_6464121 : Nat := 1106400360607336276853185

theorem tailTrace_6464121 : CollatzResearch.WordTrace tailWord_6464121 prefixEnd_6464121 1106400360607336276853185 := by
  unfold tailWord_6464121
  simp only [CollatzResearch.WordTrace]
  refine ⟨235765861814601075819256217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157177241209734050546170811 235765861814601075819256217)
  ·
    refine ⟨176824396360950806864442163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235765861814601075819256217 176824396360950806864442163)
    ·
      refine ⟨265236594541426210296663245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176824396360950806864442163 265236594541426210296663245)
      ·
        refine ⟨99463722953034828861248717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265236594541426210296663245 99463722953034828861248717)
        ·
          refine ⟨37298896107388060822968269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99463722953034828861248717 37298896107388060822968269)
          ·
            refine ⟨13987086040270522808613101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37298896107388060822968269 13987086040270522808613101)
            ·
              refine ⟨5245157265101446053229913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13987086040270522808613101 5245157265101446053229913)
              ·
                refine ⟨3933867948826084539922435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5245157265101446053229913 3933867948826084539922435)
                ·
                  refine ⟨5900801923239126809883653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3933867948826084539922435 5900801923239126809883653)
                  ·
                    refine ⟨1106400360607336276853185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5900801923239126809883653 1106400360607336276853185)
                    ·
                      rfl

theorem cell23_6464121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 1, 4].length) (baseStart_6464121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464121 prefixEnd_6464121 := by exact prefixLift 6464121
  have htrace : WordTrace (prefixWord ++ tailWord_6464121) baseStart_6464121 baseEnd_6464121 := by
    simpa [prefixWord, tailWord_6464121, baseEnd_6464121] using wordTrace_append hprefix tailTrace_6464121
  have hstable : (prefixWord ++ tailWord_6464121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464121).length < 2 ^ (prefixWord ++ tailWord_6464121).sum := by decide
  have hdescent : baseEnd_6464121 < baseStart_6464121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464127 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 3, 1, 3]
def baseStart_6464127 : Nat := 118140960795 + 6464127 * 2 ^ 59
def prefixEnd_6464127 : Nat := 4983230072969 + 3 ^ 40 * 6464127 * 2
def baseEnd_6464127 : Nat := 3319204162705935807084527

theorem tailTrace_6464127 : CollatzResearch.WordTrace tailWord_6464127 prefixEnd_6464127 3319204162705935807084527 := by
  unfold tailWord_6464127
  simp only [CollatzResearch.WordTrace]
  refine ⟨235766080652579338843974635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157177387101719559229316423 235766080652579338843974635)
  ·
    refine ⟨353649120978869008265961953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235766080652579338843974635 353649120978869008265961953)
    ·
      refine ⟨265236840734151756199471465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353649120978869008265961953 265236840734151756199471465)
      ·
        refine ⟨198927630550613817149603599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265236840734151756199471465 198927630550613817149603599)
        ·
          refine ⟨298391445825920725724405399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198927630550613817149603599 298391445825920725724405399)
          ·
            refine ⟨447587168738881088586608099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298391445825920725724405399 447587168738881088586608099)
            ·
              refine ⟨671380753108321632879912149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447587168738881088586608099 671380753108321632879912149)
              ·
                refine ⟨15735486400976288270622941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 671380753108321632879912149 15735486400976288270622941)
                ·
                  refine ⟨5900807400366108101483603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15735486400976288270622941 5900807400366108101483603)
                  ·
                    refine ⟨8851211100549162152225405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5900807400366108101483603 8851211100549162152225405)
                    ·
                      refine ⟨3319204162705935807084527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8851211100549162152225405 3319204162705935807084527)
                      ·
                        rfl

theorem cell23_6464127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_6464127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464127 prefixEnd_6464127 := by exact prefixLift 6464127
  have htrace : WordTrace (prefixWord ++ tailWord_6464127) baseStart_6464127 baseEnd_6464127 := by
    simpa [prefixWord, tailWord_6464127, baseEnd_6464127] using wordTrace_append hprefix tailTrace_6464127
  have hstable : (prefixWord ++ tailWord_6464127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464127).length < 2 ^ (prefixWord ++ tailWord_6464127).sum := by decide
  have hdescent : baseEnd_6464127 < baseStart_6464127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464137 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 6, 3, 2]
def baseStart_6464137 : Nat := 118140960795 + 6464137 * 2 ^ 59
def prefixEnd_6464137 : Nat := 4983230072969 + 3 ^ 40 * 6464137 * 2
def baseEnd_6464137 : Nat := 3319209297512480767959481

theorem tailTrace_6464137 : CollatzResearch.WordTrace tailWord_6464137 prefixEnd_6464137 3319209297512480767959481 := by
  unfold tailWord_6464137
  simp only [CollatzResearch.WordTrace]
  refine ⟨235766445382543110551838665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157177630255028740367892443 235766445382543110551838665)
  ·
    refine ⟨176824834036907332913878999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235766445382543110551838665 176824834036907332913878999)
    ·
      refine ⟨265237251055360999370818499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176824834036907332913878999 265237251055360999370818499)
      ·
        refine ⟨397855876583041499056227749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265237251055360999370818499 397855876583041499056227749)
        ·
          refine ⟨74597976859320281073042703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397855876583041499056227749 74597976859320281073042703)
          ·
            refine ⟨111896965288980421609564055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74597976859320281073042703 111896965288980421609564055)
            ·
              refine ⟨167845447933470632414346083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111896965288980421609564055 167845447933470632414346083)
              ·
                refine ⟨251768171900205948621519125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167845447933470632414346083 251768171900205948621519125)
                ·
                  refine ⟨11801633057822153841633709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 251768171900205948621519125 11801633057822153841633709)
                  ·
                    refine ⟨4425612396683307690612641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11801633057822153841633709 4425612396683307690612641)
                    ·
                      refine ⟨3319209297512480767959481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425612396683307690612641 3319209297512480767959481)
                      ·
                        rfl

theorem cell23_6464137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 3, 2].length) (baseStart_6464137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464137 prefixEnd_6464137 := by exact prefixLift 6464137
  have htrace : WordTrace (prefixWord ++ tailWord_6464137) baseStart_6464137 baseEnd_6464137 := by
    simpa [prefixWord, tailWord_6464137, baseEnd_6464137] using wordTrace_append hprefix tailTrace_6464137
  have hstable : (prefixWord ++ tailWord_6464137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464137).length < 2 ^ (prefixWord ++ tailWord_6464137).sum := by decide
  have hdescent : baseEnd_6464137 < baseStart_6464137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464164 : List Nat := [2, 3, 1, 2, 2, 1, 5, 1, 1, 5]
def baseStart_6464164 : Nat := 118140960795 + 6464164 * 2 ^ 59
def prefixEnd_6464164 : Nat := 4983230072969 + 3 ^ 40 * 6464164 * 2
def baseEnd_6464164 : Nat := 1106407720496717387440619

theorem tailTrace_6464164 : CollatzResearch.WordTrace tailWord_6464164 prefixEnd_6464164 1106407720496717387440619 := by
  unfold tailWord_6464164
  simp only [CollatzResearch.WordTrace]
  refine ⟨117883715076722647081535773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157178286768963529442047697 117883715076722647081535773)
  ·
    refine ⟨44206393153770992655575915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117883715076722647081535773 44206393153770992655575915)
    ·
      refine ⟨66309589730656488983363873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44206393153770992655575915 66309589730656488983363873)
      ·
        refine ⟨49732192297992366737522905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66309589730656488983363873 49732192297992366737522905)
        ·
          refine ⟨37299144223494275053142179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49732192297992366737522905 37299144223494275053142179)
          ·
            refine ⟨55948716335241412579713269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37299144223494275053142179 55948716335241412579713269)
            ·
              refine ⟨5245192156428882429348119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55948716335241412579713269 5245192156428882429348119)
              ·
                refine ⟨7867788234643323644022179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5245192156428882429348119 7867788234643323644022179)
                ·
                  refine ⟨11801682351964985466033269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7867788234643323644022179 11801682351964985466033269)
                  ·
                    refine ⟨1106407720496717387440619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11801682351964985466033269 1106407720496717387440619)
                    ·
                      rfl

theorem cell23_6464164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_6464164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464164 prefixEnd_6464164 := by exact prefixLift 6464164
  have htrace : WordTrace (prefixWord ++ tailWord_6464164) baseStart_6464164 baseEnd_6464164 := by
    simpa [prefixWord, tailWord_6464164, baseEnd_6464164] using wordTrace_append hprefix tailTrace_6464164
  have hstable : (prefixWord ++ tailWord_6464164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464164).length < 2 ^ (prefixWord ++ tailWord_6464164).sum := by decide
  have hdescent : baseEnd_6464164 < baseStart_6464164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464204 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 3, 2, 3]
def baseStart_6464204 : Nat := 118140960795 + 6464204 * 2 ^ 59
def prefixEnd_6464204 : Nat := 4983230072969 + 3 ^ 40 * 6464204 * 2
def baseEnd_6464204 : Nat := 3319243700716332005821673

theorem tailTrace_6464204 : CollatzResearch.WordTrace tailWord_6464204 prefixEnd_6464204 3319243700716332005821673 := by
  unfold tailWord_6464204
  simp only [CollatzResearch.WordTrace]
  refine ⟨117884444536650190497263833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157179259382200253996351777 117884444536650190497263833)
  ·
    refine ⟨88413333402487642872947875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117884444536650190497263833 88413333402487642872947875)
    ·
      refine ⟨132620000103731464309421813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88413333402487642872947875 132620000103731464309421813)
      ·
        refine ⟨12433125009724824779008295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132620000103731464309421813 12433125009724824779008295)
        ·
          refine ⟨18649687514587237168512443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12433125009724824779008295 18649687514587237168512443)
          ·
            refine ⟨27974531271880855752768665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18649687514587237168512443 27974531271880855752768665)
            ·
              refine ⟨20980898453910641814576499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27974531271880855752768665 20980898453910641814576499)
              ·
                refine ⟨31471347680865962721864749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20980898453910641814576499 31471347680865962721864749)
                ·
                  refine ⟨11801755380324736020699281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31471347680865962721864749 11801755380324736020699281)
                  ·
                    refine ⟨8851316535243552015524461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11801755380324736020699281 8851316535243552015524461)
                    ·
                      refine ⟨3319243700716332005821673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8851316535243552015524461 3319243700716332005821673)
                      ·
                        rfl

theorem cell23_6464204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_6464204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464204 prefixEnd_6464204 := by exact prefixLift 6464204
  have htrace : WordTrace (prefixWord ++ tailWord_6464204) baseStart_6464204 baseEnd_6464204 := by
    simpa [prefixWord, tailWord_6464204, baseEnd_6464204] using wordTrace_append hprefix tailTrace_6464204
  have hstable : (prefixWord ++ tailWord_6464204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464204).length < 2 ^ (prefixWord ++ tailWord_6464204).sum := by decide
  have hdescent : baseEnd_6464204 < baseStart_6464204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464205 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_6464205 : Nat := 118140960795 + 6464205 * 2 ^ 59
def prefixEnd_6464205 : Nat := 4983230072969 + 3 ^ 40 * 6464205 * 2
def baseEnd_6464205 : Nat := 3319244214196986501909169

theorem tailTrace_6464205 : CollatzResearch.WordTrace tailWord_6464205 prefixEnd_6464205 3319244214196986501909169 := by
  unfold tailWord_6464205
  simp only [CollatzResearch.WordTrace]
  refine ⟨235768925546296758165314069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157179283697531172110209379 235768925546296758165314069)
  ·
    refine ⟨11051668384982660538999097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 235768925546296758165314069 11051668384982660538999097)
    ·
      refine ⟨8288751288736995404249323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11051668384982660538999097 8288751288736995404249323)
      ·
        refine ⟨12433126933105493106373985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8288751288736995404249323 12433126933105493106373985)
        ·
          refine ⟨9324845199829119829780489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12433126933105493106373985 9324845199829119829780489)
          ·
            refine ⟨6993633899871839872335367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9324845199829119829780489 6993633899871839872335367)
            ·
              refine ⟨10490450849807759808503051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6993633899871839872335367 10490450849807759808503051)
              ·
                refine ⟨15735676274711639712754577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10490450849807759808503051 15735676274711639712754577)
                ·
                  refine ⟨11801757206033729784565933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15735676274711639712754577 11801757206033729784565933)
                  ·
                    refine ⟨4425658952262648669212225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11801757206033729784565933 4425658952262648669212225)
                    ·
                      refine ⟨3319244214196986501909169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425658952262648669212225 3319244214196986501909169)
                      ·
                        rfl

theorem cell23_6464205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_6464205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464205 prefixEnd_6464205 := by exact prefixLift 6464205
  have htrace : WordTrace (prefixWord ++ tailWord_6464205) baseStart_6464205 baseEnd_6464205 := by
    simpa [prefixWord, tailWord_6464205, baseEnd_6464205] using wordTrace_append hprefix tailTrace_6464205
  have hstable : (prefixWord ++ tailWord_6464205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464205).length < 2 ^ (prefixWord ++ tailWord_6464205).sum := by decide
  have hdescent : baseEnd_6464205 < baseStart_6464205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464217 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 1, 3, 3]
def baseStart_6464217 : Nat := 118140960795 + 6464217 * 2 ^ 59
def prefixEnd_6464217 : Nat := 4983230072969 + 3 ^ 40 * 6464217 * 2
def baseEnd_6464217 : Nat := 3319250375964840454959113

theorem tailTrace_6464217 : CollatzResearch.WordTrace tailWord_6464217 prefixEnd_6464217 3319250375964840454959113 := by
  unfold tailWord_6464217
  simp only [CollatzResearch.WordTrace]
  refine ⟨235769363222253284214750905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157179575481502189476500603 235769363222253284214750905)
  ·
    refine ⟨176827022416689963161063179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235769363222253284214750905 176827022416689963161063179)
    ·
      refine ⟨265240533625034944741594769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176827022416689963161063179 265240533625034944741594769)
      ·
        refine ⟨198930400218776208556196077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265240533625034944741594769 198930400218776208556196077)
        ·
          refine ⟨74598900082041078208573529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198930400218776208556196077 74598900082041078208573529)
          ·
            refine ⟨55949175061530808656430147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74598900082041078208573529 55949175061530808656430147)
            ·
              refine ⟨83923762592296212984645221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55949175061530808656430147 83923762592296212984645221)
              ·
                refine ⟨15735705486055539934620979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83923762592296212984645221 15735705486055539934620979)
                ·
                  refine ⟨23603558229083309901931469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15735705486055539934620979 23603558229083309901931469)
                  ·
                    refine ⟨8851334335906241213224301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23603558229083309901931469 8851334335906241213224301)
                    ·
                      refine ⟨3319250375964840454959113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8851334335906241213224301 3319250375964840454959113)
                      ·
                        rfl

theorem cell23_6464217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_6464217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464217 prefixEnd_6464217 := by exact prefixLift 6464217
  have htrace : WordTrace (prefixWord ++ tailWord_6464217) baseStart_6464217 baseEnd_6464217 := by
    simpa [prefixWord, tailWord_6464217, baseEnd_6464217] using wordTrace_append hprefix tailTrace_6464217
  have hstable : (prefixWord ++ tailWord_6464217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464217).length < 2 ^ (prefixWord ++ tailWord_6464217).sum := by decide
  have hdescent : baseEnd_6464217 < baseStart_6464217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464218 : List Nat := [3, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2]
def baseStart_6464218 : Nat := 118140960795 + 6464218 * 2 ^ 59
def prefixEnd_6464218 : Nat := 4983230072969 + 3 ^ 40 * 6464218 * 2
def baseEnd_6464218 : Nat := 3319250889445494951046609

theorem tailTrace_6464218 : CollatzResearch.WordTrace tailWord_6464218 prefixEnd_6464218 3319250889445494951046609 := by
  unfold tailWord_6464218
  simp only [CollatzResearch.WordTrace]
  refine ⟨58942349923812415346384327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157179599796833107590358205 58942349923812415346384327)
  ·
    refine ⟨88413524885718623019576491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58942349923812415346384327 88413524885718623019576491)
    ·
      refine ⟨132620287328577934529364737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88413524885718623019576491 132620287328577934529364737)
      ·
        refine ⟨99465215496433450897023553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132620287328577934529364737 99465215496433450897023553)
        ·
          refine ⟨74598911622325088172767665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99465215496433450897023553 74598911622325088172767665)
          ·
            refine ⟨55949183716743816129575749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74598911622325088172767665 55949183716743816129575749)
            ·
              refine ⟨10490471946889465524295453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55949183716743816129575749 10490471946889465524295453)
              ·
                refine ⟨3933926980083549571610795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10490471946889465524295453 3933926980083549571610795)
                ·
                  refine ⟨5900890470125324357416193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3933926980083549571610795 5900890470125324357416193)
                  ·
                    refine ⟨4425667852593993268062145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5900890470125324357416193 4425667852593993268062145)
                    ·
                      refine ⟨3319250889445494951046609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425667852593993268062145 3319250889445494951046609)
                      ·
                        rfl

theorem cell23_6464218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_6464218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464218 prefixEnd_6464218 := by exact prefixLift 6464218
  have htrace : WordTrace (prefixWord ++ tailWord_6464218) baseStart_6464218 baseEnd_6464218 := by
    simpa [prefixWord, tailWord_6464218, baseEnd_6464218] using wordTrace_append hprefix tailTrace_6464218
  have hstable : (prefixWord ++ tailWord_6464218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464218).length < 2 ^ (prefixWord ++ tailWord_6464218).sum := by decide
  have hdescent : baseEnd_6464218 < baseStart_6464218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464245 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6464245 : Nat := 118140960795 + 6464245 * 2 ^ 59
def prefixEnd_6464245 : Nat := 4983230072969 + 3 ^ 40 * 6464245 * 2
def baseEnd_6464245 : Nat := 1106421584474388781802995

theorem tailTrace_6464245 : CollatzResearch.WordTrace tailWord_6464245 prefixEnd_6464245 1106421584474388781802995 := by
  unfold tailWord_6464245
  simp only [CollatzResearch.WordTrace]
  refine ⟨235770384466151844996770189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157180256310767896664513459 235770384466151844996770189)
  ·
    refine ⟨88413894174806941873788821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235770384466151844996770189 88413894174806941873788821)
    ·
      refine ⟨4144401289444075400333851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88413894174806941873788821 4144401289444075400333851)
      ·
        refine ⟨6216601934166113100500777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4144401289444075400333851 6216601934166113100500777)
        ·
          refine ⟨4662451450624584825375583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6216601934166113100500777 4662451450624584825375583)
          ·
            refine ⟨6993677175936877238063375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4662451450624584825375583 6993677175936877238063375)
            ·
              refine ⟨10490515763905315857095063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6993677175936877238063375 10490515763905315857095063)
              ·
                refine ⟨15735773645857973785642595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10490515763905315857095063 15735773645857973785642595)
                ·
                  refine ⟨23603660468786960678463893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15735773645857973785642595 23603660468786960678463893)
                  ·
                    refine ⟨1106421584474388781802995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23603660468786960678463893 1106421584474388781802995)
                    ·
                      rfl

theorem cell23_6464245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6464245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464245 prefixEnd_6464245 := by exact prefixLift 6464245
  have htrace : WordTrace (prefixWord ++ tailWord_6464245) baseStart_6464245 baseEnd_6464245 := by
    simpa [prefixWord, tailWord_6464245, baseEnd_6464245] using wordTrace_append hprefix tailTrace_6464245
  have hstable : (prefixWord ++ tailWord_6464245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464245).length < 2 ^ (prefixWord ++ tailWord_6464245).sum := by decide
  have hdescent : baseEnd_6464245 < baseStart_6464245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464277 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_6464277 : Nat := 118140960795 + 6464277 * 2 ^ 59
def prefixEnd_6464277 : Nat := 4983230072969 + 3 ^ 40 * 6464277 * 2
def baseEnd_6464277 : Nat := 3319281184804110220208837

theorem tailTrace_6464277 : CollatzResearch.WordTrace tailWord_6464277 prefixEnd_6464277 3319281184804110220208837 := by
  unfold tailWord_6464277
  simp only [CollatzResearch.WordTrace]
  refine ⟨235771551602035914461935085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157181034401357276307956723 235771551602035914461935085)
  ·
    refine ⟨88414331850763467923225657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235771551602035914461935085 88414331850763467923225657)
    ·
      refine ⟨66310748888072600942419243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88414331850763467923225657 66310748888072600942419243)
      ·
        refine ⟨99466123332108901413628865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66310748888072600942419243 99466123332108901413628865)
        ·
          refine ⟨74599592499081676060221649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99466123332108901413628865 74599592499081676060221649)
          ·
            refine ⟨55949694374311257045166237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74599592499081676060221649 55949694374311257045166237)
            ·
              refine ⟨20981135390366721391937339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55949694374311257045166237 20981135390366721391937339)
              ·
                refine ⟨31471703085550082087906009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20981135390366721391937339 31471703085550082087906009)
                ·
                  refine ⟨23603777314162561565929507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31471703085550082087906009 23603777314162561565929507)
                  ·
                    refine ⟨35405665971243842348894261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23603777314162561565929507 35405665971243842348894261)
                    ·
                      refine ⟨3319281184804110220208837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35405665971243842348894261 3319281184804110220208837)
                      ·
                        rfl

theorem cell23_6464277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_6464277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464277 prefixEnd_6464277 := by exact prefixLift 6464277
  have htrace : WordTrace (prefixWord ++ tailWord_6464277) baseStart_6464277 baseEnd_6464277 := by
    simpa [prefixWord, tailWord_6464277, baseEnd_6464277] using wordTrace_append hprefix tailTrace_6464277
  have hstable : (prefixWord ++ tailWord_6464277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464277).length < 2 ^ (prefixWord ++ tailWord_6464277).sum := by decide
  have hdescent : baseEnd_6464277 < baseStart_6464277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464291 : List Nat := [1, 1, 1, 4, 2, 1, 1, 6, 2, 2, 2]
def baseStart_6464291 : Nat := 118140960795 + 6464291 * 2 ^ 59
def prefixEnd_6464291 : Nat := 4983230072969 + 3 ^ 40 * 6464291 * 2
def baseEnd_6464291 : Nat := 3319288373533273165433773

theorem tailTrace_6464291 : CollatzResearch.WordTrace tailWord_6464291 prefixEnd_6464291 3319288373533273165433773 := by
  unfold tailWord_6464291
  simp only [CollatzResearch.WordTrace]
  refine ⟨235772062223985194852944727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157181374815990129901963151 235772062223985194852944727)
  ·
    refine ⟨353658093335977792279417091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235772062223985194852944727 353658093335977792279417091)
    ·
      refine ⟨530487140003966688419125637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353658093335977792279417091 530487140003966688419125637)
      ·
        refine ⟨99466338750743754078586057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 530487140003966688419125637 99466338750743754078586057)
        ·
          refine ⟨74599754063057815558939543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99466338750743754078586057 74599754063057815558939543)
          ·
            refine ⟨111899631094586723338409315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74599754063057815558939543 111899631094586723338409315)
            ·
              refine ⟨167849446641880085007613973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111899631094586723338409315 167849446641880085007613973)
              ·
                refine ⟨7867942811338128984731905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167849446641880085007613973 7867942811338128984731905)
                ·
                  refine ⟨5900957108503596738548929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7867942811338128984731905 5900957108503596738548929)
                  ·
                    refine ⟨4425717831377697553911697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5900957108503596738548929 4425717831377697553911697)
                    ·
                      refine ⟨3319288373533273165433773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425717831377697553911697 3319288373533273165433773)
                      ·
                        rfl

theorem cell23_6464291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_6464291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464291 prefixEnd_6464291 := by exact prefixLift 6464291
  have htrace : WordTrace (prefixWord ++ tailWord_6464291) baseStart_6464291 baseEnd_6464291 := by
    simpa [prefixWord, tailWord_6464291, baseEnd_6464291] using wordTrace_append hprefix tailTrace_6464291
  have hstable : (prefixWord ++ tailWord_6464291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464291).length < 2 ^ (prefixWord ++ tailWord_6464291).sum := by decide
  have hdescent : baseEnd_6464291 < baseStart_6464291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464334 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2]
def baseStart_6464334 : Nat := 118140960795 + 6464334 * 2 ^ 59
def prefixEnd_6464334 : Nat := 4983230072969 + 3 ^ 40 * 6464334 * 2
def baseEnd_6464334 : Nat := 3319310453201416497196075

theorem tailTrace_6464334 : CollatzResearch.WordTrace tailWord_6464334 prefixEnd_6464334 3319310453201416497196075 := by
  unfold tailWord_6464334
  simp only [CollatzResearch.WordTrace]
  refine ⟨29471703820353676649595007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157182420375219608797840037 29471703820353676649595007)
  ·
    refine ⟨44207555730530514974392511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29471703820353676649595007 44207555730530514974392511)
    ·
      refine ⟨66311333595795772461588767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44207555730530514974392511 66311333595795772461588767)
      ·
        refine ⟨99467000393693658692383151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66311333595795772461588767 99467000393693658692383151)
        ·
          refine ⟨149200500590540488038574727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99467000393693658692383151 149200500590540488038574727)
          ·
            refine ⟨223800750885810732057862091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149200500590540488038574727 223800750885810732057862091)
            ·
              refine ⟨335701126328716098086793137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223800750885810732057862091 335701126328716098086793137)
              ·
                refine ⟨251775844746537073565094853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335701126328716098086793137 251775844746537073565094853)
                ·
                  refine ⟨47207970889975701293455285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251775844746537073565094853 47207970889975701293455285)
                  ·
                    refine ⟨4425747270935221996261433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47207970889975701293455285 4425747270935221996261433)
                    ·
                      refine ⟨3319310453201416497196075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425747270935221996261433 3319310453201416497196075)
                      ·
                        rfl

theorem cell23_6464334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_6464334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464334 prefixEnd_6464334 := by exact prefixLift 6464334
  have htrace : WordTrace (prefixWord ++ tailWord_6464334) baseStart_6464334 baseEnd_6464334 := by
    simpa [prefixWord, tailWord_6464334, baseEnd_6464334] using wordTrace_append hprefix tailTrace_6464334
  have hstable : (prefixWord ++ tailWord_6464334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464334).length < 2 ^ (prefixWord ++ tailWord_6464334).sum := by decide
  have hdescent : baseEnd_6464334 < baseStart_6464334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464347 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 4]
def baseStart_6464347 : Nat := 118140960795 + 6464347 * 2 ^ 59
def prefixEnd_6464347 : Nat := 4983230072969 + 3 ^ 40 * 6464347 * 2
def baseEnd_6464347 : Nat := 3319317128449924946333515

theorem tailTrace_6464347 : CollatzResearch.WordTrace tailWord_6464347 prefixEnd_6464347 3319317128449924946333515 := by
  unfold tailWord_6464347
  simp only [CollatzResearch.WordTrace]
  refine ⟨235774104711782316416983295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157182736474521544277988863 235774104711782316416983295)
  ·
    refine ⟨353661157067673474625474943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235774104711782316416983295 353661157067673474625474943)
    ·
      refine ⟨530491735601510211938212415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353661157067673474625474943 530491735601510211938212415)
      ·
        refine ⟨795737603402265317907318623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530491735601510211938212415 795737603402265317907318623)
        ·
          refine ⟨1193606405103397976860977935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795737603402265317907318623 1193606405103397976860977935)
          ·
            refine ⟨1790409607655096965291466903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193606405103397976860977935 1790409607655096965291466903)
            ·
              refine ⟨2685614411482645447937200355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1790409607655096965291466903 2685614411482645447937200355)
              ·
                refine ⟨4028421617223968171905800533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2685614411482645447937200355 4028421617223968171905800533)
                ·
                  refine ⟨11802016456710844253630275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 4028421617223968171905800533 11802016456710844253630275)
                  ·
                    refine ⟨17703024685066266380445413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11802016456710844253630275 17703024685066266380445413)
                    ·
                      refine ⟨3319317128449924946333515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17703024685066266380445413 3319317128449924946333515)
                      ·
                        rfl

theorem cell23_6464347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 4].length) (baseStart_6464347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464347 prefixEnd_6464347 := by exact prefixLift 6464347
  have htrace : WordTrace (prefixWord ++ tailWord_6464347) baseStart_6464347 baseEnd_6464347 := by
    simpa [prefixWord, tailWord_6464347, baseEnd_6464347] using wordTrace_append hprefix tailTrace_6464347
  have hstable : (prefixWord ++ tailWord_6464347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464347).length < 2 ^ (prefixWord ++ tailWord_6464347).sum := by decide
  have hdescent : baseEnd_6464347 < baseStart_6464347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464348 : List Nat := [2, 2, 4, 2, 1, 1, 4, 2, 5]
def baseStart_6464348 : Nat := 118140960795 + 6464348 * 2 ^ 59
def prefixEnd_6464348 : Nat := 4983230072969 + 3 ^ 40 * 6464348 * 2
def baseEnd_6464348 : Nat := 368813071325619938046779

theorem tailTrace_6464348 : CollatzResearch.WordTrace tailWord_6464348 prefixEnd_6464348 368813071325619938046779 := by
  unfold tailWord_6464348
  simp only [CollatzResearch.WordTrace]
  refine ⟨117887070592389346793884849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157182760789852462391846465 117887070592389346793884849)
  ·
    refine ⟨88415302944292010095413637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117887070592389346793884849 88415302944292010095413637)
    ·
      refine ⟨16577869302054751892890057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88415302944292010095413637 16577869302054751892890057)
      ·
        refine ⟨12433401976541063919667543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16577869302054751892890057 12433401976541063919667543)
        ·
          refine ⟨18650102964811595879501315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12433401976541063919667543 18650102964811595879501315)
          ·
            refine ⟨27975154447217393819251973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18650102964811595879501315 27975154447217393819251973)
            ·
              refine ⟨5245341458853261341109745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27975154447217393819251973 5245341458853261341109745)
              ·
                refine ⟨3934006094139946005832309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5245341458853261341109745 3934006094139946005832309)
                ·
                  refine ⟨368813071325619938046779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3934006094139946005832309 368813071325619938046779)
                  ·
                    rfl

theorem cell23_6464348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 5].length) (baseStart_6464348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464348 prefixEnd_6464348 := by exact prefixLift 6464348
  have htrace : WordTrace (prefixWord ++ tailWord_6464348) baseStart_6464348 baseEnd_6464348 := by
    simpa [prefixWord, tailWord_6464348, baseEnd_6464348] using wordTrace_append hprefix tailTrace_6464348
  have hstable : (prefixWord ++ tailWord_6464348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464348).length < 2 ^ (prefixWord ++ tailWord_6464348).sum := by decide
  have hdescent : baseEnd_6464348 < baseStart_6464348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464384 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 3]
def baseStart_6464384 : Nat := 118140960795 + 6464384 * 2 ^ 59
def prefixEnd_6464384 : Nat := 4983230072969 + 3 ^ 40 * 6464384 * 2
def baseEnd_6464384 : Nat := 3319336127234141301570845

theorem tailTrace_6464384 : CollatzResearch.WordTrace tailWord_6464384 prefixEnd_6464384 3319336127234141301570845 := by
  unfold tailWord_6464384
  simp only [CollatzResearch.WordTrace]
  refine ⟨117887727106324135868040103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157183636141765514490720137 117887727106324135868040103)
  ·
    refine ⟨176831590659486203802060155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117887727106324135868040103 176831590659486203802060155)
    ·
      refine ⟨265247385989229305703090233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176831590659486203802060155 265247385989229305703090233)
      ·
        refine ⟨198935539491921979277317675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265247385989229305703090233 198935539491921979277317675)
        ·
          refine ⟨298403309237882968915976513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198935539491921979277317675 298403309237882968915976513)
          ·
            refine ⟨223802481928412226686982385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298403309237882968915976513 223802481928412226686982385)
            ·
              refine ⟨167851861446309170015236789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223802481928412226686982385 167851861446309170015236789)
              ·
                refine ⟨15736112010591484688928449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167851861446309170015236789 15736112010591484688928449)
                ·
                  refine ⟨11802084007943613516696337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15736112010591484688928449 11802084007943613516696337)
                  ·
                    refine ⟨8851563005957710137522253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11802084007943613516696337 8851563005957710137522253)
                    ·
                      refine ⟨3319336127234141301570845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8851563005957710137522253 3319336127234141301570845)
                      ·
                        rfl

theorem cell23_6464384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_6464384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464384 prefixEnd_6464384 := by exact prefixLift 6464384
  have htrace : WordTrace (prefixWord ++ tailWord_6464384) baseStart_6464384 baseEnd_6464384 := by
    simpa [prefixWord, tailWord_6464384, baseEnd_6464384] using wordTrace_append hprefix tailTrace_6464384
  have hstable : (prefixWord ++ tailWord_6464384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464384).length < 2 ^ (prefixWord ++ tailWord_6464384).sum := by decide
  have hdescent : baseEnd_6464384 < baseStart_6464384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464387 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 8]
def baseStart_6464387 : Nat := 118140960795 + 6464387 * 2 ^ 59
def prefixEnd_6464387 : Nat := 4983230072969 + 3 ^ 40 * 6464387 * 2
def baseEnd_6464387 : Nat := 368815296408456087759259

theorem tailTrace_6464387 : CollatzResearch.WordTrace tailWord_6464387 prefixEnd_6464387 368815296408456087759259 := by
  unfold tailWord_6464387
  simp only [CollatzResearch.WordTrace]
  refine ⟨235775563631637403248439415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157183709087758268832292943 235775563631637403248439415)
  ·
    refine ⟨353663345447456104872659123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235775563631637403248439415 353663345447456104872659123)
    ·
      refine ⟨530495018171184157308988685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353663345447456104872659123 530495018171184157308988685)
      ·
        refine ⟨198935631814194058990870757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 530495018171184157308988685 198935631814194058990870757)
        ·
          refine ⟨37300430965161386060788267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198935631814194058990870757 37300430965161386060788267)
          ·
            refine ⟨55950646447742079091182401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37300430965161386060788267 55950646447742079091182401)
            ·
              refine ⟨41962984835806559318386801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55950646447742079091182401 41962984835806559318386801)
              ·
                refine ⟨31472238626854919488790101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41962984835806559318386801 31472238626854919488790101)
                ·
                  refine ⟨368815296408456087759259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31472238626854919488790101 368815296408456087759259)
                  ·
                    rfl

theorem cell23_6464387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 8].length) (baseStart_6464387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464387 prefixEnd_6464387 := by exact prefixLift 6464387
  have htrace : WordTrace (prefixWord ++ tailWord_6464387) baseStart_6464387 baseEnd_6464387 := by
    simpa [prefixWord, tailWord_6464387, baseEnd_6464387] using wordTrace_append hprefix tailTrace_6464387
  have hstable : (prefixWord ++ tailWord_6464387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464387).length < 2 ^ (prefixWord ++ tailWord_6464387).sum := by decide
  have hdescent : baseEnd_6464387 < baseStart_6464387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464394 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_6464394 : Nat := 118140960795 + 6464394 * 2 ^ 59
def prefixEnd_6464394 : Nat := 4983230072969 + 3 ^ 40 * 6464394 * 2
def baseEnd_6464394 : Nat := 3319341262040686262445799

theorem tailTrace_6464394 : CollatzResearch.WordTrace tailWord_6464394 prefixEnd_6464394 3319341262040686262445799 := by
  unfold tailWord_6464394
  simp only [CollatzResearch.WordTrace]
  refine ⟨58943954735653010860986059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157183879295074695629296157 58943954735653010860986059)
  ·
    refine ⟨88415932103479516291479089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58943954735653010860986059 88415932103479516291479089)
    ·
      refine ⟨66311949077609637218609317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88415932103479516291479089 66311949077609637218609317)
      ·
        refine ⟨12433490452051806978489247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66311949077609637218609317 12433490452051806978489247)
        ·
          refine ⟨18650235678077710467733871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12433490452051806978489247 18650235678077710467733871)
          ·
            refine ⟨27975353517116565701600807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18650235678077710467733871 27975353517116565701600807)
            ·
              refine ⟨41963030275674848552401211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27975353517116565701600807 41963030275674848552401211)
              ·
                refine ⟨62944545413512272828601817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41963030275674848552401211 62944545413512272828601817)
                ·
                  refine ⟨47208409060134204621451363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62944545413512272828601817 47208409060134204621451363)
                  ·
                    refine ⟨70812613590201306932177045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47208409060134204621451363 70812613590201306932177045)
                    ·
                      refine ⟨3319341262040686262445799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70812613590201306932177045 3319341262040686262445799)
                      ·
                        rfl

theorem cell23_6464394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_6464394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464394 prefixEnd_6464394 := by exact prefixLift 6464394
  have htrace : WordTrace (prefixWord ++ tailWord_6464394) baseStart_6464394 baseEnd_6464394 := by
    simpa [prefixWord, tailWord_6464394, baseEnd_6464394] using wordTrace_append hprefix tailTrace_6464394
  have hstable : (prefixWord ++ tailWord_6464394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464394).length < 2 ^ (prefixWord ++ tailWord_6464394).sum := by decide
  have hdescent : baseEnd_6464394 < baseStart_6464394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464404 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 8]
def baseStart_6464404 : Nat := 118140960795 + 6464404 * 2 ^ 59
def prefixEnd_6464404 : Nat := 4983230072969 + 3 ^ 40 * 6464404 * 2
def baseEnd_6464404 : Nat := 368816266316359024813417

theorem tailTrace_6464404 : CollatzResearch.WordTrace tailWord_6464404 prefixEnd_6464404 368816266316359024813417 := by
  unfold tailWord_6464404
  simp only [CollatzResearch.WordTrace]
  refine ⟨117888091836287907575904133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157184122448383876767872177 117888091836287907575904133)
  ·
    refine ⟨22104017219303982670482025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117888091836287907575904133 22104017219303982670482025)
    ·
      refine ⟨16578012914477987002861519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22104017219303982670482025 16578012914477987002861519)
      ·
        refine ⟨24867019371716980504292279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16578012914477987002861519 24867019371716980504292279)
        ·
          refine ⟨37300529057575470756438419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24867019371716980504292279 37300529057575470756438419)
          ·
            refine ⟨55950793586363206134657629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37300529057575470756438419 55950793586363206134657629)
            ·
              refine ⟨20981547594886202300496611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55950793586363206134657629 20981547594886202300496611)
              ·
                refine ⟨31472321392329303450744917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20981547594886202300496611 31472321392329303450744917)
                ·
                  refine ⟨368816266316359024813417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31472321392329303450744917 368816266316359024813417)
                  ·
                    rfl

theorem cell23_6464404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_6464404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464404 prefixEnd_6464404 := by exact prefixLift 6464404
  have htrace : WordTrace (prefixWord ++ tailWord_6464404) baseStart_6464404 baseEnd_6464404 := by
    simpa [prefixWord, tailWord_6464404, baseEnd_6464404] using wordTrace_append hprefix tailTrace_6464404
  have hstable : (prefixWord ++ tailWord_6464404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464404).length < 2 ^ (prefixWord ++ tailWord_6464404).sum := by decide
  have hdescent : baseEnd_6464404 < baseStart_6464404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464407 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_6464407 : Nat := 118140960795 + 6464407 * 2 ^ 59
def prefixEnd_6464407 : Nat := 4983230072969 + 3 ^ 40 * 6464407 * 2
def baseEnd_6464407 : Nat := 3319347937289194711583239

theorem tailTrace_6464407 : CollatzResearch.WordTrace tailWord_6464407 prefixEnd_6464407 3319347937289194711583239 := by
  unfold tailWord_6464407
  simp only [CollatzResearch.WordTrace]
  refine ⟨235776293091564946664167475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157184195394376631109444983 235776293091564946664167475)
  ·
    refine ⟨353664439637347419996251213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235776293091564946664167475 353664439637347419996251213)
    ·
      refine ⟨132624164864005282498594205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353664439637347419996251213 132624164864005282498594205)
      ·
        refine ⟨49734061824001980936972827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132624164864005282498594205 49734061824001980936972827)
        ·
          refine ⟨74601092736002971405459241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49734061824001980936972827 74601092736002971405459241)
          ·
            refine ⟨55950819552002228554094431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74601092736002971405459241 55950819552002228554094431)
            ·
              refine ⟨83926229328003342831141647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55950819552002228554094431 83926229328003342831141647)
              ·
                refine ⟨125889343992005014246712471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83926229328003342831141647 125889343992005014246712471)
                ·
                  refine ⟨188834015988007521370068707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125889343992005014246712471 188834015988007521370068707)
                  ·
                    refine ⟨283251023982011282055103061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188834015988007521370068707 283251023982011282055103061)
                    ·
                      refine ⟨3319347937289194711583239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 283251023982011282055103061 3319347937289194711583239)
                      ·
                        rfl

theorem cell23_6464407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_6464407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464407 prefixEnd_6464407 := by exact prefixLift 6464407
  have htrace : WordTrace (prefixWord ++ tailWord_6464407) baseStart_6464407 baseEnd_6464407 := by
    simpa [prefixWord, tailWord_6464407, baseEnd_6464407] using wordTrace_append hprefix tailTrace_6464407
  have hstable : (prefixWord ++ tailWord_6464407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464407).length < 2 ^ (prefixWord ++ tailWord_6464407).sum := by decide
  have hdescent : baseEnd_6464407 < baseStart_6464407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464441 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 1, 5, 2]
def baseStart_6464441 : Nat := 118140960795 + 6464441 * 2 ^ 59
def prefixEnd_6464441 : Nat := 4983230072969 + 3 ^ 40 * 6464441 * 2
def baseEnd_6464441 : Nat := 3319365395631447578558083

theorem tailTrace_6464441 : CollatzResearch.WordTrace tailWord_6464441 prefixEnd_6464441 3319365395631447578558083 := by
  unfold tailWord_6464441
  simp only [CollatzResearch.WordTrace]
  refine ⟨235777533173441770470905177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157185022115627846980603451 235777533173441770470905177)
  ·
    refine ⟨176833149880081327853178883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235777533173441770470905177 176833149880081327853178883)
    ·
      refine ⟨265249724820121991779768325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176833149880081327853178883 265249724820121991779768325)
      ·
        refine ⟨49734323403772873458706561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265249724820121991779768325 49734323403772873458706561)
        ·
          refine ⟨37300742552829655094029921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49734323403772873458706561 37300742552829655094029921)
          ·
            refine ⟨27975556914622241320522441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37300742552829655094029921 27975556914622241320522441)
            ·
              refine ⟨20981667685966680990391831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27975556914622241320522441 20981667685966680990391831)
              ·
                refine ⟨31472501528950021485587747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20981667685966680990391831 31472501528950021485587747)
                ·
                  refine ⟨47208752293425032228381621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31472501528950021485587747 47208752293425032228381621)
                  ·
                    refine ⟨4425820527508596771410777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47208752293425032228381621 4425820527508596771410777)
                    ·
                      refine ⟨3319365395631447578558083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425820527508596771410777 3319365395631447578558083)
                      ·
                        rfl

theorem cell23_6464441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_6464441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464441 prefixEnd_6464441 := by exact prefixLift 6464441
  have htrace : WordTrace (prefixWord ++ tailWord_6464441) baseStart_6464441 baseEnd_6464441 := by
    simpa [prefixWord, tailWord_6464441, baseEnd_6464441] using wordTrace_append hprefix tailTrace_6464441
  have hstable : (prefixWord ++ tailWord_6464441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464441).length < 2 ^ (prefixWord ++ tailWord_6464441).sum := by decide
  have hdescent : baseEnd_6464441 < baseStart_6464441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464465 : List Nat := [1, 2, 2, 1, 2, 1, 7, 2, 1, 1, 3]
def baseStart_6464465 : Nat := 118140960795 + 6464465 * 2 ^ 59
def prefixEnd_6464465 : Nat := 4983230072969 + 3 ^ 40 * 6464465 * 2
def baseEnd_6464465 : Nat := 3319377719167155484657973

theorem tailTrace_6464465 : CollatzResearch.WordTrace tailWord_6464465 prefixEnd_6464465 3319377719167155484657973 := by
  unfold tailWord_6464465
  simp only [CollatzResearch.WordTrace]
  refine ⟨235778408525354822569778849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157185605683569881713185899 235778408525354822569778849)
  ·
    refine ⟨176833806394016116927334137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235778408525354822569778849 176833806394016116927334137)
    ·
      refine ⟨132625354795512087695500603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176833806394016116927334137 132625354795512087695500603)
      ·
        refine ⟨198938032193268131543250905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132625354795512087695500603 198938032193268131543250905)
        ·
          refine ⟨149203524144951098657438179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198938032193268131543250905 149203524144951098657438179)
          ·
            refine ⟨223805286217426647986157269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149203524144951098657438179 223805286217426647986157269)
            ·
              refine ⟨5245436395720937062175561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 223805286217426647986157269 5245436395720937062175561)
              ·
                refine ⟨3934077296790702796631671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5245436395720937062175561 3934077296790702796631671)
                ·
                  refine ⟨5901115945186054194947507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3934077296790702796631671 5901115945186054194947507)
                  ·
                    refine ⟨8851673917779081292421261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5901115945186054194947507 8851673917779081292421261)
                    ·
                      refine ⟨3319377719167155484657973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8851673917779081292421261 3319377719167155484657973)
                      ·
                        rfl

theorem cell23_6464465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 1, 1, 3].length) (baseStart_6464465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464465 prefixEnd_6464465 := by exact prefixLift 6464465
  have htrace : WordTrace (prefixWord ++ tailWord_6464465) baseStart_6464465 baseEnd_6464465 := by
    simpa [prefixWord, tailWord_6464465, baseEnd_6464465] using wordTrace_append hprefix tailTrace_6464465
  have hstable : (prefixWord ++ tailWord_6464465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464465).length < 2 ^ (prefixWord ++ tailWord_6464465).sum := by decide
  have hdescent : baseEnd_6464465 < baseStart_6464465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464485 : List Nat := [1, 3, 1, 6, 1, 2, 1, 2, 1, 5]
def baseStart_6464485 : Nat := 118140960795 + 6464485 * 2 ^ 59
def prefixEnd_6464485 : Nat := 4983230072969 + 3 ^ 40 * 6464485 * 2
def baseEnd_6464485 : Nat := 1106462662926748468802627

theorem tailTrace_6464485 : CollatzResearch.WordTrace tailWord_6464485 prefixEnd_6464485 1106462662926748468802627 := by
  unfold tailWord_6464485
  simp only [CollatzResearch.WordTrace]
  refine ⟨235779137985282365985506909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157186091990188243990337939 235779137985282365985506909)
  ·
    refine ⟨88417176744480887244565091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235779137985282365985506909 88417176744480887244565091)
    ·
      refine ⟨132625765116721330866847637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88417176744480887244565091 132625765116721330866847637)
      ·
        refine ⟨6216832739846312384383483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 132625765116721330866847637 6216832739846312384383483)
        ·
          refine ⟨9325249109769468576575225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6216832739846312384383483 9325249109769468576575225)
          ·
            refine ⟨6993936832327101432431419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9325249109769468576575225 6993936832327101432431419)
            ·
              refine ⟨10490905248490652148647129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6993936832327101432431419 10490905248490652148647129)
              ·
                refine ⟨7868178936367989111485347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10490905248490652148647129 7868178936367989111485347)
                ·
                  refine ⟨11802268404551983667228021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7868178936367989111485347 11802268404551983667228021)
                  ·
                    refine ⟨1106462662926748468802627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11802268404551983667228021 1106462662926748468802627)
                    ·
                      rfl

theorem cell23_6464485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_6464485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464485 prefixEnd_6464485 := by exact prefixLift 6464485
  have htrace : WordTrace (prefixWord ++ tailWord_6464485) baseStart_6464485 baseEnd_6464485 := by
    simpa [prefixWord, tailWord_6464485, baseEnd_6464485] using wordTrace_append hprefix tailTrace_6464485
  have hstable : (prefixWord ++ tailWord_6464485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464485).length < 2 ^ (prefixWord ++ tailWord_6464485).sum := by decide
  have hdescent : baseEnd_6464485 < baseStart_6464485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464488 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_6464488 : Nat := 118140960795 + 6464488 * 2 ^ 59
def prefixEnd_6464488 : Nat := 4983230072969 + 3 ^ 40 * 6464488 * 2
def baseEnd_6464488 : Nat := 3319389529222208894670367

theorem tailTrace_6464488 : CollatzResearch.WordTrace tailWord_6464488 prefixEnd_6464488 3319389529222208894670367 := by
  unfold tailWord_6464488
  simp only [CollatzResearch.WordTrace]
  refine ⟨117889623702135748748933059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157186164936180998331910745 117889623702135748748933059)
  ·
    refine ⟨176834435553203623123399589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117889623702135748748933059 176834435553203623123399589)
    ·
      refine ⟨33156456666225679335637423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176834435553203623123399589 33156456666225679335637423)
      ·
        refine ⟨49734684999338519003456135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33156456666225679335637423 49734684999338519003456135)
        ·
          refine ⟨74602027499007778505184203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49734684999338519003456135 74602027499007778505184203)
          ·
            refine ⟨111903041248511667757776305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74602027499007778505184203 111903041248511667757776305)
            ·
              refine ⟨83927280936383750818332229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111903041248511667757776305 83927280936383750818332229)
              ·
                refine ⟨15736365175571953278437293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83927280936383750818332229 15736365175571953278437293)
                ·
                  refine ⟨5901136940839482479413985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15736365175571953278437293 5901136940839482479413985)
                  ·
                    refine ⟨4425852705629611859560489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5901136940839482479413985 4425852705629611859560489)
                    ·
                      refine ⟨3319389529222208894670367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425852705629611859560489 3319389529222208894670367)
                      ·
                        rfl

theorem cell23_6464488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_6464488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464488 prefixEnd_6464488 := by exact prefixLift 6464488
  have htrace : WordTrace (prefixWord ++ tailWord_6464488) baseStart_6464488 baseEnd_6464488 := by
    simpa [prefixWord, tailWord_6464488, baseEnd_6464488] using wordTrace_append hprefix tailTrace_6464488
  have hstable : (prefixWord ++ tailWord_6464488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464488).length < 2 ^ (prefixWord ++ tailWord_6464488).sum := by decide
  have hdescent : baseEnd_6464488 < baseStart_6464488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464498 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_6464498 : Nat := 118140960795 + 6464498 * 2 ^ 59
def prefixEnd_6464498 : Nat := 4983230072969 + 3 ^ 40 * 6464498 * 2
def baseEnd_6464498 : Nat := 1106464888009584618515107

theorem tailTrace_6464498 : CollatzResearch.WordTrace tailWord_6464498 prefixEnd_6464498 1106464888009584618515107 := by
  unfold tailWord_6464498
  simp only [CollatzResearch.WordTrace]
  refine ⟨58944903033558817301432537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157186408089490179470486765 58944903033558817301432537)
  ·
    refine ⟨44208677275169112976074403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58944903033558817301432537 44208677275169112976074403)
    ·
      refine ⟨66313015912753669464111605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44208677275169112976074403 66313015912753669464111605)
      ·
        refine ⟨6216845241820656512260463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66313015912753669464111605 6216845241820656512260463)
        ·
          refine ⟨9325267862730984768390695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6216845241820656512260463 9325267862730984768390695)
          ·
            refine ⟨13987901794096477152586043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9325267862730984768390695 13987901794096477152586043)
            ·
              refine ⟨20981852691144715728879065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13987901794096477152586043 20981852691144715728879065)
              ·
                refine ⟨15736389518358536796659299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20981852691144715728879065 15736389518358536796659299)
                ·
                  refine ⟨23604584277537805194988949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15736389518358536796659299 23604584277537805194988949)
                  ·
                    refine ⟨1106464888009584618515107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23604584277537805194988949 1106464888009584618515107)
                    ·
                      rfl

theorem cell23_6464498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_6464498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464498 prefixEnd_6464498 := by exact prefixLift 6464498
  have htrace : WordTrace (prefixWord ++ tailWord_6464498) baseStart_6464498 baseEnd_6464498 := by
    simpa [prefixWord, tailWord_6464498, baseEnd_6464498] using wordTrace_append hprefix tailTrace_6464498
  have hstable : (prefixWord ++ tailWord_6464498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464498).length < 2 ^ (prefixWord ++ tailWord_6464498).sum := by decide
  have hdescent : baseEnd_6464498 < baseStart_6464498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464505 : List Nat := [1, 2, 1, 3, 1, 3, 2, 5, 1, 2, 2]
def baseStart_6464505 : Nat := 118140960795 + 6464505 * 2 ^ 59
def prefixEnd_6464505 : Nat := 4983230072969 + 3 ^ 40 * 6464505 * 2
def baseEnd_6464505 : Nat := 3319398258393335328157789

theorem tailTrace_6464505 : CollatzResearch.WordTrace tailWord_6464505 prefixEnd_6464505 3319398258393335328157789 := by
  unfold tailWord_6464505
  simp only [CollatzResearch.WordTrace]
  refine ⟨235779867445209909401234969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157186578296806606267489979 235779867445209909401234969)
  ·
    refine ⟨176834900583907432050926227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235779867445209909401234969 176834900583907432050926227)
    ·
      refine ⟨265252350875861148076389341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176834900583907432050926227 265252350875861148076389341)
      ·
        refine ⟨99469631578447930528646003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265252350875861148076389341 99469631578447930528646003)
        ·
          refine ⟨149204447367671895792969005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99469631578447930528646003 149204447367671895792969005)
          ·
            refine ⟨55951667762876960922363377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149204447367671895792969005 55951667762876960922363377)
            ·
              refine ⟨41963750822157720691772533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55951667762876960922363377 41963750822157720691772533)
              ·
                refine ⟨3934101639577286314853675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41963750822157720691772533 3934101639577286314853675)
                ·
                  refine ⟨5901152459365929472280513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3934101639577286314853675 5901152459365929472280513)
                  ·
                    refine ⟨4425864344524447104210385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5901152459365929472280513 4425864344524447104210385)
                    ·
                      refine ⟨3319398258393335328157789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425864344524447104210385 3319398258393335328157789)
                      ·
                        rfl

theorem cell23_6464505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_6464505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464505 prefixEnd_6464505 := by exact prefixLift 6464505
  have htrace : WordTrace (prefixWord ++ tailWord_6464505) baseStart_6464505 baseEnd_6464505 := by
    simpa [prefixWord, tailWord_6464505, baseEnd_6464505] using wordTrace_append hprefix tailTrace_6464505
  have hstable : (prefixWord ++ tailWord_6464505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464505).length < 2 ^ (prefixWord ++ tailWord_6464505).sum := by decide
  have hdescent : baseEnd_6464505 < baseStart_6464505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464521 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 4, 1, 3]
def baseStart_6464521 : Nat := 118140960795 + 6464521 * 2 ^ 59
def prefixEnd_6464521 : Nat := 4983230072969 + 3 ^ 40 * 6464521 * 2
def baseEnd_6464521 : Nat := 3319406474083807265557715

theorem tailTrace_6464521 : CollatzResearch.WordTrace tailWord_6464521 prefixEnd_6464521 3319406474083807265557715 := by
  unfold tailWord_6464521
  simp only [CollatzResearch.WordTrace]
  refine ⟨235780451013151944133817417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157186967342101296089211611 235780451013151944133817417)
  ·
    refine ⟨176835338259863958100363063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235780451013151944133817417 176835338259863958100363063)
    ·
      refine ⟨265253007389795937150544595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176835338259863958100363063 265253007389795937150544595)
      ·
        refine ⟨397879511084693905725816893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265253007389795937150544595 397879511084693905725816893)
        ·
          refine ⟨149204816656760214647181335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397879511084693905725816893 149204816656760214647181335)
          ·
            refine ⟨223807224985140321970772003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149204816656760214647181335 223807224985140321970772003)
            ·
              refine ⟨335710837477710482956158005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223807224985140321970772003 335710837477710482956158005)
              ·
                refine ⟨31472891013535357777139813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 335710837477710482956158005 31472891013535357777139813)
                ·
                  refine ⟨5901167065037879583213715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31472891013535357777139813 5901167065037879583213715)
                  ·
                    refine ⟨8851750597556819374820573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5901167065037879583213715 8851750597556819374820573)
                    ·
                      refine ⟨3319406474083807265557715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8851750597556819374820573 3319406474083807265557715)
                      ·
                        rfl

theorem cell23_6464521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 1, 3].length) (baseStart_6464521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464521 prefixEnd_6464521 := by exact prefixLift 6464521
  have htrace : WordTrace (prefixWord ++ tailWord_6464521) baseStart_6464521 baseEnd_6464521 := by
    simpa [prefixWord, tailWord_6464521, baseEnd_6464521] using wordTrace_append hprefix tailTrace_6464521
  have hstable : (prefixWord ++ tailWord_6464521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464521).length < 2 ^ (prefixWord ++ tailWord_6464521).sum := by decide
  have hdescent : baseEnd_6464521 < baseStart_6464521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464522 : List Nat := [3, 1, 2, 2, 3, 2, 1, 4, 1, 2, 2]
def baseStart_6464522 : Nat := 118140960795 + 6464522 * 2 ^ 59
def prefixEnd_6464522 : Nat := 4983230072969 + 3 ^ 40 * 6464522 * 2
def baseEnd_6464522 : Nat := 3319406987564461761645211

theorem tailTrace_6464522 : CollatzResearch.WordTrace tailWord_6464522 prefixEnd_6464522 3319406987564461761645211 := by
  unfold tailWord_6464522
  simp only [CollatzResearch.WordTrace]
  refine ⟨58945121871537080326150955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157186991657432214203069213 58945121871537080326150955)
  ·
    refine ⟨88417682807305620489226433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58945121871537080326150955 88417682807305620489226433)
    ·
      refine ⟨66313262105479215366919825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88417682807305620489226433 66313262105479215366919825)
      ·
        refine ⟨49734946579109411525189869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66313262105479215366919825 49734946579109411525189869)
        ·
          refine ⟨18650604967166029321946201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49734946579109411525189869 18650604967166029321946201)
          ·
            refine ⟨13987953725374521991459651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18650604967166029321946201 13987953725374521991459651)
            ·
              refine ⟨20981930588061782987189477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13987953725374521991459651 20981930588061782987189477)
              ·
                refine ⟨3934111985261584310098027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20981930588061782987189477 3934111985261584310098027)
                ·
                  refine ⟨5901167977892376465147041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3934111985261584310098027 5901167977892376465147041)
                  ·
                    refine ⟨4425875983419282348860281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5901167977892376465147041 4425875983419282348860281)
                    ·
                      refine ⟨3319406987564461761645211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4425875983419282348860281 3319406987564461761645211)
                      ·
                        rfl

theorem cell23_6464522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_6464522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464522 prefixEnd_6464522 := by exact prefixLift 6464522
  have htrace : WordTrace (prefixWord ++ tailWord_6464522) baseStart_6464522 baseEnd_6464522 := by
    simpa [prefixWord, tailWord_6464522, baseEnd_6464522] using wordTrace_append hprefix tailTrace_6464522
  have hstable : (prefixWord ++ tailWord_6464522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464522).length < 2 ^ (prefixWord ++ tailWord_6464522).sum := by decide
  have hdescent : baseEnd_6464522 < baseStart_6464522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464524 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 2, 7]
def baseStart_6464524 : Nat := 118140960795 + 6464524 * 2 ^ 59
def prefixEnd_6464524 : Nat := 4983230072969 + 3 ^ 40 * 6464524 * 2
def baseEnd_6464524 : Nat := 1106469338175256917940067

theorem tailTrace_6464524 : CollatzResearch.WordTrace tailWord_6464524 prefixEnd_6464524 1106469338175256917940067 := by
  unfold tailWord_6464524
  simp only [CollatzResearch.WordTrace]
  refine ⟨117890280216070537823088313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157187040288094050430784417 117890280216070537823088313)
  ·
    refine ⟨88417710162052903367316235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117890280216070537823088313 88417710162052903367316235)
    ·
      refine ⟨132626565243079355050974353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88417710162052903367316235 132626565243079355050974353)
      ·
        refine ⟨99469923932309516288230765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132626565243079355050974353 99469923932309516288230765)
        ·
          refine ⟨37301221474616068608086537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99469923932309516288230765 37301221474616068608086537)
          ·
            refine ⟨27975916105962051456064903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37301221474616068608086537 27975916105962051456064903)
            ·
              refine ⟨41963874158943077184097355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27975916105962051456064903 41963874158943077184097355)
              ·
                refine ⟨62945811238414615776146033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41963874158943077184097355 62945811238414615776146033)
                ·
                  refine ⟨47209358428810961832109525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62945811238414615776146033 47209358428810961832109525)
                  ·
                    refine ⟨1106469338175256917940067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47209358428810961832109525 1106469338175256917940067)
                    ·
                      rfl

theorem cell23_6464524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_6464524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464524 prefixEnd_6464524 := by exact prefixLift 6464524
  have htrace : WordTrace (prefixWord ++ tailWord_6464524) baseStart_6464524 baseEnd_6464524 := by
    simpa [prefixWord, tailWord_6464524, baseEnd_6464524] using wordTrace_append hprefix tailTrace_6464524
  have hstable : (prefixWord ++ tailWord_6464524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464524).length < 2 ^ (prefixWord ++ tailWord_6464524).sum := by decide
  have hdescent : baseEnd_6464524 < baseStart_6464524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464538 : List Nat := [3, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3]
def baseStart_6464538 : Nat := 118140960795 + 6464538 * 2 ^ 59
def prefixEnd_6464538 : Nat := 4983230072969 + 3 ^ 40 * 6464538 * 2
def baseEnd_6464538 : Nat := 3319415203254933699045137

theorem tailTrace_6464538 : CollatzResearch.WordTrace tailWord_6464538 prefixEnd_6464538 3319415203254933699045137 := by
  unfold tailWord_6464538
  simp only [CollatzResearch.WordTrace]
  refine ⟨58945267763522589009296567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157187380702726904024790845 58945267763522589009296567)
  ·
    refine ⟨88417901645283883513944851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58945267763522589009296567 88417901645283883513944851)
    ·
      refine ⟨132626852467925825270917277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88417901645283883513944851 132626852467925825270917277)
      ·
        refine ⟨49735069675472184476593979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132626852467925825270917277 49735069675472184476593979)
        ·
          refine ⟨74602604513208276714890969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49735069675472184476593979 74602604513208276714890969)
          ·
            refine ⟨55951953384906207536168227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74602604513208276714890969 55951953384906207536168227)
            ·
              refine ⟨83927930077359311304252341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55951953384906207536168227 83927930077359311304252341)
              ·
                refine ⟨7868243444752435434773657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83927930077359311304252341 7868243444752435434773657)
                ·
                  refine ⟨5901182583564326576080243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7868243444752435434773657 5901182583564326576080243)
                  ·
                    refine ⟨8851773875346489864120365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5901182583564326576080243 8851773875346489864120365)
                    ·
                      refine ⟨3319415203254933699045137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8851773875346489864120365 3319415203254933699045137)
                      ·
                        rfl

theorem cell23_6464538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_6464538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464538 prefixEnd_6464538 := by exact prefixLift 6464538
  have htrace : WordTrace (prefixWord ++ tailWord_6464538) baseStart_6464538 baseEnd_6464538 := by
    simpa [prefixWord, tailWord_6464538, baseEnd_6464538] using wordTrace_append hprefix tailTrace_6464538
  have hstable : (prefixWord ++ tailWord_6464538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464538).length < 2 ^ (prefixWord ++ tailWord_6464538).sum := by decide
  have hdescent : baseEnd_6464538 < baseStart_6464538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464631 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 2, 5]
def baseStart_6464631 : Nat := 118140960795 + 6464631 * 2 ^ 59
def prefixEnd_6464631 : Nat := 4983230072969 + 3 ^ 40 * 6464631 * 2
def baseEnd_6464631 : Nat := 1106487652318600611727403

theorem tailTrace_6464631 : CollatzResearch.WordTrace tailWord_6464631 prefixEnd_6464631 1106487652318600611727403 := by
  unfold tailWord_6464631
  simp only [CollatzResearch.WordTrace]
  refine ⟨235784463042753432920321747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157189642028502288613547831 235784463042753432920321747)
  ·
    refine ⟨353676694564130149380482621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235784463042753432920321747 353676694564130149380482621)
    ·
      refine ⟨132628760461548806017680983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353676694564130149380482621 132628760461548806017680983)
      ·
        refine ⟨198943140692323209026521475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132628760461548806017680983 198943140692323209026521475)
        ·
          refine ⟨298414711038484813539782213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198943140692323209026521475 298414711038484813539782213)
          ·
            refine ⟨55952758319715902538709165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 298414711038484813539782213 55952758319715902538709165)
            ·
              refine ⟨20982284369893463452015937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55952758319715902538709165 20982284369893463452015937)
              ·
                refine ⟨15736713277420097589011953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20982284369893463452015937 15736713277420097589011953)
                ·
                  refine ⟨11802534958065073191758965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15736713277420097589011953 11802534958065073191758965)
                  ·
                    refine ⟨1106487652318600611727403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11802534958065073191758965 1106487652318600611727403)
                    ·
                      rfl

theorem cell23_6464631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_6464631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464631 prefixEnd_6464631 := by exact prefixLift 6464631
  have htrace : WordTrace (prefixWord ++ tailWord_6464631) baseStart_6464631 baseEnd_6464631 := by
    simpa [prefixWord, tailWord_6464631, baseEnd_6464631] using wordTrace_append hprefix tailTrace_6464631
  have hstable : (prefixWord ++ tailWord_6464631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464631).length < 2 ^ (prefixWord ++ tailWord_6464631).sum := by decide
  have hdescent : baseEnd_6464631 < baseStart_6464631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464634 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_6464634 : Nat := 118140960795 + 6464634 * 2 ^ 59
def prefixEnd_6464634 : Nat := 4983230072969 + 3 ^ 40 * 6464634 * 2
def baseEnd_6464634 : Nat := 3319464497397765323444695

theorem tailTrace_6464634 : CollatzResearch.WordTrace tailWord_6464634 prefixEnd_6464634 3319464497397765323444695 := by
  unfold tailWord_6464634
  simp only [CollatzResearch.WordTrace]
  refine ⟨58946143115435641108170239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157189714974495042955120637 58946143115435641108170239)
  ·
    refine ⟨88419214673153461662255359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58946143115435641108170239 88419214673153461662255359)
    ·
      refine ⟨132628822009730192493383039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88419214673153461662255359 132628822009730192493383039)
      ·
        refine ⟨198943233014595288740074559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132628822009730192493383039 198943233014595288740074559)
        ·
          refine ⟨298414849521892933110111839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198943233014595288740074559 298414849521892933110111839)
          ·
            refine ⟨447622274282839399665167759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298414849521892933110111839 447622274282839399665167759)
            ·
              refine ⟨671433411424259099497751639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447622274282839399665167759 671433411424259099497751639)
              ·
                refine ⟨1007150117136388649246627459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671433411424259099497751639 1007150117136388649246627459)
                ·
                  refine ⟨1510725175704582973869941189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007150117136388649246627459 1510725175704582973869941189)
                  ·
                    refine ⟨283260970444609307600613973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1510725175704582973869941189 283260970444609307600613973)
                    ·
                      refine ⟨3319464497397765323444695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 283260970444609307600613973 3319464497397765323444695)
                      ·
                        rfl

theorem cell23_6464634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_6464634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464634 prefixEnd_6464634 := by exact prefixLift 6464634
  have htrace : WordTrace (prefixWord ++ tailWord_6464634) baseStart_6464634 baseEnd_6464634 := by
    simpa [prefixWord, tailWord_6464634, baseEnd_6464634] using wordTrace_append hprefix tailTrace_6464634
  have hstable : (prefixWord ++ tailWord_6464634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464634).length < 2 ^ (prefixWord ++ tailWord_6464634).sum := by decide
  have hdescent : baseEnd_6464634 < baseStart_6464634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464641 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_6464641 : Nat := 118140960795 + 6464641 * 2 ^ 59
def prefixEnd_6464641 : Nat := 4983230072969 + 3 ^ 40 * 6464641 * 2
def baseEnd_6464641 : Nat := 3319468091762346796057163

theorem tailTrace_6464641 : CollatzResearch.WordTrace tailWord_6464641 prefixEnd_6464641 3319468091762346796057163 := by
  unfold tailWord_6464641
  simp only [CollatzResearch.WordTrace]
  refine ⟨235784827772717204628185777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157189885181811469752123851 235784827772717204628185777)
  ·
    refine ⟨176838620829537903471139333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235784827772717204628185777 176838620829537903471139333)
    ·
      refine ⟨33157241405538356900838625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176838620829537903471139333 33157241405538356900838625)
      ·
        refine ⟨24867931054153767675628969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33157241405538356900838625 24867931054153767675628969)
        ·
          refine ⟨18650948290615325756721727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24867931054153767675628969 18650948290615325756721727)
          ·
            refine ⟨27976422435922988635082591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18650948290615325756721727 27976422435922988635082591)
            ·
              refine ⟨41964633653884482952623887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27976422435922988635082591 41964633653884482952623887)
              ·
                refine ⟨62946950480826724428935831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41964633653884482952623887 62946950480826724428935831)
                ·
                  refine ⟨94420425721240086643403747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62946950480826724428935831 94420425721240086643403747)
                  ·
                    refine ⟨141630638581860129965105621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94420425721240086643403747 141630638581860129965105621)
                    ·
                      refine ⟨3319468091762346796057163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141630638581860129965105621 3319468091762346796057163)
                      ·
                        rfl

theorem cell23_6464641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_6464641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464641 prefixEnd_6464641 := by exact prefixLift 6464641
  have htrace : WordTrace (prefixWord ++ tailWord_6464641) baseStart_6464641 baseEnd_6464641 := by
    simpa [prefixWord, tailWord_6464641, baseEnd_6464641] using wordTrace_append hprefix tailTrace_6464641
  have hstable : (prefixWord ++ tailWord_6464641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464641).length < 2 ^ (prefixWord ++ tailWord_6464641).sum := by decide
  have hdescent : baseEnd_6464641 < baseStart_6464641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464668 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_6464668 : Nat := 118140960795 + 6464668 * 2 ^ 59
def prefixEnd_6464668 : Nat := 4983230072969 + 3 ^ 40 * 6464668 * 2
def baseEnd_6464668 : Nat := 3319481955740018190419539

theorem tailTrace_6464668 : CollatzResearch.WordTrace tailWord_6464668 prefixEnd_6464668 3319481955740018190419539 := by
  unfold tailWord_6464668
  simp only [CollatzResearch.WordTrace]
  refine ⟨117892906271809694119709329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157190541695746258826279105 117892906271809694119709329)
  ·
    refine ⟨88419679703857270589781997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117892906271809694119709329 88419679703857270589781997)
    ·
      refine ⟨33157379888946476471168249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88419679703857270589781997 33157379888946476471168249)
      ·
        refine ⟨24868034916709857353376187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33157379888946476471168249 24868034916709857353376187)
        ·
          refine ⟨37302052375064786030064281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24868034916709857353376187 37302052375064786030064281)
          ·
            refine ⟨27976539281298589522548211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37302052375064786030064281 27976539281298589522548211)
            ·
              refine ⟨41964808921947884283822317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27976539281298589522548211 41964808921947884283822317)
              ·
                refine ⟨15736803345730456606433369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41964808921947884283822317 15736803345730456606433369)
                ·
                  refine ⟨11802602509297842454825027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15736803345730456606433369 11802602509297842454825027)
                  ·
                    refine ⟨17703903763946763682237541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11802602509297842454825027 17703903763946763682237541)
                    ·
                      refine ⟨3319481955740018190419539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17703903763946763682237541 3319481955740018190419539)
                      ·
                        rfl

theorem cell23_6464668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_6464668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464668 prefixEnd_6464668 := by exact prefixLift 6464668
  have htrace : WordTrace (prefixWord ++ tailWord_6464668) baseStart_6464668 baseEnd_6464668 := by
    simpa [prefixWord, tailWord_6464668, baseEnd_6464668] using wordTrace_append hprefix tailTrace_6464668
  have hstable : (prefixWord ++ tailWord_6464668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464668).length < 2 ^ (prefixWord ++ tailWord_6464668).sum := by decide
  have hdescent : baseEnd_6464668 < baseStart_6464668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464691 : List Nat := [1, 1, 1, 2, 3, 2, 3, 4, 6]
def baseStart_6464691 : Nat := 118140960795 + 6464691 * 2 ^ 59
def prefixEnd_6464691 : Nat := 4983230072969 + 3 ^ 40 * 6464691 * 2
def baseEnd_6464691 : Nat := 368832640643896844492437

theorem tailTrace_6464691 : CollatzResearch.WordTrace tailWord_6464691 prefixEnd_6464691 368832640643896844492437 := by
  unfold tailWord_6464691
  simp only [CollatzResearch.WordTrace]
  refine ⟨235786651422536063167505927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157191100948357375445003951 235786651422536063167505927)
  ·
    refine ⟨353679977133804094751258891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235786651422536063167505927 353679977133804094751258891)
    ·
      refine ⟨530519965700706142126888337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353679977133804094751258891 530519965700706142126888337)
      ·
        refine ⟨397889974275529606595166253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530519965700706142126888337 397889974275529606595166253)
        ·
          refine ⟨149208740353323602473187345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397889974275529606595166253 149208740353323602473187345)
          ·
            refine ⟨111906555264992701854890509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149208740353323602473187345 111906555264992701854890509)
            ·
              refine ⟨41964958224372263195583941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111906555264992701854890509 41964958224372263195583941)
              ·
                refine ⟨7868429667069799349171989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41964958224372263195583941 7868429667069799349171989)
                ·
                  refine ⟨368832640643896844492437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7868429667069799349171989 368832640643896844492437)
                  ·
                    rfl

theorem cell23_6464691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 6].length) (baseStart_6464691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464691 prefixEnd_6464691 := by exact prefixLift 6464691
  have htrace : WordTrace (prefixWord ++ tailWord_6464691) baseStart_6464691 baseEnd_6464691 := by
    simpa [prefixWord, tailWord_6464691, baseEnd_6464691] using wordTrace_append hprefix tailTrace_6464691
  have hstable : (prefixWord ++ tailWord_6464691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464691).length < 2 ^ (prefixWord ++ tailWord_6464691).sum := by decide
  have hdescent : baseEnd_6464691 < baseStart_6464691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464695 : List Nat := [1, 1, 3, 1, 4, 1, 3, 4, 1, 4]
def baseStart_6464695 : Nat := 118140960795 + 6464695 * 2 ^ 59
def prefixEnd_6464695 : Nat := 4983230072969 + 3 ^ 40 * 6464695 * 2
def baseEnd_6464695 : Nat := 1106498606572563194927305

theorem tailTrace_6464695 : CollatzResearch.WordTrace tailWord_6464695 prefixEnd_6464695 1106498606572563194927305 := by
  unfold tailWord_6464695
  simp only [CollatzResearch.WordTrace]
  refine ⟨235786797314521571850651539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157191198209681047900434359 235786797314521571850651539)
  ·
    refine ⟨353680195971782357775977309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235786797314521571850651539 353680195971782357775977309)
    ·
      refine ⟨132630073489418384165991491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353680195971782357775977309 132630073489418384165991491)
      ·
        refine ⟨198945110234127576248987237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132630073489418384165991491 198945110234127576248987237)
        ·
          refine ⟨37302208168898920546685107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198945110234127576248987237 37302208168898920546685107)
          ·
            refine ⟨55953312253348380820027661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37302208168898920546685107 55953312253348380820027661)
            ·
              refine ⟨20982492095005642807510373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55953312253348380820027661 20982492095005642807510373)
              ·
                refine ⟨3934217267813558026408195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20982492095005642807510373 3934217267813558026408195)
                ·
                  refine ⟨5901325901720337039612293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3934217267813558026408195 5901325901720337039612293)
                  ·
                    refine ⟨1106498606572563194927305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5901325901720337039612293 1106498606572563194927305)
                    ·
                      rfl

theorem cell23_6464695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_6464695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464695 prefixEnd_6464695 := by exact prefixLift 6464695
  have htrace : WordTrace (prefixWord ++ tailWord_6464695) baseStart_6464695 baseEnd_6464695 := by
    simpa [prefixWord, tailWord_6464695, baseEnd_6464695] using wordTrace_append hprefix tailTrace_6464695
  have hstable : (prefixWord ++ tailWord_6464695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464695).length < 2 ^ (prefixWord ++ tailWord_6464695).sum := by decide
  have hdescent : baseEnd_6464695 < baseStart_6464695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464854 : List Nat := [5, 2, 3, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_6464854 : Nat := 118140960795 + 6464854 * 2 ^ 59
def prefixEnd_6464854 : Nat := 4983230072969 + 3 ^ 40 * 6464854 * 2
def baseEnd_6464854 : Nat := 3319577463141754462693685

theorem tailTrace_6464854 : CollatzResearch.WordTrace tailWord_6464854 prefixEnd_6464854 3319577463141754462693685 := by
  unfold tailWord_6464854
  simp only [CollatzResearch.WordTrace]
  refine ⟨14737037282559096375355601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157195064347297028003793077 14737037282559096375355601)
  ·
    refine ⟨11052777961919322281516701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14737037282559096375355601 11052777961919322281516701)
    ·
      refine ⟨4144791735719745855568763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11052777961919322281516701 4144791735719745855568763)
      ·
        refine ⟨6217187603579618783353145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4144791735719745855568763 6217187603579618783353145)
        ·
          refine ⟨4662890702684714087514859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6217187603579618783353145 4662890702684714087514859)
          ·
            refine ⟨6994336054027071131272289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4662890702684714087514859 6994336054027071131272289)
            ·
              refine ⟨5245752040520303348454217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6994336054027071131272289 5245752040520303348454217)
              ·
                refine ⟨3934314030390227511340663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5245752040520303348454217 3934314030390227511340663)
                ·
                  refine ⟨5901471045585341267010995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3934314030390227511340663 5901471045585341267010995)
                  ·
                    refine ⟨8852206568378011900516493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5901471045585341267010995 8852206568378011900516493)
                    ·
                      refine ⟨3319577463141754462693685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8852206568378011900516493 3319577463141754462693685)
                      ·
                        rfl

theorem cell23_6464854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_6464854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464854 prefixEnd_6464854 := by exact prefixLift 6464854
  have htrace : WordTrace (prefixWord ++ tailWord_6464854) baseStart_6464854 baseEnd_6464854 := by
    simpa [prefixWord, tailWord_6464854, baseEnd_6464854] using wordTrace_append hprefix tailTrace_6464854
  have hstable : (prefixWord ++ tailWord_6464854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464854).length < 2 ^ (prefixWord ++ tailWord_6464854).sum := by decide
  have hdescent : baseEnd_6464854 < baseStart_6464854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464882 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 1, 4, 2]
def baseStart_6464882 : Nat := 118140960795 + 6464882 * 2 ^ 59
def prefixEnd_6464882 : Nat := 4983230072969 + 3 ^ 40 * 6464882 * 2
def baseEnd_6464882 : Nat := 3319591840600080353143555

theorem tailTrace_6464882 : CollatzResearch.WordTrace tailWord_6464882 prefixEnd_6464882 3319591840600080353143555 := by
  unfold tailWord_6464882
  simp only [CollatzResearch.WordTrace]
  refine ⟨58948404441211025696927225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157195745176562735191805933 58948404441211025696927225)
  ·
    refine ⟨44211303330908269272695419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58948404441211025696927225 44211303330908269272695419)
    ·
      refine ⟨66316954996362403909043129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44211303330908269272695419 66316954996362403909043129)
      ·
        refine ⟨49737716247271802931782347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66316954996362403909043129 49737716247271802931782347)
        ·
          refine ⟨74606574370907704397673521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49737716247271802931782347 74606574370907704397673521)
          ·
            refine ⟨55954930778180778298255141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74606574370907704397673521 55954930778180778298255141)
            ·
              refine ⟨10491549520908895930922839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55954930778180778298255141 10491549520908895930922839)
              ·
                refine ⟨15737324281363343896384259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10491549520908895930922839 15737324281363343896384259)
                ·
                  refine ⟨23605986422045015844576389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15737324281363343896384259 23605986422045015844576389)
                  ·
                    refine ⟨4426122454133440470858073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23605986422045015844576389 4426122454133440470858073)
                    ·
                      refine ⟨3319591840600080353143555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4426122454133440470858073 3319591840600080353143555)
                      ·
                        rfl

theorem cell23_6464882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_6464882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464882 prefixEnd_6464882 := by exact prefixLift 6464882
  have htrace : WordTrace (prefixWord ++ tailWord_6464882) baseStart_6464882 baseEnd_6464882 := by
    simpa [prefixWord, tailWord_6464882, baseEnd_6464882] using wordTrace_append hprefix tailTrace_6464882
  have hstable : (prefixWord ++ tailWord_6464882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464882).length < 2 ^ (prefixWord ++ tailWord_6464882).sum := by decide
  have hdescent : baseEnd_6464882 < baseStart_6464882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464916 : List Nat := [2, 4, 2, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_6464916 : Nat := 118140960795 + 6464916 * 2 ^ 59
def prefixEnd_6464916 : Nat := 4983230072969 + 3 ^ 40 * 6464916 * 2
def baseEnd_6464916 : Nat := 3319609298942333220118399

theorem tailTrace_6464916 : CollatzResearch.WordTrace tailWord_6464916 prefixEnd_6464916 3319609298942333220118399 := by
  unfold tailWord_6464916
  simp only [CollatzResearch.WordTrace]
  refine ⟨117897428923360463297223301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157196571897813951062964401 117897428923360463297223301)
  ·
    refine ⟨22105767923130086868229369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117897428923360463297223301 22105767923130086868229369)
    ·
      refine ⟨16579325942347565151172027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22105767923130086868229369 16579325942347565151172027)
      ·
        refine ⟨24868988913521347726758041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16579325942347565151172027 24868988913521347726758041)
        ·
          refine ⟨18651741685141010795068531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24868988913521347726758041 18651741685141010795068531)
          ·
            refine ⟨27977612527711516192602797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18651741685141010795068531 27977612527711516192602797)
            ·
              refine ⟨10491604697891818572226049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27977612527711516192602797 10491604697891818572226049)
              ·
                refine ⟨7868703523418863929169537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10491604697891818572226049 7868703523418863929169537)
                ·
                  refine ⟨5901527642564147946877153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7868703523418863929169537 5901527642564147946877153)
                  ·
                    refine ⟨4426145731923110960157865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5901527642564147946877153 4426145731923110960157865)
                    ·
                      refine ⟨3319609298942333220118399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4426145731923110960157865 3319609298942333220118399)
                      ·
                        rfl

theorem cell23_6464916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_6464916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464916 prefixEnd_6464916 := by exact prefixLift 6464916
  have htrace : WordTrace (prefixWord ++ tailWord_6464916) baseStart_6464916 baseEnd_6464916 := by
    simpa [prefixWord, tailWord_6464916, baseEnd_6464916] using wordTrace_append hprefix tailTrace_6464916
  have hstable : (prefixWord ++ tailWord_6464916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464916).length < 2 ^ (prefixWord ++ tailWord_6464916).sum := by decide
  have hdescent : baseEnd_6464916 < baseStart_6464916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464928 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 7]
def baseStart_6464928 : Nat := 118140960795 + 6464928 * 2 ^ 59
def prefixEnd_6464928 : Nat := 4983230072969 + 3 ^ 40 * 6464928 * 2
def baseEnd_6464928 : Nat := 3319615460710187173168343

theorem tailTrace_6464928 : CollatzResearch.WordTrace tailWord_6464928 prefixEnd_6464928 3319615460710187173168343 := by
  unfold tailWord_6464928
  simp only [CollatzResearch.WordTrace]
  refine ⟨117897647761338726321941719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157196863681784968429255625 117897647761338726321941719)
  ·
    refine ⟨176846471642008089482912579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117897647761338726321941719 176846471642008089482912579)
    ·
      refine ⟨265269707463012134224368869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176846471642008089482912579 265269707463012134224368869)
      ·
        refine ⟨49738070149314775167069163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265269707463012134224368869 49738070149314775167069163)
        ·
          refine ⟨74607105223972162750603745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49738070149314775167069163 74607105223972162750603745)
          ·
            refine ⟨55955328917979122062952809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74607105223972162750603745 55955328917979122062952809)
            ·
              refine ⟨41966496688484341547214607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55955328917979122062952809 41966496688484341547214607)
              ·
                refine ⟨62949745032726512320821911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41966496688484341547214607 62949745032726512320821911)
                ·
                  refine ⟨94424617549089768481232867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62949745032726512320821911 94424617549089768481232867)
                  ·
                    refine ⟨141636926323634652721849301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94424617549089768481232867 141636926323634652721849301)
                    ·
                      refine ⟨3319615460710187173168343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141636926323634652721849301 3319615460710187173168343)
                      ·
                        rfl

theorem cell23_6464928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_6464928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464928 prefixEnd_6464928 := by exact prefixLift 6464928
  have htrace : WordTrace (prefixWord ++ tailWord_6464928) baseStart_6464928 baseEnd_6464928 := by
    simpa [prefixWord, tailWord_6464928, baseEnd_6464928] using wordTrace_append hprefix tailTrace_6464928
  have hstable : (prefixWord ++ tailWord_6464928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464928).length < 2 ^ (prefixWord ++ tailWord_6464928).sum := by decide
  have hdescent : baseEnd_6464928 < baseStart_6464928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464956 : List Nat := [2, 2, 2, 4, 3, 1, 1, 3, 5]
def baseStart_6464956 : Nat := 118140960795 + 6464956 * 2 ^ 59
def prefixEnd_6464956 : Nat := 4983230072969 + 3 ^ 40 * 6464956 * 2
def baseEnd_6464956 : Nat := 368847759796501451513135

theorem tailTrace_6464956 : CollatzResearch.WordTrace tailWord_6464956 prefixEnd_6464956 368847759796501451513135 := by
  unfold tailWord_6464956
  simp only [CollatzResearch.WordTrace]
  refine ⟨117898158383288006712951361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157197544511050675617268481 117898158383288006712951361)
  ·
    refine ⟨88423618787466005034713521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117898158383288006712951361 88423618787466005034713521)
    ·
      refine ⟨66317714090599503776035141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88423618787466005034713521 66317714090599503776035141)
      ·
        refine ⟨12434571391987406958006589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66317714090599503776035141 12434571391987406958006589)
        ·
          refine ⟨4662964271995277609252471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12434571391987406958006589 4662964271995277609252471)
          ·
            refine ⟨6994446407992916413878707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4662964271995277609252471 6994446407992916413878707)
            ·
              refine ⟨10491669611989374620818061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6994446407992916413878707 10491669611989374620818061)
              ·
                refine ⟨3934376104496015482806773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10491669611989374620818061 3934376104496015482806773)
                ·
                  refine ⟨368847759796501451513135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3934376104496015482806773 368847759796501451513135)
                  ·
                    rfl

theorem cell23_6464956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 5].length) (baseStart_6464956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464956 prefixEnd_6464956 := by exact prefixLift 6464956
  have htrace : WordTrace (prefixWord ++ tailWord_6464956) baseStart_6464956 baseEnd_6464956 := by
    simpa [prefixWord, tailWord_6464956, baseEnd_6464956] using wordTrace_append hprefix tailTrace_6464956
  have hstable : (prefixWord ++ tailWord_6464956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464956).length < 2 ^ (prefixWord ++ tailWord_6464956).sum := by decide
  have hdescent : baseEnd_6464956 < baseStart_6464956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464972 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 2, 1, 4]
def baseStart_6464972 : Nat := 118140960795 + 6464972 * 2 ^ 59
def prefixEnd_6464972 : Nat := 4983230072969 + 3 ^ 40 * 6464972 * 2
def baseEnd_6464972 : Nat := 3319638053858985001018141

theorem tailTrace_6464972 : CollatzResearch.WordTrace tailWord_6464972 prefixEnd_6464972 3319638053858985001018141 := by
  unfold tailWord_6464972
  simp only [CollatzResearch.WordTrace]
  refine ⟨117898450167259024079242585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157197933556345365438990113 117898450167259024079242585)
  ·
    refine ⟨88423837625444268059431939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117898450167259024079242585 88423837625444268059431939)
    ·
      refine ⟨132635756438166402089147909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88423837625444268059431939 132635756438166402089147909)
      ·
        refine ⟨24869204332156200391715233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132635756438166402089147909 24869204332156200391715233)
        ·
          refine ⟨18651903249117150293786425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24869204332156200391715233 18651903249117150293786425)
          ·
            refine ⟨13988927436837862720339819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18651903249117150293786425 13988927436837862720339819)
            ·
              refine ⟨20983391155256794080509729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13988927436837862720339819 20983391155256794080509729)
              ·
                refine ⟨15737543366442595560382297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20983391155256794080509729 15737543366442595560382297)
                ·
                  refine ⟨11803157524831946670286723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15737543366442595560382297 11803157524831946670286723)
                  ·
                    refine ⟨17704736287247920005430085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11803157524831946670286723 17704736287247920005430085)
                    ·
                      refine ⟨3319638053858985001018141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17704736287247920005430085 3319638053858985001018141)
                      ·
                        rfl

theorem cell23_6464972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_6464972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464972 prefixEnd_6464972 := by exact prefixLift 6464972
  have htrace : WordTrace (prefixWord ++ tailWord_6464972) baseStart_6464972 baseEnd_6464972 := by
    simpa [prefixWord, tailWord_6464972, baseEnd_6464972] using wordTrace_append hprefix tailTrace_6464972
  have hstable : (prefixWord ++ tailWord_6464972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464972).length < 2 ^ (prefixWord ++ tailWord_6464972).sum := by decide
  have hdescent : baseEnd_6464972 < baseStart_6464972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6464975 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 3]
def baseStart_6464975 : Nat := 118140960795 + 6464975 * 2 ^ 59
def prefixEnd_6464975 : Nat := 4983230072969 + 3 ^ 40 * 6464975 * 2
def baseEnd_6464975 : Nat := 3319639594300948489280627

theorem tailTrace_6464975 : CollatzResearch.WordTrace tailWord_6464975 prefixEnd_6464975 3319639594300948489280627 := by
  unfold tailWord_6464975
  simp only [CollatzResearch.WordTrace]
  refine ⟨235797009753507179670844379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157198006502338119780562919 235797009753507179670844379)
  ·
    refine ⟨353695514630260769506266569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235797009753507179670844379 353695514630260769506266569)
    ·
      refine ⟨265271635972695577129699927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353695514630260769506266569 265271635972695577129699927)
      ·
        refine ⟨397907453959043365694549891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265271635972695577129699927 397907453959043365694549891)
        ·
          refine ⟨596861180938565048541824837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397907453959043365694549891 596861180938565048541824837)
          ·
            refine ⟨111911471425980946601592157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 596861180938565048541824837 111911471425980946601592157)
            ·
              refine ⟨41966801784742854975597059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111911471425980946601592157 41966801784742854975597059)
              ·
                refine ⟨62950202677114282463395589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41966801784742854975597059 62950202677114282463395589)
                ·
                  refine ⟨11803163001958927961886673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62950202677114282463395589 11803163001958927961886673)
                  ·
                    refine ⟨8852372251469195971415005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11803163001958927961886673 8852372251469195971415005)
                    ·
                      refine ⟨3319639594300948489280627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8852372251469195971415005 3319639594300948489280627)
                      ·
                        rfl

theorem cell23_6464975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 3].length) (baseStart_6464975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6464975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6464975 prefixEnd_6464975 := by exact prefixLift 6464975
  have htrace : WordTrace (prefixWord ++ tailWord_6464975) baseStart_6464975 baseEnd_6464975 := by
    simpa [prefixWord, tailWord_6464975, baseEnd_6464975] using wordTrace_append hprefix tailTrace_6464975
  have hstable : (prefixWord ++ tailWord_6464975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6464975).length < 2 ^ (prefixWord ++ tailWord_6464975).sum := by decide
  have hdescent : baseEnd_6464975 < baseStart_6464975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6464975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465055 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 1, 6]
def baseStart_6465055 : Nat := 118140960795 + 6465055 * 2 ^ 59
def prefixEnd_6465055 : Nat := 4983230072969 + 3 ^ 40 * 6465055 * 2
def baseEnd_6465055 : Nat := 1106560224251102725426753

theorem tailTrace_6465055 : CollatzResearch.WordTrace tailWord_6465055 prefixEnd_6465055 1106560224251102725426753 := by
  unfold tailWord_6465055
  simp only [CollatzResearch.WordTrace]
  refine ⟨235799927593217353333756619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157199951728811568889171079 235799927593217353333756619)
  ·
    refine ⟨353699891389826030000634929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235799927593217353333756619 353699891389826030000634929)
    ·
      refine ⟨265274918542369522500476197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353699891389826030000634929 265274918542369522500476197)
      ·
        refine ⟨49739047226694285468839287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265274918542369522500476197 49739047226694285468839287)
        ·
          refine ⟨74608570840041428203258931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49739047226694285468839287 74608570840041428203258931)
          ·
            refine ⟨111912856260062142304888397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74608570840041428203258931 111912856260062142304888397)
            ·
              refine ⟨41967321097523303364333149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111912856260062142304888397 41967321097523303364333149)
              ·
                refine ⟨15737745411571238761624931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41967321097523303364333149 15737745411571238761624931)
                ·
                  refine ⟨23606618117356858142437397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15737745411571238761624931 23606618117356858142437397)
                  ·
                    refine ⟨1106560224251102725426753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23606618117356858142437397 1106560224251102725426753)
                    ·
                      rfl

theorem cell23_6465055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 6].length) (baseStart_6465055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465055 prefixEnd_6465055 := by exact prefixLift 6465055
  have htrace : WordTrace (prefixWord ++ tailWord_6465055) baseStart_6465055 baseEnd_6465055 := by
    simpa [prefixWord, tailWord_6465055, baseEnd_6465055] using wordTrace_append hprefix tailTrace_6465055
  have hstable : (prefixWord ++ tailWord_6465055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465055).length < 2 ^ (prefixWord ++ tailWord_6465055).sum := by decide
  have hdescent : baseEnd_6465055 < baseStart_6465055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465079 : List Nat := [1, 1, 3, 1, 2, 4, 4, 1, 1, 1, 4]
def baseStart_6465079 : Nat := 118140960795 + 6465079 * 2 ^ 59
def prefixEnd_6465079 : Nat := 4983230072969 + 3 ^ 40 * 6465079 * 2
def baseEnd_6465079 : Nat := 3319692996289016082380149

theorem tailTrace_6465079 : CollatzResearch.WordTrace tailWord_6465079 prefixEnd_6465079 3319692996289016082380149 := by
  unfold tailWord_6465079
  simp only [CollatzResearch.WordTrace]
  refine ⟨235800802945130405432630291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157200535296753603621753527 235800802945130405432630291)
  ·
    refine ⟨353701204417695608148945437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235800802945130405432630291 353701204417695608148945437)
    ·
      refine ⟨132637951656635853055854539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353701204417695608148945437 132637951656635853055854539)
      ·
        refine ⟨198956927484953779583781809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132637951656635853055854539 198956927484953779583781809)
        ·
          refine ⟨149217695613715334687836357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198956927484953779583781809 149217695613715334687836357)
          ·
            refine ⟨27978317927571625253969317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149217695613715334687836357 27978317927571625253969317)
            ·
              refine ⟨5245934611419679735119247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27978317927571625253969317 5245934611419679735119247)
              ·
                refine ⟨7868901917129519602678871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5245934611419679735119247 7868901917129519602678871)
                ·
                  refine ⟨11803352875694279404018307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7868901917129519602678871 11803352875694279404018307)
                  ·
                    refine ⟨17705029313541419106027461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11803352875694279404018307 17705029313541419106027461)
                    ·
                      refine ⟨3319692996289016082380149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17705029313541419106027461 3319692996289016082380149)
                      ·
                        rfl

theorem cell23_6465079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 1, 1, 4].length) (baseStart_6465079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465079 prefixEnd_6465079 := by exact prefixLift 6465079
  have htrace : WordTrace (prefixWord ++ tailWord_6465079) baseStart_6465079 baseEnd_6465079 := by
    simpa [prefixWord, tailWord_6465079, baseEnd_6465079] using wordTrace_append hprefix tailTrace_6465079
  have hstable : (prefixWord ++ tailWord_6465079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465079).length < 2 ^ (prefixWord ++ tailWord_6465079).sum := by decide
  have hdescent : baseEnd_6465079 < baseStart_6465079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465106 : List Nat := [3, 2, 2, 1, 2, 3, 3, 1, 2, 4]
def baseStart_6465106 : Nat := 118140960795 + 6465106 * 2 ^ 59
def prefixEnd_6465106 : Nat := 4983230072969 + 3 ^ 40 * 6465106 * 2
def baseEnd_6465106 : Nat := 1106568953422229158914175

theorem tailTrace_6465106 : CollatzResearch.WordTrace tailWord_6465106 prefixEnd_6465106 1106568953422229158914175 := by
  unfold tailWord_6465106
  simp only [CollatzResearch.WordTrace]
  refine ⟨58950446929008147260965793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157201191810688392695908781 58950446929008147260965793)
  ·
    refine ⟨44212835196756110445724345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58950446929008147260965793 44212835196756110445724345)
    ·
      refine ⟨33159626397567082834293259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44212835196756110445724345 33159626397567082834293259)
      ·
        refine ⟨49739439596350624251439889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33159626397567082834293259 49739439596350624251439889)
        ·
          refine ⟨37304579697262968188579917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49739439596350624251439889 37304579697262968188579917)
          ·
            refine ⟨13989217386473613070717469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37304579697262968188579917 13989217386473613070717469)
            ·
              refine ⟨5245956519927604901519051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13989217386473613070717469 5245956519927604901519051)
              ·
                refine ⟨7868934779891407352278577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5245956519927604901519051 7868934779891407352278577)
                ·
                  refine ⟨5901701084918555514208933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7868934779891407352278577 5901701084918555514208933)
                  ·
                    refine ⟨1106568953422229158914175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5901701084918555514208933 1106568953422229158914175)
                    ·
                      rfl

theorem cell23_6465106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_6465106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465106 prefixEnd_6465106 := by exact prefixLift 6465106
  have htrace : WordTrace (prefixWord ++ tailWord_6465106) baseStart_6465106 baseEnd_6465106 := by
    simpa [prefixWord, tailWord_6465106, baseEnd_6465106] using wordTrace_append hprefix tailTrace_6465106
  have hstable : (prefixWord ++ tailWord_6465106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465106).length < 2 ^ (prefixWord ++ tailWord_6465106).sum := by decide
  have hdescent : baseEnd_6465106 < baseStart_6465106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465116 : List Nat := [2, 2, 4, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_6465116 : Nat := 118140960795 + 6465116 * 2 ^ 59
def prefixEnd_6465116 : Nat := 4983230072969 + 3 ^ 40 * 6465116 * 2
def baseEnd_6465116 : Nat := 3319711995073232437617479

theorem tailTrace_6465116 : CollatzResearch.WordTrace tailWord_6465116 prefixEnd_6465116 3319711995073232437617479 := by
  unfold tailWord_6465116
  simp only [CollatzResearch.WordTrace]
  refine ⟨117901076222998180375863601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157201434963997573834484801 117901076222998180375863601)
  ·
    refine ⟨88425807167248635281897701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117901076222998180375863601 88425807167248635281897701)
    ·
      refine ⟨16579838843859119115355819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88425807167248635281897701 16579838843859119115355819)
      ·
        refine ⟨24869758265788678673033729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16579838843859119115355819 24869758265788678673033729)
        ·
          refine ⟨18652318699341509004775297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24869758265788678673033729 18652318699341509004775297)
          ·
            refine ⟨13989239024506131753581473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18652318699341509004775297 13989239024506131753581473)
            ·
              refine ⟨10491929268379598815186105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13989239024506131753581473 10491929268379598815186105)
              ·
                refine ⟨7868946951284699111389579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10491929268379598815186105 7868946951284699111389579)
                ·
                  refine ⟨11803420426927048667084369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7868946951284699111389579 11803420426927048667084369)
                  ·
                    refine ⟨8852565320195286500313277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11803420426927048667084369 8852565320195286500313277)
                    ·
                      refine ⟨3319711995073232437617479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8852565320195286500313277 3319711995073232437617479)
                      ·
                        rfl

theorem cell23_6465116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_6465116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465116 prefixEnd_6465116 := by exact prefixLift 6465116
  have htrace : WordTrace (prefixWord ++ tailWord_6465116) baseStart_6465116 baseEnd_6465116 := by
    simpa [prefixWord, tailWord_6465116, baseEnd_6465116] using wordTrace_append hprefix tailTrace_6465116
  have hstable : (prefixWord ++ tailWord_6465116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465116).length < 2 ^ (prefixWord ++ tailWord_6465116).sum := by decide
  have hdescent : baseEnd_6465116 < baseStart_6465116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465130 : List Nat := [3, 1, 3, 2, 1, 4, 1, 3, 1, 2, 2]
def baseStart_6465130 : Nat := 118140960795 + 6465130 * 2 ^ 59
def prefixEnd_6465130 : Nat := 4983230072969 + 3 ^ 40 * 6465130 * 2
def baseEnd_6465130 : Nat := 3319719183802395382842415

theorem tailTrace_6465130 : CollatzResearch.WordTrace tailWord_6465130 prefixEnd_6465130 3319719183802395382842415 := by
  unfold tailWord_6465130
  simp only [CollatzResearch.WordTrace]
  refine ⟨58950665766986410285684211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157201775378630427428491229 58950665766986410285684211)
  ·
    refine ⟨88425998650479615428526317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58950665766986410285684211 88425998650479615428526317)
    ·
      refine ⟨33159749493929855785697369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88425998650479615428526317 33159749493929855785697369)
      ·
        refine ⟨24869812120447391839273027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33159749493929855785697369 24869812120447391839273027)
        ·
          refine ⟨37304718180671087758909541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24869812120447391839273027 37304718180671087758909541)
          ·
            refine ⟨6994634658875828954795539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37304718180671087758909541 6994634658875828954795539)
            ·
              refine ⟨10491951988313743432193309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6994634658875828954795539 10491951988313743432193309)
              ·
                refine ⟨3934481995617653787072491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10491951988313743432193309 3934481995617653787072491)
                ·
                  refine ⟨5901722993426480680608737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3934481995617653787072491 5901722993426480680608737)
                  ·
                    refine ⟨4426292245069860510456553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5901722993426480680608737 4426292245069860510456553)
                    ·
                      refine ⟨3319719183802395382842415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4426292245069860510456553 3319719183802395382842415)
                      ·
                        rfl

theorem cell23_6465130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_6465130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465130 prefixEnd_6465130 := by exact prefixLift 6465130
  have htrace : WordTrace (prefixWord ++ tailWord_6465130) baseStart_6465130 baseEnd_6465130 := by
    simpa [prefixWord, tailWord_6465130, baseEnd_6465130] using wordTrace_append hprefix tailTrace_6465130
  have hstable : (prefixWord ++ tailWord_6465130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465130).length < 2 ^ (prefixWord ++ tailWord_6465130).sum := by decide
  have hdescent : baseEnd_6465130 < baseStart_6465130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465135 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 4]
def baseStart_6465135 : Nat := 118140960795 + 6465135 * 2 ^ 59
def prefixEnd_6465135 : Nat := 4983230072969 + 3 ^ 40 * 6465135 * 2
def baseEnd_6465135 : Nat := 3319721751205667863279891

theorem tailTrace_6465135 : CollatzResearch.WordTrace tailWord_6465135 prefixEnd_6465135 3319721751205667863279891 := by
  unfold tailWord_6465135
  simp only [CollatzResearch.WordTrace]
  refine ⟨235802845432927526996668859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157201896955285017997779239 235802845432927526996668859)
  ·
    refine ⟨353704268149391290495003289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235802845432927526996668859 353704268149391290495003289)
    ·
      refine ⟨265278201112043467871252467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353704268149391290495003289 265278201112043467871252467)
      ·
        refine ⟨397917301668065201806878701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265278201112043467871252467 397917301668065201806878701)
        ·
          refine ⟨149218988125524450677579513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397917301668065201806878701 149218988125524450677579513)
          ·
            refine ⟨111914241094143338008184635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149218988125524450677579513 111914241094143338008184635)
            ·
              refine ⟨167871361641215007012276953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111914241094143338008184635 167871361641215007012276953)
              ·
                refine ⟨125903521230911255259207715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167871361641215007012276953 125903521230911255259207715)
                ·
                  refine ⟨188855281846366882888811573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125903521230911255259207715 188855281846366882888811573)
                  ·
                    refine ⟨17705182673096895270826085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 188855281846366882888811573 17705182673096895270826085)
                    ·
                      refine ⟨3319721751205667863279891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17705182673096895270826085 3319721751205667863279891)
                      ·
                        rfl

theorem cell23_6465135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_6465135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465135 prefixEnd_6465135 := by exact prefixLift 6465135
  have htrace : WordTrace (prefixWord ++ tailWord_6465135) baseStart_6465135 baseEnd_6465135 := by
    simpa [prefixWord, tailWord_6465135, baseEnd_6465135] using wordTrace_append hprefix tailTrace_6465135
  have hstable : (prefixWord ++ tailWord_6465135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465135).length < 2 ^ (prefixWord ++ tailWord_6465135).sum := by decide
  have hdescent : baseEnd_6465135 < baseStart_6465135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465155 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 5]
def baseStart_6465155 : Nat := 118140960795 + 6465155 * 2 ^ 59
def prefixEnd_6465155 : Nat := 4983230072969 + 3 ^ 40 * 6465155 * 2
def baseEnd_6465155 : Nat := 3319732020818757785029799

theorem tailTrace_6465155 : CollatzResearch.WordTrace tailWord_6465155 prefixEnd_6465155 3319732020818757785029799 := by
  unfold tailWord_6465155
  simp only [CollatzResearch.WordTrace]
  refine ⟨235803574892855070412396919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157202383261903380274931279 235803574892855070412396919)
  ·
    refine ⟨353705362339282605618595379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235803574892855070412396919 353705362339282605618595379)
    ·
      refine ⟨530558043508923908427893069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353705362339282605618595379 530558043508923908427893069)
      ·
        refine ⟨198959266315846465660459901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 530558043508923908427893069 198959266315846465660459901)
        ·
          refine ⟨74609724868442424622672463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198959266315846465660459901 74609724868442424622672463)
          ·
            refine ⟨111914587302663636934008695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74609724868442424622672463 111914587302663636934008695)
            ·
              refine ⟨167871880953995455401013043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111914587302663636934008695 167871880953995455401013043)
              ·
                refine ⟨251807821430993183101519565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167871880953995455401013043 251807821430993183101519565)
                ·
                  refine ⟨94427933036622443663069837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251807821430993183101519565 94427933036622443663069837)
                  ·
                    refine ⟨35410474888733416373651189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94427933036622443663069837 35410474888733416373651189)
                    ·
                      refine ⟨3319732020818757785029799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35410474888733416373651189 3319732020818757785029799)
                      ·
                        rfl

theorem cell23_6465155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_6465155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465155 prefixEnd_6465155 := by exact prefixLift 6465155
  have htrace : WordTrace (prefixWord ++ tailWord_6465155) baseStart_6465155 baseEnd_6465155 := by
    simpa [prefixWord, tailWord_6465155, baseEnd_6465155] using wordTrace_append hprefix tailTrace_6465155
  have hstable : (prefixWord ++ tailWord_6465155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465155).length < 2 ^ (prefixWord ++ tailWord_6465155).sum := by decide
  have hdescent : baseEnd_6465155 < baseStart_6465155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465169 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 6, 2, 2]
def baseStart_6465169 : Nat := 118140960795 + 6465169 * 2 ^ 59
def prefixEnd_6465169 : Nat := 4983230072969 + 3 ^ 40 * 6465169 * 2
def baseEnd_6465169 : Nat := 3319739209547920730254735

theorem tailTrace_6465169 : CollatzResearch.WordTrace tailWord_6465169 prefixEnd_6465169 3319739209547920730254735 := by
  unfold tailWord_6465169
  simp only [CollatzResearch.WordTrace]
  refine ⟨235804085514804350803406561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157202723676536233868937707 235804085514804350803406561)
  ·
    refine ⟨176853064136103263102554921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235804085514804350803406561 176853064136103263102554921)
    ·
      refine ⟨132639798102077447326916191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176853064136103263102554921 132639798102077447326916191)
      ·
        refine ⟨198959697153116170990374287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132639798102077447326916191 198959697153116170990374287)
        ·
          refine ⟨298439545729674256485561431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198959697153116170990374287 298439545729674256485561431)
          ·
            refine ⟨447659318594511384728342147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298439545729674256485561431 447659318594511384728342147)
            ·
              refine ⟨671488977891767077092513221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447659318594511384728342147 671488977891767077092513221)
              ·
                refine ⟨125904183354706326954846229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 671488977891767077092513221 125904183354706326954846229)
                ·
                  refine ⟨5901758594751859076008417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125904183354706326954846229 5901758594751859076008417)
                  ·
                    refine ⟨4426318946063894307006313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5901758594751859076008417 4426318946063894307006313)
                    ·
                      refine ⟨3319739209547920730254735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4426318946063894307006313 3319739209547920730254735)
                      ·
                        rfl

theorem cell23_6465169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 2, 2].length) (baseStart_6465169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465169 prefixEnd_6465169 := by exact prefixLift 6465169
  have htrace : WordTrace (prefixWord ++ tailWord_6465169) baseStart_6465169 baseEnd_6465169 := by
    simpa [prefixWord, tailWord_6465169, baseEnd_6465169] using wordTrace_append hprefix tailTrace_6465169
  have hstable : (prefixWord ++ tailWord_6465169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465169).length < 2 ^ (prefixWord ++ tailWord_6465169).sum := by decide
  have hdescent : baseEnd_6465169 < baseStart_6465169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
